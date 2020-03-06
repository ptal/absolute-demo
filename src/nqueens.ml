(* Copyright 2020 Pierre Talbot

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details. *)

open Core.Types
open Bounds
open Lang.Ast
open Lang.Rewritting
open Typing.Tast
open Box
open Vardom
open Event_loop
open Direct_product
open Propagator_completion
open Domains.Interpretation

(* I. Create the model.
    Credits go to https://github.com/MiniZinc/minizinc-benchmarks/blob/master/queens/queens.mzn. *)

let noattack vars i j =
  let qi, qj = List.nth vars i, List.nth vars j in
  let ci = Cst(Bound_rat.of_int i, Int) in
  let cj = Cst(Bound_rat.of_int j, Int) in
  [Cmp(Var qi, NEQ, Var qj);
   Cmp(Binary(Var qi, ADD, ci), NEQ, Binary(Var qj, ADD, cj));
   Cmp(Binary(Var qi, SUB, ci), NEQ, Binary(Var qj, SUB, cj))]

let rec noattack_i vars i j =
  if j >= List.length vars then []
  else (noattack vars i j)@(noattack_i vars i (j+1))

let noattack_all vars =
  let rec aux i =
    if i >= List.length vars then []
    else (noattack_i vars i (i+1))@(aux (i+1)) in
  aux 0

(** [var_in_dom l u x] ensures that `x >= l` and `x <= u`. *)
let var_in_dom l u x =
  [Cmp(Var x, GEQ, Cst(Bound_rat.of_int l, Int));
   Cmp(Var x, LEQ, Cst(Bound_rat.of_int u, Int))]

(** [vars_in_dom l u vars] ensures that all variables in `vars` are in the interval [l..u]. *)
let rec vars_in_dom l u = function
  | [] -> []
  | x::vars -> (var_in_dom l u x)@(vars_in_dom l u vars)

(** [make_vars n] creates `n` variables named `x1`,...,`xn`. *)
let rec make_vars = function
  | 0 -> []
  | n -> ("x" ^ (string_of_int n))::(make_vars (n-1))

(** Model the N-Queens problem. *)
let make_nqueens n =
  let vars = List.rev (make_vars n) in
  let domains = List.rev (vars_in_dom 1 n vars) in
  let constraints = List.rev (noattack_all vars) in
  let rec make_formula = function
    | [] -> QFFormula (conjunction (domains@constraints))
    | x::vars -> Exists(x, Concrete Int, make_formula vars) in
  make_formula vars

(** II. Create the abstract domain. *)

module Box = Box.Make(Bound_int)(Itv.Itv)(Box_split.First_fail_LB)
module PC = Propagator_completion(Box.Vardom)(Box)
module E = Event_loop(Event_atom(PC))
module A = Direct_product(
  Prod_cons(Box)(
  Prod_cons(PC)(
  Prod_atom(E))))

let box_uid = 1
let pc_uid = 2
let event_uid = 3

let init () : A.t =
  let box = ref (Box.empty box_uid) in
  let pc = ref (PC.init PC.I.{uid=pc_uid; a=box}) in
  let event = ref (E.init event_uid pc) in
  A.init 0 (Owned box, (Owned pc, Owned event))

(** III. Type the formula into the abstract domains. *)

(** Given a formula, we assign each of its variables and constraints to an abstract domain.
   For the abstract domain `A`, all the variables and interval constraint go into `Box`, and the rest go into `PC`. *)
let type_formula formula =
  let rec aux' = function
    (* Domain constraint go into `Box`. *)
    | Cmp (Var x, LEQ, Cst (i,ty)) -> box_uid, TCmp(Var x, LEQ, Cst (i,ty))
    | Cmp (Var x, GEQ, Cst (i,ty)) -> box_uid, TCmp(Var x, GEQ, Cst (i,ty))
    (* Other constraint go into `PC`. *)
    | Cmp c -> pc_uid, TCmp c
    | And (f1,f2) -> pc_uid, TAnd(aux' f1, aux' f2)
    (* All other constraint are not supported in this abstract domain. *)
    | _ -> raise (Wrong_modelling "Constraint not supported by the current abstract domain.") in
  let rec aux = function
    | Exists(name, ty, qf) -> TExists({name; ty; uid=box_uid}, aux qf)
    | QFFormula f -> TQFFormula (aux' f) in
  aux formula

(** IV. Solve the typed formula. *)

module Solver = Fixpoint.Solver.Make(A)
module T = Solver.T

let print_tformula a tf =
  let adty = match A.type_of a with
    | Some adty -> adty
    | None -> raise (Wrong_modelling "The given abstract domain does not have a type.") in
  Printf.printf "N-Queens model:\n\n%s\n" (string_of_tqformula adty tf)

let print_solution n gs =
  Printf.printf "Found the solution after exploring %d nodes.\n" T.(gs.stats.nodes);
  let vars = List.rev (make_vars n) in
  let rec print_vars = function
    | [] -> ()
    | x::vars ->
      begin
        let vid, _ = A.I.to_abstract_var (A.interpretation gs.domain) x in
        Format.printf "%s=%a, " x Bound_rat.pp_print (fst (A.project gs.domain vid));
        print_vars vars
      end in
  print_vars vars

let _ =
  let nqueens = 8 in
  try
    (* (1) Merge the three previous steps. *)
    let qformula = make_nqueens nqueens in
    let a = init () in
    let tf = type_formula qformula in
    (* (1b) Print the typed formula (optional). *)
    print_tformula a tf;
    (* (2) Interpret the typed formula into the abstract element. *)
    let a, cs = A.interpret a Exact tf in
    (* (3) Add the interpreted constraints into the abstract element. *)
    let a = List.fold_left A.weak_incremental_closure a cs in
    (* (4) Create the solver. *)
    let bound_sol = T.BoundSolutions 1 in
    let transformer = T.init a [bound_sol] in
    (* (5) Run the solver. *)
    let (gs,_) =
      try Solver.solve transformer
      with Solver.T.StopSearch t -> t in
    if T.(gs.stats.sols) > 0 then
      print_solution nqueens gs
    else
      Printf.printf "No solution found."
  with e ->
    Printf.printf "Exception: %s\n" (Printexc.to_string e)
