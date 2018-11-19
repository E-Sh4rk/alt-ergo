(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format
open Parsed

[@@@ocaml.warning "-33"]
open Options

(** Anotations (used by the GUI). *)

type ('a, 'b) annoted =
  { c : 'a;
    annot : 'b }

let new_id = let r = ref 0 in fun () -> r := !r+1; !r

let mk ?(annot=new_id ()) c = { c; annot; }


(** Terms and Formulas *)

type tconstant =
  | Tint of string
  | Treal of Num.num
  | Tbitv of string
  | Ttrue
  | Tfalse
  | Tvoid

type oplogic =
    OPand | OPor | OPxor | OPimp | OPnot | OPiff
  | OPif

type 'a tterm =
  { tt_ty : Ty.t; tt_desc : 'a tt_desc }

and 'a atterm = ('a tterm, 'a) annoted

and 'a tt_desc =
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of ('a tterm, 'a) annoted * Symbols.t * ('a tterm, 'a) annoted
  | TTprefix of Symbols.t * ('a tterm, 'a) annoted
  | TTapp of Symbols.t * ('a tterm, 'a) annoted list
  | TTmapsTo of Hstring.t * ('a tterm, 'a) annoted
  | TTinInterval of
      ('a tterm, 'a) annoted * bool * ('a tterm, 'a) annoted *
      ('a tterm, 'a) annoted *  bool
  (* bool = true <-> interval is_open *)

  | TTget of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTset of
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTextract of
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTconcat of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTdot of ('a tterm, 'a) annoted * Hstring.t
  | TTrecord of (Hstring.t * ('a tterm, 'a) annoted) list
  | TTlet of (Symbols.t * ('a tterm, 'a) annoted) list * ('a tterm, 'a) annoted
  | TTnamed of Hstring.t * ('a tterm, 'a) annoted
  | TTite of ('a tform, 'a) annoted *
             ('a tterm, 'a) annoted * ('a tterm, 'a) annoted

and 'a atatom = ('a tatom, 'a) annoted

and 'a tatom =
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted * bool (* true <-> negated *)

and 'a quant_form = {
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : (('a tterm, 'a) annoted list * bool) list ;
  qf_hyp : ('a tform, 'a) annoted list;
  qf_form : ('a tform, 'a) annoted
}

and 'a atform = ('a tform, 'a) annoted

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted

and 'a tlet_kind =
  | TletTerm of ('a tterm, 'a) annoted
  | TletForm of ('a tform, 'a) annoted



(** Declarations *)

type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

type goal_sort = Cut | Check | Thm

type theories_extensions =
  | Sum
  | Arrays
  | Records
  | Bitv
  | LIA
  | LRA
  | NRA
  | NIA
  | FPA

type 'a atdecl = ('a tdecl, 'a) annoted

and 'a tdecl =
  (* to simplify impl and extension of GUI, a TTtheory is seen a list
     of tdecl, although we only allow axioms in theories
     declarations *)
  | TTheory of
      Loc.t * string * theories_extensions * ('a tdecl, 'a) annoted list
  | TAxiom of Loc.t * string * axiom_kind * ('a tform, 'a) annoted
  | TRewriting of Loc.t * string * (('a tterm, 'a) annoted rwt_rule) list
  | TGoal of Loc.t * goal_sort * string * ('a tform, 'a) annoted
  | TLogic of Loc.t * string list * plogic_type
  | TPredicate_def of
      Loc.t * string *
      (string * ppure_type) list * ('a tform, 'a) annoted
  | TFunction_def of
      Loc.t * string *
      (string * ppure_type) list * ppure_type * ('a tform, 'a) annoted
  | TTypeDecl of Loc.t * string list * string * body_type_decl

(*****)

let string_of_op = function
  | OPand -> "and"
  | OPor -> "or"
  | OPimp -> "->"
  | OPiff -> "<->"
  | _ -> assert false

let print_binder fmt (s, t) =
  fprintf fmt "%a :%a" Symbols.print s Ty.print t

let print_binders fmt l =
  List.iter (fun c -> fprintf fmt "%a, " print_binder c) l

let rec print_term fmt t = match t.c.tt_desc with
  | TTconst Ttrue ->
    fprintf fmt "true"
  | TTconst Tfalse ->
    fprintf fmt "false"
  | TTconst Tvoid ->
    fprintf fmt "void"
  | TTconst (Tint n) ->
    fprintf fmt "%s" n
  | TTconst (Treal n) ->
    fprintf fmt "%s" (Num.string_of_num n)
  | TTconst Tbitv s ->
    fprintf fmt "%s" s
  | TTvar s ->
    fprintf fmt "%a" Symbols.print s
  | TTapp(s,l) ->
    fprintf fmt "%a(%a)" Symbols.print s print_term_list l
  | TTinfix(t1,s,t2) ->
    fprintf fmt "%a %a %a" print_term t1 Symbols.print s print_term t2
  | TTprefix (s, t') ->
    fprintf fmt "%a %a" Symbols.print s print_term t'
  | TTget (t1, t2) ->
    fprintf fmt "%a[%a]" print_term t1 print_term t2
  | TTset (t1, t2, t3) ->
    fprintf fmt "%a[%a<-%a]" print_term t1 print_term t2 print_term t3
  | TTextract (t1, t2, t3) ->
    fprintf fmt "%a^{%a,%a}" print_term t1 print_term t2 print_term t3
  | TTconcat (t1, t2) ->
    fprintf fmt "%a @ %a" print_term t1 print_term t2
  | TTdot (t1, s) ->
    fprintf fmt "%a.%s" print_term t1 (Hstring.view s)
  | TTrecord l ->
    fprintf fmt "{ ";
    List.iter
      (fun (s, t) -> fprintf fmt "%s = %a" (Hstring.view s) print_term t) l;
    fprintf fmt " }"
  | TTlet (binders, t2) ->
    fprintf fmt "let %a in %a" print_term_binders binders print_term t2
  | TTnamed (lbl, t) ->
    fprintf fmt "%a" print_term t

  | TTinInterval(e, lb, i, j, ub) ->
    fprintf fmt "%a in %s%a, %a%s"
      print_term e
      (if lb then "]" else "[")
      print_term i
      print_term j
      (if ub then "[" else "]")

  | TTmapsTo(x,e) ->
    fprintf fmt "%s |-> %a" (Hstring.view x) print_term e

  | TTite(cond, t1, t2) ->
    fprintf fmt "(if %a then %a else %a)"
      print_formula cond print_term t1 print_term t2

and print_term_binders fmt l =
  match l with
  | [] -> assert false
  | (sy, t) :: l ->
    fprintf fmt "%a = %a" Symbols.print sy print_term t;
    List.iter (fun (sy, t) ->
        fprintf fmt ", %a = %a" Symbols.print sy print_term t) l

and print_term_list fmt = List.iter (fprintf fmt "%a," print_term)

and print_atom fmt a =
  match a.c with
  | TAtrue ->
    fprintf fmt "True"
  | TAfalse ->
    fprintf fmt "True"
  | TAeq [t1; t2] ->
    fprintf fmt "%a = %a" print_term t1 print_term t2
  | TAneq [t1; t2] ->
    fprintf fmt "%a <> %a" print_term t1 print_term t2
  | TAle [t1; t2] ->
    fprintf fmt "%a <= %a" print_term t1 print_term t2
  | TAlt [t1; t2] ->
    fprintf fmt "%a < %a" print_term t1 print_term t2
  | TApred (t, negated) ->
    if negated then fprintf fmt "(not (%a))" print_term t
    else print_term fmt t
  | _ -> assert false

and print_triggers fmt l =
  List.iter (fun (tr, _) -> fprintf fmt "%a | " print_term_list tr) l

and print_formula fmt f =
  match f.c with
  | TFatom a ->
    print_atom fmt a
  | TFop(OPnot, [f]) ->
    fprintf fmt "not %a" print_formula f
  | TFop(OPif, [cond; f1;f2]) ->
    fprintf fmt "if %a then %a else %a"
      print_formula cond print_formula f1 print_formula f2
  | TFop(op, [f1; f2]) ->
    fprintf fmt "%a %s %a" print_formula f1 (string_of_op op) print_formula f2
  | TFforall {qf_bvars = l; qf_triggers = t; qf_form = f} ->
    fprintf fmt "forall %a [%a]. %a"
      print_binders l print_triggers t print_formula f
  | _ -> assert false

and print_form_list fmt = List.iter (fprintf fmt "%a" print_formula)

let th_ext_of_string ext loc =
  match ext with
  | "Sum" -> Sum
  | "Arrays" -> Arrays
  | "Records" -> Records
  | "Bitv" -> Bitv
  | "LIA" -> LIA
  | "LRA" -> LRA

  | "NRA" -> NRA
  | "NIA" -> NIA
  | "FPA" -> FPA
  |  _ ->  Errors.error (Errors.ThExtError ext) loc

let string_of_th_ext ext =
  match ext with
  | Sum -> "Sum"
  | Arrays -> "Arrays"
  | Records -> "Records"
  | Bitv -> "Bitv"
  | LIA -> "LIA"
  | LRA -> "LRA"
  | NRA -> "NRA"
  | NIA -> "NIA"
  | FPA -> "FPA"


module Expr = struct

  (* Unified expressions.
     These are mainly there because alt-ergo distinguishes
     terms, atoms, and formulas, whereas some languages
     (and thus the typechecker) do not make this difference
     (for instance smtlib) *)
  type t =
    | Term of int atterm
    | Atom of int atatom
    | Form of int atform * Ty.tvar list
    (* Formulas also carry their set of explicitly
       quantified type variables, so that non top-level type
       variable quantification can be rejected as invalid. *)

  (* TODO: implement hash, compare and equal on typed terms *)

  let ty = function
    | Term { c = { tt_ty ; _ }; _ } -> tt_ty
    | Atom _
    | Form _ -> Ty.Safe.prop

  module Var = struct

    type t = {
      var : Symbols.t;
      ty  : Ty.t;
    }

    let hash { var; _ } = Symbols.hash var

    let compare v v' =
      Symbols.compare v.var v'.var

    let equal v v' = compare v v' = 0

    let ty { ty; _ } = ty

    let make var ty = { var; ty; }

    let mk name ty = make (Symbols.var name) ty

  end

  module Const = struct

    type t = {
      symbol : Symbols.t;
      vars : Ty.Safe.Var.t list;
      args : Ty.t list;
      ret  : Ty.t;
    }

    let hash { symbol; _ } = Symbols.hash symbol

    let compare c c' =
      Symbols.compare c.symbol c'.symbol

    let equal c c' = compare c c' = 0

    let arity c =
      List.length c.vars,
      List.length c.args

    let mk symbol vars args ret =
      { symbol; vars; args; ret; }

    let tag _ _ _ = ()

  end

  exception Term_expected
  exception Formula_expected
  exception Formula_in_term_let
  exception Deep_type_quantification
  exception Wrong_type of t * Ty.t
  exception Wrong_arity of Const.t * int * int

  (* Auxiliary functions. *)

  let promote_term = function
    | ((Term t) as e) when Ty.equal Ty.Safe.prop (ty e) ->
      Atom (mk (TApred (t, false)))
    | e -> e

  let promote_atom = function
    | Atom a -> Form (mk (TFatom a), [])
    | e -> e

  let expect_term = function
    | Term t -> t
    | Atom { c = TApred (t, false); _ } -> t
    | _ -> raise Term_expected

  let expect_formula t =
    match promote_atom @@ promote_term t with
    | Form (f, []) -> f
    | Form (_, _) -> raise Deep_type_quantification
    | _ -> raise Formula_expected


  (* Smart constructors:
     Wrappers to build term while checking the well-typedness *)

  let apply c tys args =
    (* check arity *)
    let n_ty = List.length tys in
    let n_args = List.length args in
    let a_ty, a_args = Const.arity c in
    if n_ty <> a_ty || n_args <> a_args then
      raise (Wrong_arity (c, n_ty, n_args))
    else begin
      (* compute the type variable substitution *)
      let s = List.fold_left2 (fun acc v ty ->
          Ty.M.add v.Ty.v ty acc) Ty.M.empty c.Const.vars tys in
      (* comptue the actual expected arguments types *)
      let expected_args_ty = List.map (Ty.apply_subst s) c.Const.args in
      (* check that the arsg have the expected type, and unwrap them *)
      let actual_args =
        List.map2 (fun t expected_ty ->
            if not (Ty.equal (ty t) expected_ty) then
              raise (Wrong_type (t, expected_ty))
            else expect_term t
          ) args expected_args_ty in
      (* compute the return type and create the resulting term. *)
      let ret_ty = Ty.apply_subst s c.Const.ret in
      promote_term (Term (
          mk ({ tt_ty = ret_ty;
                tt_desc = TTapp (c.Const.symbol, actual_args)})
        ))
    end

  let _true = Atom (mk TAtrue)
  let _false = Atom (mk TAfalse)

  let eq a b =
    let a_t = expect_term a in
    let b_t = expect_term b in
    let a_ty = a_t.c.tt_ty in
    let b_ty = b_t.c.tt_ty in
    if not (Ty.equal a_ty b_ty) then
      raise (Wrong_type (b, a_ty))
    else
      Atom (mk (TAeq [a_t; b_t]))

  let distinct = function
    | [] -> _true
    | x :: r ->
      let x_t = expect_term x in
      let expected_ty = x_t.c.tt_ty in
      let r' = List.map (fun t ->
          if not (Ty.equal expected_ty (ty t)) then
            raise (Wrong_type (t, expected_ty))
          else expect_term t
        ) r
      in
      Atom (mk (TAdistinct (x_t :: r')))

  let mk_form_op op l =
    let l_f = List.map expect_formula l in
    Form (mk (TFop(op, l_f)), [])

  let neg t = mk_form_op OPnot [t]
  let imply p q = mk_form_op OPimp [p; q]
  let equiv p q = mk_form_op OPiff [p; q]
  let xor p q = mk_form_op OPxor [p; q]

  let _and = mk_form_op OPand
  let _or = mk_form_op OPor


  (** free variable computation *)

  let rec fv_term_desc ty ((fv, bv) as acc) = function
    | TTconst _ -> fv
    | TTvar v ->
      if Symbols.Set.mem v bv then fv
      else Symbols.Map.add v ty fv
    (* neither infix nor prefix operators cannot be variables *)
    | TTinfix (l, _, r)             -> fv_term_list acc [l; r]
    | TTprefix (_, t)               -> fv_term acc t
    | TTapp (_, l)                  -> fv_term_list acc l
    | TTmapsTo (_, t)               -> fv_term acc t
    | TTinInterval (l, _, t, u, _)  -> fv_term_list acc [t; l; u]
    | TTget (a, i)                  -> fv_term_list acc [a; i]
    | TTset (a, i, v)               -> fv_term_list acc [a; i; v]
    | TTextract (a, i, l)           -> fv_term_list acc [a; i; l]
    | TTconcat (u, v)               -> fv_term_list acc [u; v]
    | TTdot (t, _)                  -> fv_term acc t
    | TTrecord l                    -> fv_term_list acc (List.map snd l)
    | TTnamed (_, t)                -> fv_term acc t
    | TTite (f, a, b)               -> fv_term_list ((fv_form acc f), bv) [a; b]
    | TTlet (l, body)               -> fv_term_let acc body l

  and fv_term_let ((fv, bv) as acc) body = function
    | [] -> fv_term acc body
    | (x, t) :: r ->
      let fv' = fv_term acc t in
      let bv' = Symbols.Set.add x bv in
      fv_term_let (fv', bv') body r

  and fv_term_list (fv, bv) l =
    let aux lv t = fv_term (lv, bv) t in
    List.fold_left aux fv l

  and fv_term acc t =
    fv_term_desc t.c.tt_ty acc t.c.tt_desc

  and fv_atom_desc ((fv, bv) as acc) = function
    | TAtrue | TAfalse -> fv
    | TAeq l | TAneq l
    | TAle l | TAlt l
    | TAdistinct l -> fv_term_list acc l
    | TApred (t, _) -> fv_term acc t

  and fv_atom acc a =
    fv_atom_desc acc a.c

  and fv_form_desc ((fv, bv) as acc) = function
    | TFatom a -> fv_atom acc a
    | TFop (_, l) -> fv_form_list acc l
    | TFforall q | TFexists q ->
      let aux m (v, ty) = Symbols.Map.add v ty m in
      List.fold_left aux fv q.qf_upvars
    | TFnamed (_, f) -> fv_form acc f
    | TFlet (l, _, _) ->
      let aux m (v, ty) = Symbols.Map.add v ty m in
      List.fold_left aux fv l

  and fv_form_let ((fv, bv) as acc) body = function
    | [] -> fv_form acc body
    | (v, TletTerm t) :: r ->
      let fv' = fv_term acc t in
      let bv' = Symbols.Set.add v bv in
      fv_form_let (fv', bv') body r
    | (v, TletForm f) :: r ->
      let fv' = fv_form acc f in
      let bv' = Symbols.Set.add v bv in
      fv_form_let (fv', bv') body r

  and fv_form_list (fv, bv) l =
    let aux lv t = fv_form (lv, bv) t in
    List.fold_left aux fv l

  and fv_form acc f =
    fv_form_desc acc f.c

  let _empty_acc = (Symbols.Map.empty, Symbols.Set.empty)

  (* NOTE: free type variables are not computed here. *)
  let to_fv m =
    [], Symbols.Map.fold (fun v ty acc ->
        Var.make v ty :: acc) m []

  let fv = function
    | Term t -> to_fv @@ fv_term _empty_acc t
    | Atom a -> to_fv @@ fv_atom _empty_acc a
    | Form (f, _) -> to_fv @@ fv_form _empty_acc f

  let var_to_tuple { Var.var; ty; } = var, ty

  let all (_, t_fv) (ty_qv, t_qv) e =
    let f = expect_formula e in
    let qf_bvars = List.map var_to_tuple t_qv in
    let qf_upvars = List.map var_to_tuple t_fv in
    Form (mk @@ TFforall {
        qf_bvars; qf_upvars;
        qf_triggers = [];
        qf_hyp = [];
        qf_form = f;
      }, ty_qv)

  let ex (_, t_fv) (ty_qv, t_qv) e =
    let f = expect_formula e in
    let qf_bvars = List.map var_to_tuple t_qv in
    let qf_upvars = List.map var_to_tuple t_fv in
    Form (mk @@ TFexists {
        qf_bvars; qf_upvars;
        qf_triggers = [];
        qf_hyp = [];
        qf_form = f;
      }, ty_qv)

  let letin l e =
    match promote_atom e with
    | Atom _ -> assert false
    | Term t ->
      let l' = List.map (fun (v, e') ->
          match e' with
          | Term t' -> v, t'
          | _ -> raise Formula_in_term_let
        ) l in
      Term (mk @@ { tt_desc = TTlet (l', t); tt_ty = t.c.tt_ty})
    | Form (f, []) ->
      let l' = List.map (fun (v, e') ->
          match promote_atom e' with
          | Term t' -> v, TletTerm t'
          | Form (f', []) -> v, TletForm f'
          | Form (_, _) -> raise Deep_type_quantification
          | Atom _ -> assert false
        ) l in
      let fv_m = fv_form_let _empty_acc f l' in
      let fv_l = Symbols.Map.fold (fun v ty acc -> (v, ty) :: acc) fv_m [] in
      Form (mk @@ TFlet (fv_l, l', f), [])
    | Form (_, _) -> raise Deep_type_quantification

end

