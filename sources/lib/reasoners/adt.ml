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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format
open Sig
open Exception
module Sy = Symbols
module T  = Term
module A  = Literal
module Hs = Hstring

type 'a abstract =
  | Constr of { c_name : Hs.t ; c_ty : Ty.t ; c_args : (Hs.t * 'a) list }
  | Select of { d_name : Hs.t ; d_ty : Ty.t ; d_arg : 'a }
  | Tester of { t_name : Hs.t ; t_arg : 'a }
  | Alien of 'a

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end


let constr_of_destr ty dest =
  fprintf fmt "ty = %a@." Ty.print ty;
  match ty with
  | Ty.Tadt (s, params, cases) ->
    begin
      try
        List.find
          (fun (c, destrs) ->
             List.exists (fun (d, _) -> Hstring.equal dest d) destrs
          )cases
      with Not_found -> assert false (* invariant *)
    end
  | _ -> assert false


module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  module SX = Set.Make(struct type t = r let compare = X.hash_cmp end)

  let name = "Adt"

  [@@ocaml.ppwarning "XXX: IsConstr not interpreted currently"]
  [@@ocaml.ppwarning "XXX: remove useless case Destructor from Symbols"]
  let is_mine_symb sy ty =
    match sy, ty with
    | Sy.Op (Sy.Constr _), Ty.Tadt _ -> true
    | Sy.Op Sy.Destruct (_, guarded), _ -> true
    | _ -> false

  let embed r =
    match X.extract r with
    | Some c -> c
    | None -> Alien r

  let print fmt = function
    | Alien x ->
      fprintf fmt "%a" X.print x

    | Constr {c_name; c_args} ->
      fprintf fmt "%a" Hs.print c_name;
      begin
        match c_args with
          [] -> ()
        | (lbl, v) :: l ->
          fprintf fmt " { %a = %a " Hs.print lbl X.print v;
          List.iter
            (fun (lbl, v) ->
               fprintf fmt "; %a = %a " Hs.print lbl X.print v) l;
          fprintf fmt "}"
      end

    | Select d ->
      fprintf fmt "%a#!%a" X.print d.d_arg Hs.print d.d_name
    | Tester t ->
      fprintf fmt "(%a ? %a)" X.print t.t_arg Hs.print t.t_name


  [@@ocaml.ppwarning "TODO: canonization is missing"]
  let is_mine u =
    match u with
    | Alien r -> r
    | Constr _ | Tester _ -> X.embed u
    | Select {d_arg; d_name} ->
      match embed d_arg with
      | Constr c ->
        begin
          try snd @@ List.find (fun (lbl, v) -> Hs.equal d_name lbl) c.c_args
          with Not_found ->
            fprintf fmt "is_mine %a failed@." print u;
            assert false
        end
      | _ -> X.embed u

  let equal s1 s2 =
    match s1, s2 with
    | Alien r1, Alien r2 -> X.equal r1 r2
    | Constr c1, Constr c2 ->
      Hstring.equal c1.c_name c2.c_name &&
      Ty.equal c1.c_ty c2.c_ty &&
      begin
        try
          List.iter2
            (fun (hs1, v1) (hs2, v2) ->
               assert (Hs.equal hs1 hs2);
               if not (X.equal v1 v2) then raise Exit
            )c1.c_args c2.c_args;
          true
        with
        | Exit -> false
        | _ -> assert false
      end

    | Select d1, Select d2 ->
      Hstring.equal d1.d_name d2.d_name &&
      Ty.equal d1.d_ty d2.d_ty &&
      X.equal d1.d_arg d2.d_arg

    | Tester t1, Tester t2 ->
      Hstring.equal t1.t_name t2.t_name &&
      X.equal t1.t_arg t2.t_arg

    | _ -> false


  [@@ocaml.ppwarning "TODO: canonization is missing"]
  let make t =
    if debug_adt () then
      eprintf "make %a@." T.print t;
    let {T.f; xs; ty} = T.view t in
    let _sx, ctx =
      List.fold_left
        (fun (args, ctx) s ->
           let rs, ctx' = X.make s in
           rs :: args, List.rev_append ctx' ctx
        )([], []) xs
    in
    let xs = List.rev _sx in
    match f, xs, ty with
    | Sy.Op Sy.Constr hs, _, Ty.Tadt (_,_,cases) ->
      let case_hs = try List.assoc hs cases with Not_found -> assert false in
      let c_args =
        try
          List.rev @@
          List.fold_left2
            (fun c_args v (lbl, _) -> (lbl, v) :: c_args)
            [] xs case_hs
        with _ -> assert false
      in
      is_mine @@
      Constr {c_name = hs; c_ty = ty; c_args}, ctx

    | Sy.Op Sy.Destruct (hs, guarded), [e], _ ->
      let sel = Select {d_name = hs ; d_arg = e ; d_ty = ty} in
      if not guarded then is_mine sel, ctx
      else
        X.term_embed t, ctx
    (* No risk !
         if equal sel (embed sel_x) then X.term_embed t, ctx
         else sel_x, ctx (* canonization OK *)
    *)
    | _ ->
      assert false

  let hash = function
    | Alien r ->
      X.hash r

    | Constr { c_name ; c_ty ; c_args } ->
      List.fold_left
        (fun acc (_, r) -> acc * 7 + X.hash r)
        (Hstring.hash c_name + 7 * Ty.hash c_ty) c_args

    | Select { d_name ; d_ty ; d_arg } ->
      ((Hstring.hash d_name + 11 * Ty.hash d_ty)) * 11 + X.hash d_arg

    | Tester { t_name ; t_arg } ->
      Hstring.hash t_name * 13 + X.hash t_arg

  let leaves r =
    let l = match r with
      | Alien r -> [Hs.empty, r]
      | Constr { c_args ; _ } ->  c_args
      | Select { d_arg  ; _ } -> [Hs.empty, d_arg]
      | Tester { t_arg  ; _ } -> [Hs.empty, t_arg]
    in
    SX.elements @@
    List.fold_left
      (fun sx (_, r) ->
         List.fold_left (fun sx x -> SX.add x sx) sx (X.leaves r)
      )SX.empty l

  [@@ocaml.ppwarning "TODO: not sure"]
  let fully_interpreted sb = false (* not sure *)

  let type_info = function
    | Alien r -> X.type_info r
    | Constr { c_ty ; _ } ->  c_ty
    | Select { d_ty  ; _ } -> d_ty
    | Tester _ -> Ty.Tbool

  exception Out of int

  let compare s1 s2 =
    match embed s1, embed s2 with
    | Alien r1, Alien r2 -> X.str_cmp r1 r2
    | Alien r1, _ -> 1
    | _, Alien r2 -> -1

    | Constr c1, Constr c2 ->
      let c = Hstring.compare c1.c_name c2.c_name in
      if c <> 0 then c
      else
        let c = Ty.compare c1.c_ty c2.c_ty in
        if c <> 0 then c
        else
          begin
            try
              List.iter2
                (fun (hs1, v1) (hs2, v2) ->
                   assert (Hs.equal hs1 hs2);
                   let c = X.str_cmp v1 v2 in
                   if c <> 0 then raise (Out c);
                )c1.c_args c2.c_args;
              0
            with
            | Out c -> c
            | _ -> assert false
          end
    | Constr _, _ -> 1
    | _, Constr _ -> -1

    | Select d1, Select d2 ->
      let c = Hstring.compare d1.d_name d2.d_name in
      if c <> 0 then c
      else
        let c = Ty.compare d1.d_ty d2.d_ty in
        if c <> 0 then c
        else X.str_cmp d1.d_arg d2.d_arg

    | Select _, _ -> 1
    | _, Select _ -> -1

    | Tester t1, Tester t2 ->
      let c = Hstring.compare t1.t_name t2.t_name in
      if c <> 0 then c
      else
        X.str_cmp t1.t_arg t2.t_arg

  let abstract_selectors p acc =
    match p with
    | Alien r -> assert false (* handled in Combine *)
    | Constr { c_args } ->
      let acc, args =
        List.fold_left (fun (acc, l) (lbl, x) ->
            let y, acc = X.abstract_selectors x acc in
            if not (X.equal x y)
                [@ocaml.ppwarning "TODO: abstract Selectors"] then
              assert false; (* TODO *)
            acc, (lbl, y) :: l
          ) (acc, []) c_args
      in
      is_mine p, acc

    | Tester {t_arg} ->
      let s_arg, acc = X.abstract_selectors t_arg acc in
      if not (X.equal s_arg t_arg)
          [@ocaml.ppwarning "TODO: abstract Selectors"] then
        assert false;
      is_mine p, acc

    | Select ({d_arg} as s)  [@ocaml.ppwarning "TODO: abstract Selectors"] ->
      (* no need to abstract THIS selector. It's necessiraly
         toplevel in ADTs *)
      let s_arg, acc = X.abstract_selectors d_arg acc in
      if not (X.equal s_arg d_arg)
          [@ocaml.ppwarning "TODO: abstract Selectors"] then
        assert false;
      let x = is_mine @@ Select {s with d_arg=s_arg} in
      begin match embed x  with
        | Select ({d_name; d_ty; d_arg} as s) ->
          let cstr, cstr_args = constr_of_destr (X.type_info d_arg) d_name in
          let xs = List.map (fun (_, ty) -> T.fresh_name ty) cstr_args in
          let cons = T.make (Sy.constr (Hs.view cstr)) xs (X.type_info d_arg) in
          if debug_adt () then
            fprintf fmt "abstr with equality %a == %a@."
              X.print d_arg T.print cons;
          let cons, _ = make cons in
          let acc = (d_arg, cons) :: acc in
          let xx = is_mine @@ Select {s with d_arg = cons} in
          if debug_adt () then
            fprintf fmt "%a becomes %a@." X.print x  X.print xx;
          xx, acc

        | _ ->
          x, acc

      end


  let is_alien_of e x =
    List.exists (fun y -> X.equal x y) (X.leaves e)

  let solve r1 r2 pb =
    if debug_adt () then
      Format.eprintf "[ADTs] solve %a = %a@." X.print r1 X.print r2;
    match embed r1, embed r2 with
    | Select _, _ | _, Select _ -> assert false (* should be eliminated *)
    | Tester _, _ | _, Tester _ -> assert false (* not interpreted *)
    | Alien _, Alien _ ->
      { pb with
        sbt = (if X.str_cmp r1 r2 > 0 then r1, r2 else r2, r1) :: pb.sbt }

    | Alien r, Constr _ ->
      if is_alien_of r2 r then raise Unsolvable;
      { pb with sbt = (r, r2) :: pb.sbt }

    | Constr _, Alien r ->
      if is_alien_of r1 r then raise Unsolvable;
      { pb with sbt = (r, r1) :: pb.sbt }

    | Constr c1, Constr c2 ->
      if not (Hstring.equal c1.c_name c2.c_name) then raise Unsolvable;
      try
        {pb with
         eqs =
           List.fold_left2
             (fun eqs (hs1, v1) (hs2, v2) ->
                assert (Hstring.equal hs1 hs2);
                (v1, v2) :: eqs
             )pb.eqs c1.c_args c2.c_args
        }
      with Invalid_argument _ -> assert false


  [@@ocaml.ppwarning "TODO: canonization is missing"]

  let subst p v s =
    match s with
    | Alien r -> if X.equal p r then v else X.subst p v r
    | Constr c ->
      is_mine @@
      Constr
        { c with
          c_args = List.map (fun (lbl, u) -> lbl, X.subst p v u) c.c_args }

    | Select d ->
      is_mine @@ Select { d with d_arg = X.subst p v d.d_arg }

    | Tester t ->
      is_mine @@ Tester { t with t_arg = X.subst p v t.t_arg }


  let color _        = assert false

  let term_extract _ = None, false


  let assign_value r _ eq = assert false
  let choose_adequate_model t _ l = assert false


  (***

     (*BISECT-IGNORE-BEGIN*)
     module Debug = struct

     let solve_bis a b =
      if debug_sum () then fprintf fmt "[Sum] we solve %a = %a@."
        X.print a X.print b

     let solve_bis_result res =
      if debug_sum () then
        match res with
          | [p,v] -> fprintf fmt "\twe get: %a |-> %a@." X.print p X.print v
          | []    -> fprintf fmt "\tthe equation is trivial@."
          | _ -> assert false

     let solve_bis_unsolvable () =
      if debug_sum () then fprintf fmt "\tthe equation is unsolvable@."

     end
     (*BISECT-IGNORE-END*)

     let print = Debug.print

   ***)
end

module Relation (X : ALIEN) (Uf : Uf.S with type r = X.r) = struct

  type r = X.r
  type uf = Uf.t

  module Ex = Explanation
  module ST = T.Set
  module MT = T.Map
  module HSS = Hs.Set
  module Sh = Shostak(X)
  open Sh
  module MX = Map.Make (struct type t = X.r let compare = X.hash_cmp end)
  module LR =
    Literal.Make(struct type t = X.r let compare = X.hash_cmp include X end)
  module MA = A.LT.Map
  module SA = A.LT.Set
  module MHs = Hs.Map

  type t =
    {
      classes : Term.Set.t list;
      domains : (HSS.t * Explanation.t) MX.t;
      seen_destr : ST.t;
      seen_access : ST.t;
      seen_testers : HSS.t MX.t;
      [@ocaml.ppwarning "selectors should be improved. only representatives \
                         in it. No true or false _is"]

        selectors : (Literal.LT.t * Ex.t) list MHs.t MX.t;
      size_splits : Numbers.Q.t;
      new_terms : T.Set.t;
      pending_deductions : (Literal.LT.t * Ex.t) list;
    }

  let empty classes = {
    classes;
    domains = MX.empty;
    seen_destr = ST.empty;
    seen_access = ST.empty;
    seen_testers = MX.empty;
    selectors = MX.empty;
    size_splits = Numbers.Q.one;
    new_terms = T.Set.empty;
    pending_deductions = [];
  }


  (* ################################################################ *)
  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let assume bol r1 r2 =
      if debug_adt () then
        fprintf fmt "[Sum.Rel] we assume %a %s %a@."
          X.print r1 (if bol then "=" else "<>") X.print r2

    let print_env loc env =
      if debug_adt () then begin
        fprintf fmt "--ADT env %s ---------------------------------@." loc;
        MX.iter
          (fun r (hss, ex) ->
             fprintf fmt "%a ::= " X.print r;
             begin
               match HSS.elements hss with
                 []      -> ()
               | hs :: l ->
                 fprintf fmt " %s" (Hs.view hs);
                 List.iter (fun hs -> fprintf fmt " | %s" (Hs.view hs)) l
             end;
             fprintf fmt " : %a@." Ex.print ex;

          ) env.domains;
        fprintf fmt "-- seen testers ---------------------------@.";
        MX.iter
          (fun r hss ->
             HSS.iter
               (fun hs ->
                  fprintf fmt "(%a is %a)@." X.print r Hs.print hs
               )hss
          )env.seen_testers;
        fprintf fmt "-- selectors ------------------------------@.";
        MX.iter
          (fun r mhs ->
             MHs.iter
               (fun hs l ->
                  List.iter (fun (a, _) ->
                      fprintf fmt "(%a is %a) ==> %a@."
                        X.print r Hs.print hs A.LT.print a
                    ) l
               )mhs
          )env.selectors;
        fprintf fmt "-------------------------------------------@.";
      end

    let case_split r r' =
      if debug_adt () then
        fprintf fmt "[ADT.case-split] %a = %a@." X.print r X.print r'

    let no_case_split () =
      if debug_adt () then fprintf fmt "[ADT.case-split] nothing@."

    let add r =
      if debug_adt () then fprintf fmt "ADT.Rel.add: %a@." X.print r

  end
  (*BISECT-IGNORE-END*)
  (* ################################################################ *)


  let print_model fmt env l = ()
  let new_terms env = env.new_terms
  let instantiate ~do_syntactic_matching _ env uf _ = env, []

  let assume_th_elt t th_elt dep =
    assert false


  let values_of ty =
    match ty with
    | Ty.Tadt (_,_,l) ->
      Some (List.fold_left (fun st (hs, _) -> HSS.add hs st) HSS.empty l)
    | _ -> None

  let add_adt env t r sy ty =
    if MX.mem r env.domains then env
    else
      match sy, ty with
      | Sy.Op Sy.Constr hs, Ty.Tadt _ ->
        if debug_adt () then Format.eprintf "new ADT expr(C): %a@." T.print t;
        { env with domains =
                     MX.add r (HSS.singleton hs, Ex.empty) env.domains }

      | _, Ty.Tadt _ ->
        if debug_adt () then Format.eprintf "new ADT expr: %a@." T.print t;
        let constrs =
          match values_of ty with None -> assert false | Some s -> s
        in
        { env with domains = MX.add r (constrs, Ex.empty) env.domains }

      | _ -> env

  let seen_tester r hs env =
    try HSS.mem hs (MX.find r env.seen_testers)
    with Not_found -> false

  let update_tester r hs env =
    let old = try MX.find r env.seen_testers with Not_found -> HSS.empty in
    {env with seen_testers = MX.add r (HSS.add hs old) env.seen_testers}

  let trivial_tester r hs =
    match embed r with (* can filter further/better *)
    | Constr {c_name} -> Hstring.equal c_name hs
    | _ -> false

  [@@ocaml.ppwarning "XXX improve. For each selector, store its \
                      corresponding constructor when typechecking ?"]
  let add_guarded_destr env uf t hs e t_ty =
    if debug_adt () then
      Format.eprintf "new (guarded) Destr: %a@." T.print t;
    let env = { env with seen_destr = ST.add t env.seen_destr } in
    let c, _ = constr_of_destr (T.view e).T.ty hs in
    let access = T.make (Sy.destruct (Hs.view hs) ~guarded:false) [e] t_ty in
    let is_c = A.LT.mk_builtin true (A.IsConstr c) [e] in
    let eq = A.LT.mk_eq access t in
    if debug_adt () then begin
      fprintf fmt "associated with constr %a@." Hstring.print c;
      fprintf fmt "%a => %a@." A.LT.print is_c A.LT.print eq;
    end;
    let r_e, ex_e = try Uf.find uf e with Not_found -> assert false in
    if trivial_tester r_e c then
      {env with pending_deductions = (eq, ex_e) :: env.pending_deductions}
    else
    if seen_tester r_e c env then
      {env with pending_deductions = (eq, ex_e) :: env.pending_deductions}
    else
      let m_e = try MX.find r_e env.selectors with Not_found -> MHs.empty in
      let old = try MHs.find c m_e with Not_found -> [] in
      { env with selectors =
                   MX.add r_e (MHs.add c ((eq, ex_e)::old) m_e)
                     env.selectors }


  [@@ocaml.ppwarning "working with X.term_extract r would be sufficient ?"]
  let add env (uf:uf) (r:r) t =
    let {T.f=sy; xs; ty} = T.view t in
    let env = add_adt env t r sy ty in
    match sy, xs with
    | Sy.Op Sy.Destruct (hs, true), [e] -> (* guarded *)
      if debug_adt () then
        fprintf fmt "[ADTs] add guarded destruct: %a@." T.print t;
      if (ST.mem t env.seen_destr) then env
      else add_guarded_destr env uf t hs e ty

    | Sy.Op Sy.Destruct (_, false), [_] -> (* not guarded *)
      if debug_adt () then
        fprintf fmt "[ADTs] add unguarded destruct: %a@." T.print t;
      { env with seen_access = ST.add t env.seen_access }

    | Sy.Op Sy.Destruct _, _ ->
      assert false (* not possible *)

    (*| Sy.Op Sy.IsConstr _, _ ->
       if debug_adt () then
         Format.eprintf "new Tester: %a@." T.print t;
       { env with seen_testers = ST.add t env.seen_testers }
    *)
    | _ -> env

  let add env uf r t =
    Debug.print_env "before add" env;
    let env = add env uf r t in
    Debug.print_env "after add" env;
    env

  let count_splits env la =
    let nb =
      List.fold_left
        (fun nb (_,_,_,i) ->
           match i with
           | CS (Th_sum, n) -> Numbers.Q.mult nb n
           | _ -> nb
        )env.size_splits la
    in
    {env with size_splits = nb}

  let deduce_is_constr uf r h eqs env ex =
    let r, ex' = try Uf.find_r uf r with Not_found -> assert false in
    let ex = Ex.union ex ex' in
    match embed r with
    | Alien r ->
      begin match X.term_extract r with
        | Some t, _ ->
          let eqs =
            if seen_tester r h env then eqs
            else
              let is_c = A.LT.mk_builtin true (A.IsConstr h) [t] in
              if debug_adt () then
                fprintf fmt "[deduce is_constr] %a@." A.LT.print is_c;
              (Sig.LTerm is_c, ex, Sig.Other) :: eqs
          in
          begin
            match T.view t with
            | {T.ty = Ty.Tadt (_,_,cases) as ty} ->
              (* Only do this deduction for finite types ??
                   may not terminate in some cases otherwise.
                   eg. type t = A of t
                   goal g: forall e,e' :t. e = C(e') -> false
                   + should not be guareded by "seen_tester"
              *)
              let c, args =
                try List.find (fun (c, _) -> Hstring.equal h c) cases
                with Not_found -> assert false
              in
              let xs = List.map (fun (_, ty) -> T.fresh_name ty) args in
              let cons = T.make (Sy.constr (Hs.view h)) xs ty in
              let env = {env with new_terms = ST.add cons env.new_terms} in
              let eq = A.LT.mk_eq t cons in
              if debug_adt () then
                fprintf fmt "[deduce equal to constr] %a@." A.LT.print eq;
              let eqs = (Sig.LTerm eq, ex, Sig.Other) :: eqs in
              env, eqs
            | _ -> env, eqs
          end
        | _ ->
          fprintf fmt "%a@." X.print r;
          assert false
      end
    | _ -> env,eqs

  let add_diseq uf hss sm1 sm2 dep env eqs =
    match sm1, sm2 with
    | Alien r , Constr {c_name = h; c_args = []}
    | Constr {c_name = h; c_args = []}, Alien r  ->
      (* not correct with args *)
      let enum, ex =
        try MX.find r env.domains with Not_found -> hss, Ex.empty
      in
      let enum = HSS.remove h enum in
      let ex = Ex.union ex dep in
      if HSS.is_empty enum then raise (Inconsistent (ex, env.classes))
      else
        let env = { env with domains = MX.add r (enum, ex) env.domains } in
        if HSS.cardinal enum = 1 then
          let h' = HSS.choose enum in
          let env, eqs = deduce_is_constr uf r h' eqs env ex in
          env, eqs
        else env, eqs

    | Alien r , Constr _ | Constr _, Alien r  ->
      env, eqs

    | Alien r1, Alien r2 ->
      let enum1,ex1=
        try MX.find r1 env.domains with Not_found -> hss,Ex.empty in
      let enum2,ex2=
        try MX.find r2 env.domains with Not_found -> hss,Ex.empty in

      let env, eqs =
        if HSS.cardinal enum1 = 1 then
          let ex = Ex.union dep ex1 in
          let h' = HSS.choose enum1 in
          deduce_is_constr uf r1 h' eqs env ex
        else env, eqs
      in
      let env, eqs =
        if HSS.cardinal enum2 = 1 then
          let ex = Ex.union dep ex2 in
          let h' = HSS.choose enum2 in
          deduce_is_constr uf r2 h' eqs env ex
        else env, eqs
      in
      env, eqs

    |  _ -> env, eqs

  let assoc_and_remove_selector hs r env =
    try
      let mhs = MX.find r env.selectors in
      let deds = MHs.find hs mhs in
      let mhs = MHs.remove hs mhs in
      deds,
      (if MHs.is_empty mhs then {env with selectors = MX.remove r env.selectors}
       else {env with selectors = MX.add r mhs env.selectors})

    with Not_found ->
      [], env

  let assume_is_constr uf hs r dep env eqs =
    match embed r with
    | Constr{c_name} when not (Hs.equal c_name hs) ->
      raise (Inconsistent (dep, env.classes));
    | _ ->
      if debug_adt () then
        fprintf fmt "assume is constr %a %a@." X.print r Hs.print hs;
      if seen_tester r hs env then
        env, eqs
      else
        let deds, env = assoc_and_remove_selector hs r env in
        let eqs =
          List.fold_left
            (fun eqs (ded, dep') ->
               (Sig.LTerm ded, Ex.union dep dep', Sig.Other) :: eqs
            )eqs deds
        in
        let env = update_tester r hs env in

        let enum, ex =
          try MX.find r env.domains
          with Not_found ->
          (*Cannot just put assert false !
            some terms are not well inited *)
          match values_of (X.type_info r) with
          | None -> assert false
          | Some s -> s, Ex.empty
        in
        let ex = Ex.union ex dep in
        if not (HSS.mem hs enum) then raise (Inconsistent (ex, env.classes));
        let env, eqs = deduce_is_constr uf r hs eqs env ex in
        {env with domains = MX.add r (HSS.singleton hs, ex) env.domains} , eqs

  let assume_not_is_constr uf hs r dep env eqs =
    match embed r with
    | Constr{c_name} when Hs.equal c_name hs ->
      raise (Inconsistent (dep, env.classes));
    | _ ->

      let _, env = assoc_and_remove_selector hs r env in
      let enum, ex =
        try MX.find r env.domains with
          Not_found ->
          (* semantic values may be not inited with function add *)
          match values_of (X.type_info r) with
          | Some s -> s, Ex.empty
          | None -> assert false
      in
      if not (HSS.mem hs enum) then env, eqs
      else
        let enum = HSS.remove hs enum in
        let ex = Ex.union ex dep in
        if HSS.is_empty enum then raise (Inconsistent (ex, env.classes))
        else
          let env = { env with domains = MX.add r (enum, ex) env.domains } in
          if HSS.cardinal enum = 1 then
            let h' = HSS.choose enum in
            let env, eqs = deduce_is_constr uf r h' eqs env ex in
            env, eqs
          else env, eqs



  (* dot it modulo equivalence class ? or is it sufficient ? *)
  let add_eq uf hss sm1 sm2 dep env eqs =
    match sm1, sm2 with
    | Alien r, Constr {c_name=h} | Constr {c_name=h}, Alien r  ->
      let enum, ex =
        try MX.find r env.domains with Not_found -> hss, Ex.empty
      in
      let ex = Ex.union ex dep in
      if not (HSS.mem h enum) then raise (Inconsistent (ex, env.classes));
      let env, eqs = deduce_is_constr uf r h eqs env ex in
      {env with domains = MX.add r (HSS.singleton h, ex) env.domains} , eqs

    | Alien r1, Alien r2   ->
      let enum1,ex1 =
        try MX.find r1 env.domains with Not_found -> hss, Ex.empty in
      let enum2,ex2 =
        try MX.find r2 env.domains with Not_found -> hss, Ex.empty in
      let ex = Ex.union dep (Ex.union ex1 ex2) in
      let diff = HSS.inter enum1 enum2 in
      if HSS.is_empty diff then raise (Inconsistent (ex, env.classes));
      let domains = MX.add r1 (diff, ex) env.domains in
      let env = {env with domains = MX.add r2 (diff, ex) domains } in
      if HSS.cardinal diff = 1 then begin
        fprintf fmt "XXX: make a deduction here@.";
        let h' = HSS.choose diff in
        let env, eqs = deduce_is_constr uf r1 h' eqs env ex in
        let env, eqs = deduce_is_constr uf r2 h' eqs env ex in

           (*
           let ty = X.type_info r1 in
           env,
           (LSem (LR.mkv_eq r1 (is_mine (Cons(h',ty)))), ex, Sig.Other)::eqs
            *)
        env, eqs
      end
      else env, eqs

    |  _ -> env, eqs


  let add_aux env r =
    Debug.add r;
    match embed r with
    | Alien r when not (MX.mem r env.domains) ->
      begin match values_of (X.type_info r) with
        | Some s -> { env with domains = MX.add r (s, Ex.empty) env.domains }
        | None ->
          env
      end
    | _ -> env

  (* needed for models generation because fresh terms are not
     added with function add *)
  let add_rec env r = List.fold_left add_aux env (X.leaves r)

  let update_cs_modulo_eq r1 r2 ex env eqs =
    (* PB Here: even if Subst, we are not sure that it was
       r1 |-> r2, because LR.mkv_eq may swap r1 and r2 *)
    try
      let old = MX.find r1 env.selectors in
      if debug_adt () then
        fprintf fmt "update selectors modulo eq: %a |-> %a@."
          X.print r1 X.print r2;
      let mhs = try MX.find r2 env.selectors with Not_found -> MHs.empty in
      let eqs = ref eqs in
      let _new =
        MHs.fold
          (fun hs l mhs ->
             if trivial_tester r2 hs then begin
               if debug_adt () then
                 fprintf fmt "make deduction because %a ? %a is trivial @."
                   X.print r2 Hs.print hs;
               List.iter
                 (fun (a, dep) -> eqs := (LTerm a, dep, Sig.Other) :: !eqs) l;
             end;
             let l = List.rev_map (fun (a, dep) -> a, Ex.union ex dep) l in
             MHs.add hs l mhs
          )old mhs
      in
      { env with selectors = MX.add r2 _new env.selectors }, !eqs
    with Not_found -> env, eqs

  let assume env uf la =
    let env = count_splits env la in
    let classes = Uf.cl_extract uf in
    let env = { env with classes = classes } in
    let aux bol r1 r2 dep env eqs = function
      | None     -> env, eqs
      | Some hss ->
        Debug.assume bol r1 r2;
        if bol then
          add_eq uf hss (embed r1) (embed r2) dep env eqs
        else
          add_diseq uf hss (embed r1) (embed r2) dep env eqs
    in
    Debug.print_env "before assume" env;
    let env, eqs =
      List.fold_left
        (fun (env,eqs) -> function
           | A.Eq(r1,r2), _, ex, orig ->
             (* needed for models generation because fresh terms are not
                added with function add *)
             let env = add_rec (add_rec env r1) r2 in
             let env, eqs =
               if orig == Sig.Subst then update_cs_modulo_eq r1 r2 ex env eqs
               else env, eqs
             in
             aux true  r1 r2 ex env eqs (values_of (X.type_info r1))

           | A.Distinct(false, [r1;r2]), _, ex, _ ->
             (* needed for models generation because fresh terms are not
                added with function add *)
             let env = add_rec (add_rec env r1) r2 in
             aux false r1 r2 ex env eqs (values_of (X.type_info r1))

           | A.Builtin(true, A.IsConstr hs, [e]), _, ex, _ ->
             assume_is_constr uf hs e ex env eqs

           | A.Builtin(false, A.IsConstr hs, [e]), _, ex, _ ->
             fprintf fmt "TODO: assume not (. ? .)@.";
             assume_not_is_constr uf hs e ex env eqs

           | _ -> env, eqs

        ) (env,[]) la
    in
    let eqs =
      List.fold_left
        (fun eqs (a, ex) -> (LTerm a, ex, Sig.Other) :: eqs)
        eqs env.pending_deductions
    in
    let env = {env with pending_deductions = []} in
    Debug.print_env "after assume" env;
    if debug_adt () then begin
      fprintf fmt "[ADT] assume deduced %d equalities@." (List.length eqs);
      List.iter
        (fun (a, _, _) ->
           match a with
           | LTerm a -> fprintf fmt "  %a@." A.LT.print a;
           | _ -> assert false
        )eqs;
    end;
    env, { assume = eqs; remove = [] }


  (* ################################################################ *)

  let two = Numbers.Q.from_int 2
  let case_split env uf ~for_model =
    assert (not for_model);
    Debug.print_env "before cs" env;
    try
      let r, mhs = MX.choose env.selectors in
      fprintf fmt "found r = %a@." X.print r;
      let hs, _ = MHs.choose mhs in
      fprintf fmt "found hs = %a@." Hs.print hs;
      (* cs on negative version would be better in general *)
      let cs =  LR.mkv_builtin false (A.IsConstr hs) [r] in
      [ cs, true, CS(Th_adt, two) ]
    with Not_found ->
      Debug.no_case_split ();
      []

  let case_split env uf ~for_model =
    []


  let query env uf a_ex = Sig.No
                            (*
    try ignore(assume env uf [a_ex]); Sig.No
    with Inconsistent (expl, classes) -> Sig.Yes (expl, classes)
                             *)
  (* ################################################################ *)
  (* ################################################################ *)
  (* ################################################################ *)
  (***
     type r = X.r
     type uf = Uf.t

     module Sh = Shostak(X)
     open Sh

     module Ex = Explanation

     module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
     module HSS = Set.Make (struct type t=Hs.t let compare = Hs.compare end)


     type t = { mx : (HSS.t * Ex.t) MX.t; classes : Term.Set.t list;
             size_splits : Numbers.Q.t }

     let empty classes = { mx = MX.empty; classes = classes;
                        size_splits = Numbers.Q.one }



     let add_eq hss sm1 sm2 dep env eqs =
     match sm1, sm2 with
      | Alien r, Cons(h,ty) | Cons (h,ty), Alien r  ->
        let enum, ex = try MX.find r env.mx with Not_found -> hss, Ex.empty in
        let ex = Ex.union ex dep in
        if not (HSS.mem h enum) then raise (Inconsistent (ex, env.classes));
     	{env with mx = MX.add r (HSS.singleton h, ex) env.mx} , eqs

      | Alien r1, Alien r2   ->
        let enum1,ex1 =
          try MX.find r1 env.mx with Not_found -> hss, Ex.empty in
        let enum2,ex2 =
          try MX.find r2 env.mx with Not_found -> hss, Ex.empty in
        let ex = Ex.union dep (Ex.union ex1 ex2) in
        let diff = HSS.inter enum1 enum2 in
        if HSS.is_empty diff then raise (Inconsistent (ex, env.classes));
        let mx = MX.add r1 (diff, ex) env.mx in
        let env = {env with mx = MX.add r2 (diff, ex) mx } in
        if HSS.cardinal diff = 1 then
          let h' = HSS.choose diff in
          let ty = X.type_info r1 in
          env, (LSem (LR.mkv_eq r1 (is_mine (Cons(h',ty)))), ex, Sig.Other)::eqs
        else env, eqs

      |  _ -> env, eqs


     let assume env uf la =
     let env = count_splits env la in
     let classes = Uf.cl_extract uf in
     let env = { env with classes = classes } in
     let aux bol r1 r2 dep env eqs = function
      | None     -> env, eqs
      | Some hss ->
        Debug.assume bol r1 r2;
        if bol then
          add_eq hss (embed r1) (embed r2) dep env eqs
        else
          add_diseq hss (embed r1) (embed r2) dep env eqs
     in
     Debug.print_env env;
     let env, eqs =
      List.fold_left
        (fun (env,eqs) -> function
          | A.Eq(r1,r2), _, ex, _ ->
            (* needed for models generation because fresh terms are not
               added with function add *)
            let env = add_rec (add_rec env r1) r2 in
     	    aux true  r1 r2 ex env eqs (values_of r1)

          | A.Distinct(false, [r1;r2]), _, ex, _ ->
            (* needed for models generation because fresh terms are not
               added with function add *)
            let env = add_rec (add_rec env r1) r2 in
     	    aux false r1 r2 ex env eqs (values_of r1)

          | _ -> env, eqs

        ) (env,[]) la
     in
     env, { assume = eqs; remove = [] }

     let add env _ r _ = add_aux env r

     let case_split env uf ~for_model =
     let acc = MX.fold
      (fun r (hss, ex) acc ->
        let sz = HSS.cardinal hss in
        if sz = 1 then acc
        else match acc with
     	| Some (n,r,hs) when n <= sz -> acc
     	| _ -> Some (sz, r, HSS.choose hss)
      ) env.mx None
     in
     match acc with
     | Some (n,r,hs) ->
      let n = Numbers.Q.from_int n in
      if for_model ||
        Numbers.Q.compare
        (Numbers.Q.mult n env.size_splits) (max_split ()) <= 0  ||
        Numbers.Q.sign  (max_split ()) < 0 then
        let r' = is_mine (Cons(hs,X.type_info r)) in
        Debug.case_split r r';
        [LR.mkv_eq r r', true, CS(Th_sum, n)]
      else []
     | None ->
      Debug.no_case_split ();
      []

     let query env uf a_ex =
     try ignore(assume env uf [a_ex]); Sig.No
     with Inconsistent (expl, classes) -> Sig.Yes (expl, classes)

     let assume env uf la =
     if Options.timers() then
      try
     	Timers.exec_timer_start Timers.M_Sum Timers.F_assume;
     	let res =assume env uf la in
     	Timers.exec_timer_pause Timers.M_Sum Timers.F_assume;
     	res
      with e ->
     	Timers.exec_timer_pause Timers.M_Sum Timers.F_assume;
     	raise e
     else assume env uf la

     let query env uf la =
     if Options.timers() then
      try
     	Timers.exec_timer_start Timers.M_Sum Timers.F_query;
     	let res = query env uf la  in
     	Timers.exec_timer_pause Timers.M_Sum Timers.F_query;
     	res
      with e ->
     	Timers.exec_timer_pause Timers.M_Sum Timers.F_query;
     	raise e
     else query env uf la


     let print_model _ _ _ = ()

     let new_terms env = Term.Set.empty

     let instantiate ~do_syntactic_matching _ env uf _  = env, []
     let assume_th_elt t th_elt dep =
     match th_elt.Commands.extends with
     | Typed.Sum ->
      failwith "This Theory does not support theories extension"
     | _ -> t
   ***)
end
