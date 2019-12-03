(** Translates the sttfa ast to a PVS core ast. *)
open Core
open Extras
module A = Ast

(** Manipulation of context. *)
module Context =
struct
  type t =
    { ctx_te : tevar StrMap.t
    ; ctx_ty : tyvar StrMap.t }

  (** [add_tevar v tev ctx] returns context [ctx] with a term variable [tev]
      whose name was [v] (in STTfa). *)
  let add_tevar : string -> tevar -> t -> t =
    fun v tev ({ctx_te; _} as ctx) ->
    {ctx with ctx_te = StrMap.add v tev ctx_te}

  (** [add_tyvar v tev ctx] returns context [ctx] with a type variable [tyv]
      whose name was [v] (in STTfa). *)
  let add_tyvar : string -> tyvar -> t -> t =
    fun v tyv ({ctx_ty; _} as ctx) ->
    {ctx with ctx_ty = StrMap.add v tyv ctx_ty}
end

(** [mk_type ty] transforms an STTfa type to a PVS core type. *)
let rec mk_type : A._ty -> ty = function
  | A.TyVar(v)       -> YVar(Bindlib.new_var ty_mkfree v)
  | A.Arrow(tyl,tyr) ->
    let x = Bindlib.new_var te_mkfree "p" in
    _Prod
      (tylift (mk_type tyl))
      (Bindlib.bind_var x (tylift (mk_type tyr))) |>
    Bindlib.unbox
  | A.Prop           -> Prop
  | A.TyOp(_)        -> failwith "Not yet implemented"

(** [mk_poly_type ty] transforms an STTfa polymorphic type into a PVS core
    type. *)
let rec mk_poly_type : A.ty -> ty = function
  | A.ForallK(_,ty) -> mk_poly_type ty
  | A.Ty(mty)       -> mk_type mty

(** [mk_term ctx t] creates a PVS core term from a sttfa monomorphic term
    [t] and context [ctx]. *)
let rec mk_term : Context.t -> Ast._te -> te = fun ctx te ->
  match te with
  | A.TeVar(v)        -> EVar(Bindlib.new_var te_mkfree v)
  | A.Abs(v,ty,te)    ->
    (* Get appropriate variable from context. *)
    let x = Bindlib.new_var te_mkfree v in
    let ctx = Context.add_tevar v x ctx in
    let b = Bindlib.bind_var x (telift (mk_term ctx te)) in
    Abst((mk_type ty), Bindlib.unbox b)
  | A.App(l,r)        ->
    Appl(mk_term ctx l, mk_term ctx r)
  | A.Forall(v,ty,te) ->
    let x = Bindlib.new_var te_mkfree v in
    let ctx = Context.add_tevar v x ctx in
    let b = Bindlib.bind_var x (telift (mk_term ctx te)) in
    Fall(mk_type ty, Bindlib.unbox b)
  | A.Impl(l,r)       -> Impl(mk_term ctx l, mk_term ctx r)
  | AbsTy(v,te)       ->
    let x = Bindlib.new_var ty_mkfree v in
    let ctx = Context.add_tyvar v x ctx in
    mk_term ctx te
  | Cst(_) -> failwith "Not yet implemented"

(** [mk_poly_term ctx t] creates a PVS core term from a polymorphic sttfa
    term [t] and context [ctx]. *)
let rec mk_poly_term : Context.t -> Ast.te -> te = fun ctx te ->
  match te with
  | ForallP(v,t) ->
    let x = Bindlib.new_var ty_mkfree v in
    let ctx = Context.add_tyvar v x ctx in
    mk_poly_term ctx t
  | Te(t) -> mk_term ctx t
