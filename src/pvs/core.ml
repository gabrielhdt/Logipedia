(** AST of PVS-core. *)

type top = Type
type ty =
  | Prop
  | YVar of tyvar
  | Prod of ty * (te, ty) Bindlib.binder
  (** Dependent product with domain. *)
  | Psub of (ty, te) Bindlib.binder
and te =
  | EVar of tevar
  | Fall of ty * (te, te) Bindlib.binder
  (** Forall with domain. *)
  | Impl of te * te
  | Abst of ty * (te, te) Bindlib.binder
  (** Abstraction with domain. *)
  | Appl of te * te

(** Type variable shortcut. *)
and tyvar = ty Bindlib.var

(** Term variable shortcut. *)
and tevar = te Bindlib.var

(** [te_mkfree x] injects a term variable [x] into a term. *)
let te_mkfree : tevar -> te = fun x -> EVar(x)

(** [ty_mkfree x] injects a type variable [x] into a type. *)
let ty_mkfree : tyvar -> ty = fun x -> YVar(x)

(** Term box shortcut. *)
type tebox = te Bindlib.box

(** Type box shortcut. *)
type tybox = ty Bindlib.box

(** [_Prod ty pb] lifts a product to a [ty] box. *)
let _Prod : tybox -> (te, ty) Bindlib.binder Bindlib.box -> tybox =
  Bindlib.box_apply2 (fun d b -> Prod(d, b))

(** Boxed version of {!constructor:Prop}. *)
let _Prop : tybox = Bindlib.box Prop

(** [_EVar v] injects variable [v] into a bindlib box. *)
let _EVar : tevar -> tebox = Bindlib.box_var

(** [_Fall d b] lifts binder [b] with domain [d] into a boxed
    {!constructor:Fall} *)
let _Fall : tybox -> (te, te) Bindlib.binder Bindlib.box -> tebox =
  Bindlib.box_apply2 (fun d b -> Fall(d, b))

(** [_Impl t u] lifts the implication [t ⇒ u] to a boxed implication. *)
let _Impl : tebox -> tebox -> tebox =
  Bindlib.box_apply2 (fun t u -> Impl(t, u))

(** [_Abst d b] lifts *)
let _Abst : tybox -> (te, te) Bindlib.binder Bindlib.box -> tebox =
  Bindlib.box_apply2 (fun d b -> Abst(d, b))

let _Appl : tebox -> tebox -> tebox =
  Bindlib.box_apply2 (fun t u -> Appl(t, u))

(** [telift te] lifts the term [te] to the {!type:tebox} type. *)
let rec telift : te -> tebox = function
  | EVar(x)   -> _EVar x
  | Fall(d,b) -> _Fall (tylift d) (Bindlib.box_binder telift b)
  | Impl(t,u) -> _Impl (telift t) (telift u)
  | Abst(d,b) -> _Abst (tylift d) (Bindlib.box_binder telift b)
  | Appl(t,u) -> _Appl (telift t) (telift u)

(** [tylift ty] lifts the type [ty] to the {!type:ty} type. *)
and tylift : ty -> tybox = function
  | Prop      -> _Prop
  | YVar(x)   -> Bindlib.box_var x
  | Prod(d,b) -> _Prod (tylift d) (Bindlib.box_binder tylift b)
  | Psub(_)   -> failwith "Not yet implemented"

(** Sets of term variables. *)
module TeVarSet = Set.Make(struct
    type t = tevar
    let compare = Bindlib.compare_vars
  end)
