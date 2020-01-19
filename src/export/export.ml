(** Signature of a system. Any export system must comply with the signature
    {!val:S} defined here. *)

open Core
open Extras

(** Ast and interactions with Dk files that a system must provide. *)
module type AST =
sig
  type t

  val compile : Kernel.Basic.mident -> Parsing.Entry.entry list -> t
  (** [compile md es] builds an ast out of a list of Dedukti entries
      [es] coming from module [md]. *)

  val decompile : t -> Parsing.Entry.entry list
  (** [decompile ast] returns the list of Dedukti entries coming from
      ast [ast]. *)
end

(** Build rules for the system. Provides the rules, keys and values to use the
    build system {!module:Build.Classic}. *)
module type MAKEFILE =
sig
  open Build.Classic

  type key
  (** Keys or targets. *)

  type value
  (** Values are either the created files or the loaded signatures. *)

  val key_eq : key eq
  (** Equality on keys. *)

  val pp_key : key pp
  (** [pp_key fmt k] prints key [k] to formatter [fmt]. *)

  val valid_stored : key -> value -> bool
  (** [valid_stored k v] returns whether value [v] stored in the database is a
      valid value of key [k]. *)

  val want : string list -> key list
  (** [want p] creates targets out of paths [p]. Used to declare initial
      targets. *)

  (* val rules_for : string list -> (key, value) rule list *)
  (** [rules_for pth] creates the rules to export files in [pth]. The files
      [pth] are the Dedukti files selected from the command line. *)

  val rules : (key, value) rule list
  (** Static rules. *)

  val generators : (key, value) generator list
  (** Dynamic rules generators used *)
end

(** Type of a system. An export system must have this signature. *)
module type S =
sig
  module Ast : AST
  (** Representation of the Ast. *)

  module Mid : Middleware.S
  (** Middleware used for the json export. *)

  module Makefile : MAKEFILE
  (** Defines the rules to build targets. *)

  val file_ext : string
  (** Extension of files (without the dot). *)

  val export : Ast.t pp
  (** [export fmt ast] exports abstract syntax tree [ast] to formatter
      [fmt] in the syntax of the system. *)
end
