open Core
open Extras
open Export

module Ast : AST with type t = Sttfa.Ast.ast = Ast

module Mid : Middleware.S = Middleware.Sttfa

let export : Ast.t pp = fun fmt ast ->
  let (module M:Sttfa.Export.E) = Sttfa.Export.of_system `Lean in
  M.print_ast fmt ast

module Makefile : MAKEFILE =
struct
  include Sttfa.Makefile.Basis

  let rules_for files mk_target =
    let entries_pp md fmt ens = Ast.compile md ens |> export fmt in
    Sttfa.Makefile.rules_for files mk_target entries_pp
end
