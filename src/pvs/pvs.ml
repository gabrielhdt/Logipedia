open Core
open Extras
open Export

module Ast : AST with type t = Sttfa.Ast.ast = Ast

module Mid : Middleware.S = Middleware.Sttfa

let export : Ast.t pp = fun fmt ast ->
  let (module M:Sttfa.Export.E) = Sttfa.Export.of_system `Pvs in
  M.print_ast fmt ast

module Makefile : Build_template.S =
struct
  open Build_template

  type key =
    [ `Kfile of path
    | `Ksign of mident
    | `Kchck of path
      (** A checked file. *) ]

  type value =
    [ `Vfile of path * float
    | `Vsign of entry list
    | `Vchck of path * float
      (** Checked file with time of last check. *) ]

  (** [want pth] declares path [pth] as a checked target. *)
  let want pth = `Kchck(pth)

  (** [atime p] returns the last access time of filepath [p]. *)
  let atime pth = Unix.((stat pth).st_atime)

  let valid_stored k v = match k, v with
    | `Kchck(p), `Vchck(_,t) -> Sys.file_exists p && t >= (atime p)
    | _                      -> Dk.valid_stored k v

  let pp_key fmt k = match k with
    | `Kchck(p) -> Format.fprintf fmt"%s checked" p
    | _         -> Dk.pp_key fmt k

  let key_eq k l = match k, l with
    | `Kchck(p), `Kchck(q) -> String.equal p q
    | _                    -> Dk.key_eq k l

  (** [rule_check t] specifies that file [t] should be checked with
      "proveit". *)
  let rule_check target : (key, value) Build.Classic.rule =
    let log_rule = Build.log_rule.logger in
    let m_creates = `Kchck(target) in
    let m_depends = [`Kfile(target)] in
    let m_action _ =
      let cmd =
        Format.sprintf "proveit --importchain --scripts --force %s" target
      in
      log_rule ~lvl:25 "%s" cmd;
      if Sys.command cmd <> 0 then log_rule ~lvl:10 "Command failure";
      `Vchck(target, atime target)
    in
    Build.Classic.{m_creates; m_depends; m_action}

  let rules_for files mk_target =
    let entries_pp md fmt ens = Ast.compile md ens |> export fmt in
    Sttfa.Makefile.rules_for files mk_target entries_pp @
    List.map (fun f -> rule_check (mk_target f)) files
end
