(** Define some rule making facilites for export from STTfa. *)
open Core
open Build.Classic
open Console
open Extras
open Build_template

let log_rule = Build.log_rule.logger

(** The rule of a system file roughly looks like, where [export] is the export
    folder, [sys] the extension of the system files, [file] the module,

    {v
    `Vfile(export/file.sys): `Vsign(entries)
         entries_pp entries
    v} *)

(** [mk_sysrule target entries_pp md] creates a rule that prints entries of
    module [md] with [entries_pp md] into file [target]. *)
let mk_sysrule : path -> (mident -> entry list pp) -> mident -> (_, _) rule =
  fun tg pp_entries md ->
  let pp_entries = pp_entries md in
  let print entries =
    log_rule ~lvl:25 "printing [%s]" tg;
    let ochan = open_out tg in
    let ofmt = Format.formatter_of_out_channel ochan in
    match entries with
    | [`Vsign(entries)] ->
      pp_entries ofmt entries;
      close_out ochan;
      `Vfile(mtime tg)
    | _                 -> assert false
  in
  (target (`Kfile(tg))) +< (`Ksign(md)) |> assemble print

(** [rules_for files mk_target entries_pp] yields all the rules necessary to
    export source files [files] using [entries_pp] to print entries. The
    function [mk_target] transforms a file of [files] into the target filepath.
    [entries_pp] is a function such that for any module [md], [entries_pp md] is
    a usable printer for entries. *)
let rules_for : path list -> (path -> path) -> (mident -> entry list pp) ->
  (_, _) rule list =
  fun files mk_target entries_pp ->
  let module B = Kernel.Basic in
  let module E = Api.Env.Default in
  let sigrule f = Sign.mk_sigrule (E.init f) in
  let sysrule f = mk_sysrule (mk_target f) entries_pp (E.init f) in
  let objrule f = Dkob.mk_dko ~incl:(B.get_path ()) f in
  let logic_rules =
    (* Kind of unsafe *)
    let sttfamd = B.mk_mident "sttfa" in
    [Sign.mk_sigrule sttfamd; objrule (Api.Dep.get_file sttfamd)]
  in
  logic_rules @
  (List.map (fun t -> [objrule t; sigrule t; sysrule t]) files |> List.flatten)

(** A basis for sttfa makefiles. *)
module Basis =
struct
  open Build_template

  type key =
    [ `Kfile of path
    | `Ksign of mident ]

  type value =
    [ `Vfile of float
    | `Vsign of entry list ]

  let key_eq k l =
    match k, l with
    | `Kfile(p), `Kfile(q) -> Dkob.key_eq p q
    | `Ksign(m), `Ksign(n) -> Sign.key_eq m n
    | _                    -> false

  let valid_stored k v = match k, v with
    | `Kfile(p), `Vfile(t) -> Dkob.valid_stored p t
    | `Ksign(x), `Vsign(y) -> Sign.valid_stored x y
    | _                    -> false

  let pp_key fmt k = match k with
    | `Kfile(p) -> Dkob.pp_key fmt p
    | `Ksign(m) -> Sign.pp_key fmt m
    | _         -> invalid_arg "No printer"

  let want : path -> key = fun p -> `Kfile(p)
end
