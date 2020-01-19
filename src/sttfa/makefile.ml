(** Define some rule making facilites for export from STTfa. *)
open Core
open Extras
open Build.Classic
open Build_template

let mk_generators : string -> (DkTools.Mident.t -> DkTools.entry list pp) ->
  (Key.t, Value.t) generator list = fun ext entries_pp ->
  (* Format.(printf "paths [%a]@." (pp_print_list ~pp_sep:pp_print_space
   *   pp_print_string)) (Kernel.Basic.get_path ());
   * begin
   *   let md = Kernel.Basic.mk_mident "sttfa" in
   *   let s = Api.Env.Default.get_signature () in
   *   let open Kernel.Signature in
   *   import s Kernel.Basic.dloc md
   * end; *)
  let sysrule = function
    | Key.File(p) when Filename.extension p = ext ->
      let srcmd = dk_of p |> Api.Env.Default.init in
      Some(Rule.entry_printer p entries_pp srcmd)
    | _                                           -> None
  in
  let objrule = function
    | Key.File(p) when Filename.extension p = ".dko" -> Some(Rule.dko p)
    | _                                              -> None
  in
  let filrule = function
    | Key.File(p) when Filename.extension p = ".dk" -> Some(Rule.need p)
    | _                                             -> None
  in
  [sysrule; objrule; filrule]

(** A basis for sttfa makefiles. *)
module Basis =
struct
  type nonrec key = Key.t
  let key_eq = Key.eq
  let pp_key = Key.pp
  type nonrec value = Value.t
  let valid_stored = valid_stored
  let rules = []
end
