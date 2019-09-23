open Extras
module B = Basic

exception IllFormedUri of string

(** A uri of the form [protocol:path/name.extension]. *)
type t =
  { protocol : string
  ; path : string list
  ; name : string
  ; extension : string }

let to_string : t -> string = fun {protocol; path; name; extension} ->
  protocol ^ ":" ^ String.concat "/" path ^ "/" ^ name ^ "." ^ extension

let of_string s =
  let r_prot = Str.regexp "^[^:]+:" in
  let r_ext = Str.regexp "[\\.]+$" in
  let r_path = Str.regexp ":.*/" in
  let r_nm = Str.regexp "/[^\\.]+" in
  let wrap i = if i <= 0 then raise (IllFormedUri s) in
  let protocol =
    wrap @@ Str.search_forward r_prot s 0;
    Str.matched_string s
  in
  let extension =
    wrap @@ Str.search_forward r_ext s 0;
    Str.matched_string s
  in
  let name =
    wrap @@ Str.search_forward r_nm s 0;
    (* Drop the first element *)
    String.drop (Str.matched_string s) 0
  in
  let path =
    wrap @@ Str.search_forward r_path s 0;
    let r_sep = Str.regexp "/" in
    let nocolon = String.drop (Str.matched_string s) 0 in
    Str.split r_sep nocolon
  in
  {protocol; path; name; extension}

let name_of_uri {path; name; _} =
  B.mk_name (B.mk_mident @@ String.concat "." path) (B.mk_ident name)

let uri_of_dkid : B.mident -> B.ident -> string -> string -> t =
  fun md id th tx ->
  { protocol = th ; path = [B.string_of_mident md]
  ; name = B.string_of_ident id ; extension = tx}

let ext_of_uri : t -> string = fun u -> u.extension
