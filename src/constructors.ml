(***********************************************************)
(* Copyright 2010 Matthieu Sozeau <mattam@mattam.org>      *)
(* This file is distributed under the terms of the         *)
(* GNU Lesser General Public License Version 2.1           *)
(***********************************************************)

(** Constructors - An example plugin and tactic for Coq

    This defines a tactic [constructors of c in id] that puts
    the list of constructors of the inductive type [c] in the 
    (fresh) hypothesis [id]. We build a [list dynamic] where 
    [dyn] is defined in a support file of the plugin
    (in theories/Dynamic.v) and is isomorphic to a sigma type.
*)

(* These are necessary for grammar extensions like the one at the end 
   of the module *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $$ *)

open Term
open Names
open Coqlib
open Termops
open Pp

(* Getting constrs (primitive Coq terms) from exisiting Coq libraries. *)

let find_constant contrib dir s =
  Libnames.constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "constructors"
let init_constant dir s = find_constant contrib_name dir s

let constructors_path = ["Constructors";"Dynamic"]

(* We use lazy as the Coq library is not yet loaded when we
   initialize the plugin, once [Constructors.Dynamic] is loaded 
   in the interpreter this will resolve correctly. *)

let coq_dynamic_ind = lazy (init_constant constructors_path "dyn")
let coq_dynamic_constr = lazy (init_constant constructors_path "mkDyn")
let coq_dynamic_type = lazy (init_constant constructors_path "dyn_type")
let coq_dynamic_obj = lazy (init_constant constructors_path "dyn_value")

(* Reflect the constructor of [dyn] values *)

let mkDyn ty value = 
  mkApp (Lazy.force coq_dynamic_constr, [| ty ; value |])

(* We also need lists from the standard library. *)

let list_path = ["Coq";"Init";"Datatypes"]
let coq_list_ind = lazy (init_constant list_path "list")
let coq_list_nil = lazy (init_constant list_path "nil")
let coq_list_cons = lazy (init_constant list_path "cons")

(* Now the real tactic. *)

let constructors env c =
  (* Decompose the application of the inductive type to params and arguments. *)
  let ind, args = Inductive.find_rectype env c in
  (* Find information about it (constructors, other inductives in the same block...) *)
  let mindspec = Global.lookup_inductive ind in
  (* The [list dyn] term *)
  let listty = mkApp (Lazy.force coq_list_ind, [| Lazy.force coq_dynamic_ind |]) in
  let listval =
    (* We fold on the constructors and build a [dyn] object for each one. *)
    Util.array_fold_right_i (fun i v l -> 
      (* Constructors are just referenced using the inductive type
	 and constructor number (starting at 1). *)
      let cd = mkConstruct (ind, succ i) in
      let d = mkDyn v cd in
	(* Cons the constructor on the list *)
	mkApp (Lazy.force coq_list_cons, [| Lazy.force coq_dynamic_ind; d; l |]))
      (* An array of types for the constructors, with parameters abstracted too. *)
      (Inductive.type_of_constructors ind mindspec)
      (* Our init is just the empty list *)
      (mkApp (Lazy.force coq_list_nil, [| Lazy.force coq_dynamic_ind |]))
  in listval, listty

(* below, functions to turn a caml string into a coq string, adapted
   from the parse string module *)

let ascii_module = ["Coq";"Strings";"Ascii"]
let coq_Ascii = lazy (init_constant ascii_module "Ascii")

let init_module = ["Coq";"Init";"Datatypes"]
let coq_true = lazy (init_constant init_module "true")
let coq_false = lazy (init_constant init_module "false")

let string_module = ["Coq";"Strings";"String"]

let coq_string = lazy (init_constant string_module "string")
let coq_String = lazy (init_constant string_module "String")
let coq_EmptyString = lazy (init_constant string_module "EmptyString")


let (!!) = Lazy.force

let ascii_of_int p =
  let rec aux n p =
     if n = 0 then [] else
     let mp = p mod 2 in
     (if mp = 0 then !!coq_false else !!coq_true)
     :: (aux (n-1) (p/2)) in
  mkApp (Lazy.force coq_Ascii, Array.of_list (aux 8 p))


let coqstring_of_string s =
  let le = String.length s in
  let rec aux n =
     if n = le then !!coq_EmptyString else
     mkApp 
       ((!!coq_String),
        [| ascii_of_int (int_of_char s.[n]); aux (n+1)|])
  in aux 0

let string_of_constr env c =
  let stream = print_constr_env env c in
  msg_with Format.str_formatter stream;
  Format.flush_str_formatter ()

let coqstring_of_constr env c =
  coqstring_of_string (string_of_constr env c)

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg
open Util

(* A clause specifying that the [let] should not try to fold anything the goal
   matching the list of constructors (see [letin_tac] below). *)

let nowhere = { onhyps = Some []; concl_occs = Rawterm.no_occurrences_expr }


let rec get_names_aux (_,pat) = match pat with
  | IntroWildcard -> "_"
  | IntroAnonymous -> "?"
  | IntroForthcoming _ ->
      error "Forthcoming pattern not allowed"
  | IntroFresh id ->
      "?" ^ (string_of_id id)
  | IntroRewrite _->
      error "Rewriting pattern not allowed"
  | IntroOrAndPattern [l] ->
      let l = List.map get_names_aux l in
      "(" ^ (String.concat ", "  l) ^")"
  | IntroOrAndPattern l ->
      error "Disjunctive patterns not allowed"
  | IntroIdentifier id ->
      string_of_id id

let get_names ((_, pat) as lpat) = match pat with
(* we accept an empty pattern for the "destruction" tactic, since it
    is needed to allow the _eqn thing *)

| IntroOrAndPattern [[]] -> None
| IntroOrAndPattern l ->
    let lnames =
      List.map
       (fun conj ->
         String.concat " " (List.map get_names_aux conj)) l in
    Some (Array.of_list lnames)
| _ -> Some [| get_names_aux lpat|]


let apply_tac_leave_str env ind tac id opat =
  let names = 
    match opat with
    | None -> None
    | Some pat ->
        get_names pat in
(* Decompose the application of the inductive type to params and arguments. *)
  let ind, args =
    try Inductive.find_rectype env ind
    with Not_found -> error "Unknown inductive"
  in
  (* Find information about it (constructors, other inductives in the same block...) *)
  let mindspec = Global.lookup_inductive ind in
  (* The array of tactics to be applied. I don't know how to get the
     number of constructors of an inductive *)
  let types = Inductive.type_of_constructors ind mindspec in
 ( match names with
  | None -> ()
  | Some a ->
      if Array.length a <> Array.length types then
        error "The intro pattern has a wrong number of cases");
  let next_tacs =
    Array.mapi (fun i _ ->
      let cd = mkConstruct (ind, succ i) in
      let s =  string_of_constr env cd in
      let s' =
        match names with
        | None -> coqstring_of_string s
        | Some a ->
            let n = if a.(i) = "" then "" else " " ^ a.(i) in
            coqstring_of_string (s ^ n)
      in
      Tactics.letin_tac None (Name id) s' (Some (!!coq_string)) nowhere
      ) types in
  tclTHENSV tac next_tacs







(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. There's currently no way to return a term 
   through an extended tactic, hence the use of a let binding. *)

TACTIC EXTEND constructors_of_in
| ["constructors" "of" constr(c) "in" ident(id) ] -> 
    [ fun gl -> (* The current goal *)
      let v, t = constructors (pf_env gl) c in
	(* Defined the list in the context using name [id]. *)
	Tactics.letin_tac None (Name id) v (Some t) nowhere gl
    ]
END

TACTIC EXTEND string_of_in
| ["string" "of" constr(c) "in" ident(id) ] -> 
    [ fun gl -> (* The current goal *)
      let s =  coqstring_of_string (string_of_constr (pf_env gl) c) in
	(* Defined the list in the context using name [id]. *)
	Tactics.letin_tac None (Name id) s (Some (!!coq_string)) nowhere gl
    ]
END

TACTIC EXTEND apply_to_ind
| ["run_tac" tactic(tac) "on" constr(ind) "in" ident(id) ] -> 
    [ fun gl -> (* The current goal *)
      apply_tac_leave_str (pf_env gl) ind (snd tac) id None gl
    ]
| ["run_tac" tactic(tac) "on" constr(ind)
     "as" simple_intropattern(ipat) "in" ident(id) ] -> 
    [ fun gl -> (* The current goal *)
      apply_tac_leave_str (pf_env gl) ind (snd tac) id (Some ipat) gl
    ]
END
