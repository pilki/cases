(***********************************************************)
(* Copyright 2010 Alexandre Pilkiewicz                     *)
(*     <alexandre.pilkiewicz@polytechnique.org >           *)
(* This file is distributed under the terms of the         *)
(* GNU Lesser General Public License Version 2.1           *)
(***********************************************************)

(* the file is adapted from the Constructors plugin by Matthieu Sozeau
   https://github.com/mattam82/Constructors

   Copyright 2010 Matthieu Sozeau <mattam@mattam.org>. All rights
   reserved.

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

let __coq_plugin_name = "Case_tactics"

(* Getting constrs (primitive Coq terms) from exisiting Coq libraries. *)

let find_constant contrib dir s =
  Globnames.printable_constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "Case_tactics"
let init_constant dir s = find_constant contrib_name dir s


(* functions to turn a caml string into a coq string, adapted from the
   parse string module *)

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

let string_of_constr ?(with_notations=true) env c =
  (* backup the current mode for printing notation *)
  let back_notation = !Constrextern.print_no_symbol in
  (* activate of remove the printing of notations *)
  Constrextern.print_no_symbol := not with_notations;
  let stream = print_constr_env env c in
  msg_with Format.str_formatter stream;
  (* change back the printing of notations *)
  Constrextern.print_no_symbol := back_notation;
  Format.flush_str_formatter ()

let coqstring_of_constr ?(with_notations=true) env c =
  coqstring_of_string (string_of_constr ~with_notations env c)

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg
open Util
(*open Rawterm*)
open Libobject
open Goptions
open Misctypes
open Errors

(* define if notation shoud be used when using case tactics *)

let use_notations = ref false

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use notations with Case tactics";
      optkey   = ["Notations"; "With"; "Case"];
      optread  = (fun () -> !use_notations);
      optwrite = ((:=) use_notations) }


(* build a continuation tactic from tactic expression (I
   think... Taken from the quote plugin )*)
(*let make_cont k x =
  let k = TacDynamic(Loc.dummy_loc, Tacinterp.tactic_in (fun _ -> fst k)) in
  let x = TacDynamic(Loc.dummy_loc, Pretyping.constr_in x) in
  let tac = <:tactic<let cont := $k in cont $x>> in
  Tacinterp.interp tac*)
let make_cont k x =
  let k = TacDynamic(Loc.dummy_loc, Tacinterp.tactic_in (fun _ -> k)) in
  let x = TacDynamic(Loc.dummy_loc, Pretyping.constr_in x) in
  let tac = <:tactic<let cont := $k in cont $x>> in
  Tacinterp.interp tac

(* A clause specifying that the [let] should not try to fold anything the goal
   matching the list of constructors (see [letin_tac] below). *)

let nowhere = { Locus.onhyps = Some [];
    	        Locus.concl_occs = Locus.NoOccurrences }

(* getting the names of the variable from a pattern construct to add
   strings like "S n'" instead of just "S" *)

let get_names_naming = function
| IntroIdentifier id -> string_of_id id
| IntroFresh id ->  "?" ^ (string_of_id id)
| IntroAnonymous -> "?"

let rec get_names_aux  (_,pat) = match pat with
| IntroForthcoming _ -> error "Forthcoming pattern not allowed"
| IntroNaming naming_pattern -> get_names_naming naming_pattern
| IntroAction action_pattern ->
  match action_pattern with
  | IntroWildcard -> "_"
  | IntroOrAndPattern [l] ->
    let l = List.map get_names_aux l in
    "(" ^ (String.concat ", "  l) ^")"
  | IntroOrAndPattern l -> error "Disjunctive patterns not allowed"
  | IntroInjection _ -> error "Injection intros not allowed"
  | IntroApplyOn _ -> error "Apply On intros not allowed"
  | IntroRewrite _ -> error "Rewritting patterns not allowed"

let get_names ((_, pat) as lpat) = match pat with
(* we accept an empty pattern for the "destruction" tactic, since it
    is needed to allow the _eqn thing *)
| IntroForthcoming _ -> error "Forthcoming pattern not allowed"
| IntroNaming naming_pattern -> Some [|get_names_naming naming_pattern|]
| IntroAction action_pattern ->
  match action_pattern with
  | IntroWildcard -> Some [| "_" |]
  | IntroOrAndPattern [[]] -> None
  | IntroOrAndPattern l ->
    let lnames =
      List.map
       (fun conj ->
         String.concat " " (List.map get_names_aux conj)) l in
    Some (Array.of_list lnames)
  | IntroInjection _ -> error "Injection intros not allowed"
  | IntroApplyOn _ -> error "Apply On intros not allowed"
  | IntroRewrite _ -> error "Rewritting patterns not allowed"


let constr_str_of_ind env ind = 
  (* Decompose the application of the inductive type to params and arguments. *)
  let ind, args =
    try Inductive.find_rectype env ind
    with Not_found -> error "Unknown inductive"
  in
  (* Find information about it (constructors, other inductives in the same block...) *)
  let mindspec = Global.lookup_inductive (fst ind) in
  let types = Inductive.type_of_constructors ind mindspec in
  Array.mapi (fun i _ ->
    let cd = mkConstruct (fst ind, succ i) in
    string_of_constr ~with_notations:(!use_notations) env cd
  ) types

(* The array of tactics to be applied.*)
let build_next_tacs names constr_str id =
  Array.mapi (fun i s ->
    let s' =
      match names with
      | None -> coqstring_of_string s
      | Some a ->
          let n = if a.(i) = "" then "" else " " ^ a.(i) in
          coqstring_of_string (s ^ n)
    in
    Tactics.letin_tac None (Name id) s' (Some (!!coq_string)) nowhere
  ) constr_str

(* the actual tactic *)
let apply_tac_leave_str env ind tac id opat =
  let constr_str = constr_str_of_ind env ind in
  let names = 
    match opat with
    | None -> None
    | Some pat ->
        get_names pat in
  (* we check we have the right number of names *)
  ( match names with
  | None -> ()
  | Some a ->
      if Array.length a <> Array.length constr_str then
        error "The intro pattern has a wrong number of cases");
  Tacticals.New.tclTHENS tac (Array.to_list (build_next_tacs names constr_str id))

let apply_tac_leave_str_lst env inds tac id = 
  let constr_str =
    Array.concat (List.map (constr_str_of_ind env) inds) in
  Tacticals.New.tclTHENS tac (Array.to_list (build_next_tacs None constr_str id))


let letin_string id cs =
  Tactics.letin_tac None (Name id) cs (Some (!!coq_string)) nowhere

(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. There's currently no way to return a term 
   through an extended tactic, hence the use of a let binding. *)

DECLARE PLUGIN "case_tactics_plugin"

(* the tactic that builds a coq string from a term *)
TACTIC EXTEND string_of_in
| ["string" "of" constr(c) "in" ident(id) ] -> 
    [ Proofview.Goal.enter (fun gl -> (* The current goal *)
      let s =  coqstring_of_constr ~with_notations:true (Proofview.Goal.env gl) c in
	(* Defined the list in the context using name [id]. *)
      letin_string id s)
    ]
END


TACTIC EXTEND string_of_in_without
| ["string" "of" constr(c) "without" "notations" "in" ident(id) ] -> 
    [ Proofview.Goal.enter (fun gl -> (* The current goal *)
      let s =  coqstring_of_constr ~with_notations:false (Proofview.Goal.env gl) c in
	(* Defined the list in the context using name [id]. *)
      letin_string id s)
    ]
END

(* tactic that runs a tac and write in "id" the name of the branch we are in *)
TACTIC EXTEND run_tac_on_ind
| ["run_tac" tactic(tac) "on" constr(ind) "in" ident(id) ] -> 
    [ Proofview.Goal.enter (fun gl -> (* The current goal *)
      apply_tac_leave_str (Proofview.Goal.env gl) ind  (Tacinterp.eval_tactic tac) id None)
    ]
| ["run_tac" tactic(tac) "on" constr(ind)
     "as" simple_intropattern(ipat) "in" ident(id) ] -> 
    [ Proofview.Goal.enter (fun gl -> (* The current goal *)
      apply_tac_leave_str (Proofview.Goal.env gl) ind (Tacinterp.eval_tactic tac) id (Some ipat))
    ]
| ["run_tac" tactic(tac) "ons" constr_list(ind) "in" ident(id) ] -> 
    [ Proofview.Goal.enter (fun gl -> (* The current goal *)
      apply_tac_leave_str_lst (Proofview.Goal.env gl) ind (Tacinterp.eval_tactic tac) id)
    ]
END

(* we want to register the "fst_case_tac" tactics, that selects which
   S*Case tactic is applied next. For that, we store it in a
   reference. We need to use de declare_object and declare_summary
   methods, so it is stored in the .vo files, and it works well with
   interactive development *)


(* this might be a bit ugly... It's a reference on the tactic that
   select the next case tactic *)
let fst_case_ref = ref None
(*let fst_case () =
  match !fst_case_ref with
  | None -> None
  | Some t -> Some (make_cont (glob_tactic t))
*)
let fst_case_obj =
  declare_object
    {( default_object "Firt Case") with
       cache_function = (fun (_,fc) -> fst_case_ref := fc);
       load_function = (fun _ (_,fc) -> fst_case_ref := fc)}

let _ = Summary.declare_summary "Firt Case"
	  { freeze_function = (fun _ -> !fst_case_ref);
	    unfreeze_function = ((:=) fst_case_ref);
	    init_function = (fun () -> fst_case_ref := None) }

let declare_fst_case t =
  if !fst_case_ref = None then
    Lib.add_anonymous_leaf (fst_case_obj (Some t))
  else
    error "The tactic has already been registered. You cannot change it."

(* Vernacular command that registers de "fstcase" tactic. To be used
   at most once *)

VERNAC COMMAND EXTEND RegisterFstCase
  [ "Register" "First" "Case" tactic(t) ] ->
    [ declare_fst_case t ]
END


(* we now move to the (e)apply' tactics *)

(* which apply tactic should be used *)
let select_app_tac with_evars =
  if with_evars then
    Tactics.eapply_with_bindings
  else
    Tactics.apply_with_bindings


(* build the coqstring from the hypothesis *)
let hyp_name_of =
  let no_name = lazy (coqstring_of_string "NONAMEGOAL") in
  function
    | Anonymous -> !!no_name
    | Name id -> coqstring_of_string (string_of_id id)


(* build the list of names of hypothesis that will become sub goals,
   among the n first hypothesis of the type*)

let rec list_of_no_dep_names concl_nprod exclude_num thmy =
  let rec build n nth_non_dep c =
    if n = 0 then [] else
    match kind_of_term c with
    | Prod(na, _, t2) ->
        let dep = dependent (mkRel 1) t2 in
        (* I *think* that an argument becomes a subgoal when it the
           rest is not dependent on it *)
        if dep then build (pred n) nth_non_dep t2 else
        let hyp_name = hyp_name_of na in
        let tail = build (pred n) (succ nth_non_dep) t2 in

        (* if the dependent hypothesis is explicitly bound, no subgoal
           will be created for it *)
        if List.mem nth_non_dep exclude_num then
          tail
        else
          hyp_name :: tail

    | LetIn(_,a,_,t) -> build n nth_non_dep (Vars.subst1 a t)
    | Cast(t,_,_) -> build n nth_non_dep t
    | _ -> []
  in
  let limit = nb_prod thmy - concl_nprod in
  if limit <= 0 then None else Some (build limit 0 thmy)
