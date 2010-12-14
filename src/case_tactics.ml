(***********************************************************)
(* Copyright 2010 Alexandre Pilkiewicz                     *)
(*     <alexandre.pilkiewicz@polytechnique.org >           *)
(* This file is distributed under the terms of the         *)
(* GNU Lesser General Public License Version 2.1           *)
(***********************************************************)

(* the file is adapted from the Constructors plugin by Matthieu Sozeau
   https://github.com/mattam82/Constructors
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

(* getting the names of the variable from a pattern construct to add
   strings like "S n'" instead of just "S" *)

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


(* the actual tactic *)
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
  (* I don't know how to get the number of constructors of an
     inductive so I use the array of types of constructors..*)

  let types = Inductive.type_of_constructors ind mindspec in
  (* we check we have the right number of names *)
  ( match names with
  | None -> ()
  | Some a ->
      if Array.length a <> Array.length types then
        error "The intro pattern has a wrong number of cases");
  (* The array of tactics to be applied.*)
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


let letin_string id cs =
  Tactics.letin_tac None (Name id) cs (Some (!!coq_string)) nowhere

(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. There's currently no way to return a term 
   through an extended tactic, hence the use of a let binding. *)

(* the tactic that builds a coq string from a term *)
TACTIC EXTEND string_of_in
| ["string" "of" constr(c) "in" ident(id) ] -> 
    [ fun gl -> (* The current goal *)
      let s =  coqstring_of_string (string_of_constr (pf_env gl) c) in
	(* Defined the list in the context using name [id]. *)
      letin_string id s gl
    ]
END

(* tactic that runs a tac and write in "id" the name of the branch we are in *)
TACTIC EXTEND run_tac_on_ind
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




(* build the coqstring from the hypothesis *)
let hyp_name_of =
  let no_name = lazy (coqstring_of_string "NONAMEGOAL") in
  function
    | Anonymous -> !!no_name
    | Name id -> coqstring_of_string (string_of_id id)


(* build the list of names of hypothesis that will become sub goals,
   among the n first hypothesis of the type*)

let rec list_of_no_dep_names limit exclude_num x =
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
        if List.mem nth_non_dep exclude_num then tail else hyp_name :: tail

    | LetIn(_,a,_,t) -> build n nth_non_dep (subst1 a t)
    | Cast(t,_,_) -> build n nth_non_dep t
    | _ -> []
  in build limit 0 x

open Rawterm

let select_app_tac with_evars =
  if with_evars then Tactics.eapply_with_bindings else Tactics.apply_with_bindings


let build_apply' with_evars thm bl id gl =
  (* get the list of numbers of non dep hypothesis that are explicitly
     bound *)
  let rec mkexcludes = function
    | [] -> []
    | (_, AnonHyp n, _) :: l -> n :: mkexcludes l
    | _ :: l -> mkexcludes l in
  let exclude_num =
    match bl with
    | NoBindings
    | ImplicitBindings _ -> [] (* implicit bindings only concerns dep hypothesis *)
    | ExplicitBindings ebs -> mkexcludes ebs in

  let concl_nprod = nb_prod (pf_concl gl) in
  let thm_ty = Reductionops.nf_betaiota (project gl) (pf_type_of gl thm) in
  let t_nprod = nb_prod thm_ty in
  let n = t_nprod - concl_nprod in
  let lst_name = list_of_no_dep_names n exclude_num thm_ty in
  tclTHENS ((select_app_tac with_evars) (thm, bl)) (List.map (fun s -> letin_string id s) lst_name) gl

TACTIC EXTEND apply_aux
| ["apply_aux" constr_with_bindings(c) "resin" ident(id) ] ->
    [ let thm,bl = sig_it c in build_apply' false thm bl id]
END

TACTIC EXTEND eapply_aux
| ["eapply_aux" constr_with_bindings(c) "resin" ident(id) ] ->
    [ let thm,bl = sig_it c in  build_apply' true thm bl id]
END



let mk_constructor with_evars optnum id gl =
  let cl = pf_concl gl in
  let (mind,redcl) = pf_reduce_to_quantified_ind gl cl in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).Declarations.mind_consnames in
  (* list of numbers of constructors we want to try to apply *)
  let ln =
    match optnum with
    | None -> interval 1 nconstr
    | Some n ->
        if n <= 0 then error "The constructors are numbered starting from 1."
        else if n > nconstr then error "Not enough constructors."
        else
          [n] in
  let all_apply_tacs =
    tclFIRST (List.map (fun i ->
      build_apply'
        with_evars (mkConstruct (ith_constructor_of_inductive mind i))
        NoBindings id) ln) in
  (tclTHENLIST
     [convert_concl_no_check redcl DEFAULTcast; Tactics.intros; all_apply_tacs]) gl



(* for a reason I ignore, I can't have integer(..), I need to use
    int_or_var(...). I've no idea why *)

let ioa_to_int = function
  | ArgArg i -> i
  | _ -> error "You must pass an integer"

TACTIC EXTEND constructor_aux
| ["constructor_aux" int_or_var(n) "resin" ident(id) ] ->
    [ mk_constructor false (Some (ioa_to_int n)) id ]
| ["constructor_aux" "resin" ident(id) ] ->
    [ mk_constructor false None id]
END

TACTIC EXTEND econstructor_aux
| ["econstructor_aux" integer_opt(on) "resin" ident(id) ] ->
    [ mk_constructor true on id]
END



(*


  check_number_of_constructors expctdnumopt i nconstr;
  let cons = mkConstruct (ith_constructor_of_inductive mind i) in
  let apply_tac = general_apply true false with_evars (dloc,(cons,lbind)) in
  (tclTHENLIST
     [convert_concl_no_check redcl DEFAULTcast; intros; apply_tac]) gl





let check_number_of_constructors expctdnumopt i nconstr =
  if i=0 then error "The constructors are numbered starting from 1.";
  begin match expctdnumopt with
    | Some n when n <> nconstr ->
	error ("Not an inductive goal with "^
	       string_of_int n^plural n " constructor"^".")
    | _ -> ()
  end;
  if i > nconstr then error "Not enough constructors."

let constructor_tac with_evars expctdnumopt i lbind gl =
  let cl = pf_concl gl in
  let (mind,redcl) = pf_reduce_to_quantified_ind gl cl in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  check_number_of_constructors expctdnumopt i nconstr;
  let cons = mkConstruct (ith_constructor_of_inductive mind i) in
  let apply_tac = general_apply true false with_evars (dloc,(cons,lbind)) in
  (tclTHENLIST
     [convert_concl_no_check redcl DEFAULTcast; intros; apply_tac]) gl

let one_constructor i lbind = constructor_tac false None i lbind

(* Try to apply the constructor of the inductive definition followed by
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let any_constructor with_evars tacopt gl =
  let t = match tacopt with None -> tclIDTAC | Some t -> t in
  let mind = fst (pf_reduce_to_quantified_ind gl (pf_concl gl)) in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  if nconstr = 0 then error "The type has no constructors.";
  tclFIRST
    (List.map
      (fun i -> tclTHEN (constructor_tac with_evars None i NoBindings) t)
      (interval 1 nconstr)) gl
 *)
