open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  let transitions = nfa.delta in 
  List.fold_left (fun acc x -> let (startState, char, endState) = x in   
    if (elem startState qs) && (char = s) && (not (elem endState acc)) then (insert endState acc) else acc)
    [] transitions


let rec e_closure_helper nfa startStates endStates = 
  match startStates with 
  | [] -> endStates 
  | h::t -> if (elem h endStates) then (e_closure_helper nfa t endStates) (*if possible state is already in the list then make recursive call with next elem in list*)
    else e_closure_helper nfa (union t (move nfa [h] None)) (insert h endStates)

(* use move but the symbol is epsilon*)  
let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  e_closure_helper nfa qs [] 

let rec accept_helper nfa charList currState  =
  match charList with
  |[] -> currState
  |h::t -> accept_helper nfa t (e_closure nfa (move nfa currState (Some h)))

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let accept = accept_helper nfa (explode s) (e_closure nfa [nfa.q0]) in
  if intersection accept nfa.fs = [] then false else true

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  fold_left (fun acc x -> insert (e_closure nfa (move nfa qs (Some x))) acc) [] nfa.sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  fold_left (fun acc x -> insert (qs, Some x, (e_closure nfa (move nfa qs (Some x)))) acc) [] nfa.sigma

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  fold_left (fun acc x -> if (elem x qs) == true then [qs] else acc) [] nfa.fs

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t = 
    match work with 
    |[] -> dfa (*Done*)
    |h::t -> 
      let newStates = new_states nfa h in
      let finalStates = union dfa.fs (new_finals nfa h) in
      let transitions = union dfa.delta (new_trans nfa h) in                                                            
      nfa_to_dfa_step nfa{sigma = nfa.sigma; qs = dfa.qs@newStates; q0 = dfa.q0; fs = finalStates; delta = transitions} (t@(diff newStates dfa.qs))

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let dfa = nfa_to_dfa_step nfa{sigma = nfa.sigma; qs = [e_closure nfa [nfa.q0]]; q0 = (e_closure nfa [nfa.q0]); fs = []; delta =[]} [e_closure nfa [nfa.q0]] in
  let newStates = fold_left (fun acc x -> if (length x) = 0 then acc else x::acc) [] dfa.qs in
  let finalStates = fold_left (fun acc x -> union acc (new_finals nfa x)) [] dfa.qs in 
  let transitions = (fold_left (fun acc x -> match x with 
    |(start, char, ends) -> if ends = [] then acc else union [x] acc) [] dfa.delta)
  in {sigma = nfa.sigma; qs= newStates; q0 = dfa.q0; fs = finalStates; delta = transitions}
