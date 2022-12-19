open Printf

(* Définitions de terme, test et programme *)
type term = 
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test = 
 | Equals of term * term
 | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string` 
   et `str_of_test : test -> string` qui convertissent des termes 
   et des tests en chaînes de caractères du format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)

let rec str_of_term t = 
  (* Cette fonction fait un match with avec le paramètre t *)
  match t with 
  (* Si t est du type const, renvoie c (en String) - terminaison*)
  | Const c -> string_of_int c
  (* Si t est du type var, e.g 5 on renvoie x5  - terminaison*)
  | Var v  ->  x v
  (* Sinon, pour add et mult on renvoie (+ t1 t2) de façon recursive car
    on peut avoir dans t1 et t2 des termes qui contiennent de termes et ainsi de suite*)
  | Add (t1, t2) -> "(+ " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
  | Mult(t1, t2) -> "(x " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
    

let rec str_of_test t = 
  (* Convertion d'un type Equals ou LessThan dans un String, en utilisant du matching et de
    la méthode récursive str_of_term*)
  match t with 
  | Equals (t1, t2) -> "(= " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^")"
  | LessThan(t1, t2) -> "(< " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"

let rec contraire t = 
  (* Convertion d'un type Equals ou LessThan dans un String, en utilisant du matching et de
    la méthode récursive str_of_term. Cette fois ici on renvoie le contraire d'égal et de lessthan, donc
    not et greater then (>=)*)
  match t with 
  | Equals (t1, t2) -> "(not (" ^ str_of_term t1 ^ " " ^ str_of_term t2 ^"))"
  | LessThan(t1, t2) -> "(>= " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
        
let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne 
   de caractères qui exprime que le tuple (t1, ..., tk) est dans 
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne 
   "(Inv x1 10)".
   *)

let create_tab_var n = 
  (* Fonction auxilaire qui récoit un entier et créer une tableau de var qui va de Var 1 à Var n *)
  let rec loop n res = 
    match n with
    | 0 -> res
    | _ -> loop (n-1) ((Var n) :: res) 
  in loop n [];;

let create_tab_const n = 
  (* Fonction auxilaire qui récoit un entier et créer une tableau de const *)
  let rec loop n res = 
    match n with
    | 0 -> res
    | _ -> loop (n-1) ((Const n) :: res)
  in loop n [];;

(* let create_tab_of_term term size = 
  match term with
  |Var x -> create_tab_var size
  |Const x -> create_tab_const size
  | _  -> failwith "not valid term" *)

let str_condition l = 
  (* Dans un premier temps, ici on va creer un tab qui contient le contenu de l
    au format termes e.g. l = [Var 1, Const 10] devient ["x1", "10"] *)
  let tab = List.map (fun x-> str_of_term x) l in
  (* Ensuite on va ajouter dans une string chaque element de tab avec de la recursion *)
  let rec loop tab res counter =
    if counter > List.length tab then
      (* si tab est fini, on renvoie la string finale *)
      res 
    else if counter = List.length tab then
      (* si c'est le dernier element on doit fermer le parenthèse *)
      res^")"
    else 
      (* sinon on continue la recursivité avec le prochain element du tableau *)
      loop tab (res^" "^(List.nth tab counter)) (counter+1) in
  (* le premier appel *)
  loop tab "(Invar" 0

(* Question 3. Écrire une fonction 
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "< x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (< x1 x2)))".  *)

let str_assert s = "(assert " ^ s ^")"

let create_variable n = 
  (* Ici, nous avons une methode auxiliaire, qui crée pour le int n
    un paremètre du type (xn Int) *)
  "(x"^string_of_int(n)^" Int)"
  
let create_variables n = 
  (* Ici on va creer l'ensemble des paramètres (x1 Int) ... (xn Int) *)
  (* Pour cela on utilise d'un fonction recursive auxiliaire loop et de la
    méthode create_variable *)
  let rec loop result counter =
    if counter > n then result
    else
    (* Appel récursive sans space au début (premier appel) *) 
    if counter = 1 then loop (result^(create_variable counter)) (counter+1)
    (* Appel récursive avec space au début *)
    else loop (result^" "^(create_variable counter)) (counter+1)
  (* Premier appel *)
  in loop "(" 1
  

let str_assert_forall n s = 
  (* Concatenation de toutes composantes d'un assert forall (create_variables) *)
  "(assert (forall "^(create_variables n) ^") "^"("^s^")))"

   
(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"
    ^str_assert_forall (p.nvars) ("\n=> (and "^str_condition(create_tab_var(p.nvars))^" "
    ^str_of_test(p.loopcond)^") "^str_condition(p.mods)) in
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^str_assert_forall (p.nvars) ("\n => (and "^str_condition(create_tab_var(p.nvars))^" "^contraire(p.loopcond)^") "^str_of_test(p.assertion)) 
  in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}


let () = Printf.printf "%s" (smtlib_of_wa p1)

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)


(* 

example du cours - page 133.
(declare-fun Invar (Int Int) Bool)
; équation (61) : la relation Invar est un invariant de boucle
(assert (forall (( x Int ) ( y Int ))
(=> (and (Invar x y) (< x 10)) (Invar (+ x 2) (+ y 1)))))
; équation (62) : la relation Invar est vraie initialement
(assert (Invar 0 1))
; équation (63) : l'assertion finale est vérifiée
(assert (forall (( x Int ) ( y Int ))
(=> (and (Invar x y) (>= x 10)) (< y 10))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)
(exit) 
*)

let p2 =  {nvars = 2;
  loopcond = LessThan ((Var 1),(Const 10));
  mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Const 1))];
  inits = [(Const 0) ; (Const 1)];
  assertion = LessThan ((Var 2),(Const 10))}

let () = Printf.printf "\n\n%s" (smtlib_of_wa p2)
