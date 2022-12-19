           Mini-projet 2 : Synthèse d'invariant en SMT-LIB
                            fichier RENDU
                     (à remplir obligatoirement)

**Un mini-projet sans fichier RENDU rempli ne recevra pas de note.**

Date limite: 19 décembre 2022

Identité
--------
Nombre de binôme: Binôme 11      
Nom, prénom 1: MOLLO CHRISTONDIS, FELIPE PARIS     
Nom, prénom 2: POSTOLACHI, MARIN       


Questions sur votre code
------------------------

## Exercice 2 

0. Avez-vous testé que `make invariants` s'exécute sans erreurs ou
   warnings, puis que `./invariants` produit une sortie au format
   SMT-LIB, et enfin que cette sortie est acceptée par Z3 ?

**Réponse:**      
La commande `make invariants` et la commande `./invariants` s'exécutent sans erreur. La sortie est accepté.

```
paris@paris-pc:~/Documents/UniversiteParis/L3/Projects/lo5-projet-2022$ make
ocamlfind ocamlopt -o invariants -linkpkg invariants.ml
paris@paris-pc:~/Documents/UniversiteParis/L3/Projects/lo5-projet-2022$ ./invariants 
; synthèse d'invariant de programme
; on déclare le symbole non interprété de relation Invar
(declare-fun Invar (Int Int ) Bool)
; la relation Invar est un invariant de boucle
(assert (forall ((x1 Int) (x2 Int)) (
=> (and (Invar x1 x2) (< x1 3)) (Invar (+ x1 1) (+ x2 3)))))
; la relation Invar est vraie initialement
(assert (Invar 0 0))
; l'assertion finale est vérifiée
(assert (forall ((x1 Int) (x2 Int)) (
 => (and (Invar x1 x2) (>= x1 3)) (= x2 9))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)
(exit)


; synthèse d'invariant de programme
; on déclare le symbole non interprété de relation Invar
(declare-fun Invar (Int Int ) Bool)
; la relation Invar est un invariant de boucle
(assert (forall ((x1 Int) (x2 Int)) (
=> (and (Invar x1 x2) (< x1 10)) (Invar (+ x1 2) (+ x2 1)))))
; la relation Invar est vraie initialement
(assert (Invar 0 1))
; l'assertion finale est vérifiée
(assert (forall ((x1 Int) (x2 Int)) (
 => (and (Invar x1 x2) (>= x1 10)) (< x2 10))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)
(exit)
```
Sortie du code sur Z3:

```
sat
(
  (define-fun Invar ((x!0 Int) (x!1 Int)) Bool
    (or (and (<= 0 x!0)
             (<= 1 x!0)
             (<= 2 x!0)
             (<= 3 x!0)
             (not (= x!1 10))
             (not (= x!1 7))
             (not (= x!1 3))
             (not (= x!1 (- 3)))
             (not (= x!1 8))
             (not (= x!1 11))
             (not (= x!1 0))
             (not (= x!1 (- 2)))
             (not (= x!1 1))
             (not (= x!1 2))
             (not (= x!1 5))
             (not (= x!1 6))
             (not (= x!1 (- 1)))
             (not (= x!1 4))
             (= x!1 9))
        (and (<= 0 x!0)
             (<= 1 x!0)
             (<= 2 x!0)
             (not (<= 3 x!0))
             (not (= x!1 10))
             (not (= x!1 7))
             (not (= x!1 3))
             (not (= x!1 (- 3)))
             (not (= x!1 8))
             (not (= x!1 11))
             (not (= x!1 0))
             (not (= x!1 (- 2)))
             (not (= x!1 1))
             (not (= x!1 2))
             (not (= x!1 5))
             (= x!1 6))
        (and (<= 0 x!0)
             (<= 1 x!0)
             (not (<= 2 x!0))
             (not (= x!1 10))
             (not (= x!1 7))
             (= x!1 3))
        (and (<= 0 x!0)
             (not (<= 1 x!0))
             (not (= x!1 10))
             (not (= x!1 7))
             (not (= x!1 3))
             (not (= x!1 (- 3)))
             (not (= x!1 8))
             (not (= x!1 11))
             (= x!1 0))))
)
```

---

1. Le type `term` est un type récursif: quel type de fonction est-il
   naturel d'utiliser? Quels sont vos cas de base et quelle quantité
   strictement décroissante au cours des appels successifs vous assure
   la terminaison?
   
**Réponse:** 

Comme défini dans le fichier `invariants.ml`, le type `term` a quatre définitions possibles. Deux d'entre eux étant des définitions récursives (Add, et Mult) car ils contiennent des "termes" dans leurs définition, tandis que `Var` et `Const` ne sont composés que d'un int. Donc, pour la fonction `str_of_term` nous avons utilisé d'un `match with` cela nous a permis de faire un appel récursive pour les termes du type `Add` et `Mult` et ensuite d'assurer la terminaison avec les types `Var` et `Const`.


```ocaml
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

```

---

2. Pour l'implémentation de `str_condition`, quelles sont les
   fonctions auxiliaires que vous avez utilisées et/ou écrites ? (Par
   une fonction auxiliaire, on entend ici soit une fonction d'une
   bibliothèque, par exemple des fonctions comme `List.length` ou
   `List.rev_append`, ou une fonction `aux_str_condition` que vous
   avez écrite vous-mêmes.) Expliquez en quelques phrases en français
   comment ces fonctions auxiliaires sont utilisées dans votre
   implémentation de la fonction `str_condition`.
   
**Réponse:**      
Pour l'implémentation de `str_condition` nous avons utilisé les fonctions auxiliaires suivantes: 

1) `List.map`: Pour convertir chaque élément du tableau l, nous appliquons une méthode `str_of_term` à chaque élément avec la méthode `List.map` et le stockons dans une variable pour ensuite être analysé.
2) `rec loop`: Nous avons écrit une méthode récursive auxiliaire, qui doit parcourir le tableau `tab`,  résultat du point 1). Cette fonction sera responsable pour concaténer les éléments du tableau `tab` dans une seule string.
3) Dans la méthode auxiliaire `loop` nous avons utilisé de la méthode `List.length` et `List.nth` pour respectivement, savoir la taille du tableau et pour retrouver un élément dans tableau, tout cela utilisé dans la création de la string.

---

3. Pour l'implémentation de `str_assert_forall`, quelles sont les
   fonctions auxiliaires que vous avez utilisées et/ou écrites ?
   Expliquez en quelques phrases en français comment ces fonctions
   auxiliaires sont utilisées dans votre implémentation de la fonction
   `str_assert_forall`.

**Réponse:**

1) `create_variable n`: Cette méthode renvoie une string du format `(xn Int)` pour un `n` donné.
2) `create_variables n`: Pour un ensemble de paramètres de taille `n`, cette méthode renvoie une string avec toutes les paramètres, e.g `(x1 Int) . . . (xn Int)`. Cette méthode utilise de la méthode auxilaire `create_variable`
3) `str_assert_forall n s`: Finalise le processus avec la concaténation de `assert`, `forall`, les paramètres (`create_variables n`) et finalement de la string `s`.
  
   
---

4. Le langage de programmation WA suppose que les mises à jour des
   variables `x1`, ..., `xk` sont simultanées : par exemple, si `x1`
   vaut `1` et x2 vaut `1`, exécuter

   x1 = x2 + 1;
   x2 = x1 + 1;

   résulte en `x1` valant `2` et `x2` valant `2`. En Java, les mises à
   jour sont séquentielles et le résultat serait que `x1` vaudrait `2`
   et `x2` vaudrait `3`. Expliquez en français comment modifier le
   code pour construite un programme SMT-LIB plus proche de la façon
   dont les variables sont mises à jour en Java.

**Réponse:**

L'utilisation de variables auxiliaires, chargées de stocker les valeurs intermédiaires de la variable
x1 et x2 pourraient permettre au programme de fonctionner d'une manière similaire à celle de Java.

---


