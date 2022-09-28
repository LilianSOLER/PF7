# TP2 : ARBRES BINAIRES - Benjamin Bracquier + Lilian Soler


Il est demandé, pour ce TP et ceux qui vendront ensuite, de faire suivre chaque définition de fonction
par un ou plusieurs tests significatifs.
À cet effet, employez des appels sur le modèle assert expr = résultat attendu comme dans
l’exemple suivant.
```ocaml
let affine a b = fun x y -> a*x + b*y
let aff21 = affine 2 1
let _ = assert (aff21 3 4 = 10)
```


## 2.1 Fonctions simples sur un arbre
- **Définir un type abin** pour un arbre binaire d’entiers (les nœuds doivent être étiquetés, pas les
feuilles).

    ```ocaml 
    type abin = Nil | Cons of abin * int * abin;; (* Nil ou fils_gauche * valeur * fils_droite *) 
    ```

- Écrire une fonction qui calcule le **nombre de nœuds** d’un arbre binaire.
  
    ```ocaml
    let rec nombre_noeuds = fun abin -> match abin with 
      | Nil -> 0 
      | Cons(a1, x, a2) -> 1 + nombre_noeuds a1 + nombre_noeuds a2;; (*1 + la somme des noeuds de ses fils *)
  ```

- Écrire une fonction qui calcule la **hauteur** d’un arbre binaire.

    ```ocaml
    let rec hauteur_arbre = fun abin -> match abin with 
      | Nil -> 0 (* hauteur d'un arbre vide *)
      | Cons(a1, x, a2) -> 1 + max (hauteur_arbre a1) (hauteur_arbre a2);; (* 1 + la hauteur du plus grand fils *)
    ```

- Écrire une fonction qui calcule le **produit** de tous les éléments d’un arbre binaire.

    ```ocaml
    let rec produit_arbre = fun abin -> match abin with 
      | Nil -> 1 (* neutre de la multiplication *)
      | Cons(a1, x, a2) -> produit_arbre a1 * x * produit_arbre a2;; (* produit des fils * valeur du noeud *)
    ```

- Écrire une fonction qui calcule la **somme** de tous les éléments d’un arbre binaire.

    ```ocaml
    let rec somme_arbre = fun abin -> match abin with 
      | Nil -> 0 (* neutre de l'addition *)
      | Cons(a1, x, a2) -> somme_arbre a1 + x + somme_arbre a2;; (* somme des fils + valeur du noeud *)
    ```

- Écrire une fonction qui détermine si un élément **appartient à un arbre binaire**.

    ```ocaml
    let rec is_in_arbre = fun abin e -> match abin with 
      | Nil -> false (* l'arbre est vide, l'élément n'y est pas *)
      | Cons(a1, x, a2) -> (e = x) || is_in_arbre a1 e || is_in_arbre a2 e;; (* l'élément est dans le noeud ou dans l'un de ses fils *)
    ```

- Écrire une fonction qui calcule le **maximum** d’un arbre binaire.

    ```ocaml
    let rec max_arbre = fun abin -> match abin with
      | Nil -> min_int (* le plus petit entier possible *)
      | Cons(a1, x, a2) -> max (max x (max_arbre a1)) (max_arbre a2);; (* le plus grand des fils ou la valeur du noeud courant *)
    ```

- Écrire une fonction qui calcule le **nombre de nœuds “vraiment binaires”** d’un arbre binaire
(autrement dit le nombre de nœuds ayant 2 fils non vides).

    ```ocaml
    let rec nombre_noeuds_really_binary = fun abin -> match abin with
      | Nil -> 0 (* l'arbre est vide, il n'y a pas de noeuds *)
      | Cons(Nil, x, Nil) -> 0 (* le noeud n'a pas de fils *)
      | Cons(Nil, x, a2) -> nombre_noeuds_really_binary a2 (* le noeud n'a pas de fils gauche donc on cherche que dans le fils droit *)
      | Cons(a1, x, Nil) -> nombre_noeuds_really_binary a1  (* le noeud n'a pas de fils droit donc on cherche que dans le fils gauche *)
      | Cons(a1, x, a2) -> 1 +  nombre_noeuds_really_binary a1 + nombre_noeuds_really_binary a2;; (* le noeud a deux fils donc on cherche dans les deux et ce noeud est completement binaire *)
    ```

## 2.2 Arbres Binaires de Recherche

Un Arbre Binaire de Recherche (en abrégé ABR) est un
arbre étiqueté tel que pour tout nœud N :
- les étiquettes de tous les nœuds du sous-arbre
gauche de N sont strictement inférieures à l’étiquette de N ;
- et les étiquettes de tous les nœuds du sous-arbre
droit de N sont strictement supérieures à l’étiquette de N.

Pour définir un tel objet en OCaml, on peut se contenter du type d’arbre binaire ordinaire abin cidessus. En effet, ce n’est pas le type mais les fonctions de manipulation qui assureront que l’objet
construit reste bien un ABR.

### ***Exercice 17** -  Construire (à la main) un (petit) exemple d’ABR en OCaml en utilisant ce type.

```ocaml
let feuille = fun x -> Cons(Nil, x, Nil);;  (* fonction qui crée une feuille *)

(* exemple d'arbre binaire de recherche *)
let abr0 = feuille 1;;
let abr1 = Cons(abr0, 3, feuille 2);;
let abr2 = Cons(abr1, 4, feuille 5);;
let abr3 = Cons(feuille 7, 8, feuille 9);;
let abr4 = Cons(abr3, 10, feuille 11)
let abr5 = Cons(abr2, 6, abr4);;
```
## 2.2.1 Fonctions de manipulation

### **Exercice 18** -  Écrire la fonction **mem** qui recherche si un entier donné **appartient** à un ABR donné. Il s’agit ici de profiter des caractéristiques de l’ABR pour ne pas effectuer une recherche exhaustive.

```ocaml
let rec mem = fun abr e -> match abr with 
  | Nil -> false (* l'arbre est vide, l'élément n'y est pas *)
  | Cons(a1, x, a2) -> if x = e then true else if x < e then mem a2 e else mem a1 e;; (* si l'élément est dans le noeud, on le retourne, sinon on regarde dans le sous arbre gauche ou droit en utilisant les propriétés des arbres binaire de recherche *)
```

### **Exercice 19** - Écrire la fonction **insert** qui insère un entier donné dans un ABR donné, à une place appropriée pour conserver la propriété d’ABR. Là encore, les caractéristiques de cette structure doivent vous aider à trouver cette place facilement.
```ocaml
let rec insert = fun abin e -> match abin with 
  | Nil -> feuille e (* l'arbre est vide, on retourne une feuille avec l'élément *)
  | Cons(a1, x, a2) -> if x < e then Cons(a1, x, insert a2 e) else Cons(insert a1 e, x, a2);; (* si l'élément est plus grand que le noeud courant, on insère dans le sous arbre droit, sinon dans le sous arbre gauche *)
```
### **Exercice 20** - Écrire une fonction **verif** qui vérifie si un arbre donné est bien un arbre binaire de recherche.

```ocaml
let rec verif_abr = fun abin -> match abin with 
  | Nil -> true (* l'arbre est vide, il est donc un arbre binaire de recherche *)
  | Cons(Nil, x, Nil) -> true (* le noeud n'a pas de fils, il est donc un arbre binaire de recherche *)
  | Cons(Nil, x, Cons(a1, y, a2)) -> if x < y then verif_abr (Cons(a1, y, a2)) else false (* le noeud n'a pas de fils gauche, on vérifie que le fils droit est bien un arbre binaire de recherche *)
  | Cons(Cons(a1, y, a2), x, Nil) -> if x > y then verif_abr (Cons(a1, y, a2)) else false (* le noeud n'a pas de fils droit, on vérifie que le fils gauche est bien un arbre binaire de recherche *)
  | Cons(Cons(a1, y, a2), x, Cons(a3, z, a4)) -> if x > y && x < z then verif_abr (Cons(a1, y, a2)) && verif_abr (Cons(a3, z, a4)) else false;; (* le noeud a deux fils, on vérifie que les deux fils sont bien des arbres binaires de recherche *)
```

## 2.2.2 Utilisation pour le tri

### **Exercice 21** -  Écrire une fonction **triABR** qui prend en argument une liste, et renvoie la liste constituée des mêmes éléments en ordre croissant, à l’aide des étapes suivantes : 
-  insérer chacun des éléments de la liste dans un ABR ;
- parcourir l’ABR de façon à récupérer les éléments en ordre croissant.
Vous êtes encouragés à décomposer cet exercice en plusieurs fonctions.

```ocaml
let triAbr = fun list -> 
  let rec triAbr_aux = fun list abin -> match list with 
    | Nil_int -> abin (* la liste est vide, on retourne l'arbre *)
    | Cons_int(x, list) -> triAbr_aux list (insert abin x) (* on insère x à l'arbre*) in 
  triAbr_aux list Nil;;  (* on appelle la fonction auxiliaire avec une liste et un arbre vide puis l'arbre courant *)

  let abr_to_list = fun abin -> 
    let rec abr_to_list_aux = fun abin list -> match abin with 
      | Nil -> list (* l'arbre est vide, on retourne la liste *)
      | Cons(a1, x, a2) -> abr_to_list_aux a1 (Cons_int(x, abr_to_list_aux a2 list)) in  abr_to_list_aux abin Nil_int;; (* on parcourt l'arbre en profondeur, on ajoute les éléments dans la liste *)

```

### **Bonus** - Pour faire nos test, nous avons trouvé utile de pouvoir afficher un abre. Écrire une fonction **display_tree** qui affiche un ABR donné.

```ocaml
let display_tree = fun abin ->
  let rec display_tree_aux = fun abin tab -> match abin with 
    | Nil -> () (* l'arbre est vide, on ne fait rien *)
    | Cons(a1, x, a2) -> display_tree_aux a2 (tab ^ "   ");print_string (tab ^ string_of_int x ^ "  "); print_newline(); display_tree_aux a1 (tab ^ "   ") in 
  display_tree_aux abin "";;
```
- La sortie de la fonction est la suivante :

    ```ocaml
    display_tree abin;;
              11  
      10  
            9  
          8  
                8  
            7  
    6  
          5  
      4  
            2  
          3  
            1  
    ```
# ***Question*** : 
   - On sent que la fonction qui affiche l'abre peut être améliorée en prenant en compte la largeur de l'arbre pour l'affichage (pour l'instant, on a un décalage fixe de 3 espaces). Comment faire ?
  
  - De plus, l'arbre est affiché de facon horizontale (on peut le voir sur la sortie de la fonction). Comment faire pour l'afficher de facon verticale ? (idée : matrice et transposition)
