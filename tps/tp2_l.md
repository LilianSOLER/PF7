# TP2 : ARBRES BINAIRES


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
- Définir un type abin pour un arbre binaire d’entiers (les nœuds doivent être étiquetés, pas les
feuilles).
- Écrire une fonction qui calcule le nombre de nœuds d’un arbre binaire.
- Écrire une fonction qui calcule la hauteur d’un arbre binaire.
- Écrire une fonction qui calcule le produit de tous les éléments d’un arbre binaire.
- Écrire une fonction qui calcule la somme de tous les éléments d’un arbre binaire.
- Écrire une fonction qui détermine si un élément appartient à un arbre binaire.
- Écrire une fonction qui calcule le maximum d’un arbre binaire.
- Écrire une fonction qui calcule le nombre de nœuds “vraiment binaires” d’un arbre binaire
(autrement dit le nombre de nœuds ayant 2 fils non vides).