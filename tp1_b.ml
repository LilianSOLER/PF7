;; This buffer is for text that is not saved, and for Lisp evaluation.
                                                      ;; To create a file, visit it with C-x C-f and enter text in its buffer.
let r = let x= 7 in 6 * x
let a = (r - 6)/6-6
let o=r*r-x*x-51
let u=let x=9 in if (x<9)then 9/(x-x) else (x+x)/9
                                                   (*exercice 2*)
let pi_sur_4=3.14/.4.(*fallait mettre un . sur l'operation*)
let dans_l_ordre = 1<2&&2<3(*mettre un and entre 2 op bool*)
let positif=let a=42 in if a>=0 then true else false(*donner toute condition*)
let double_absolu=let x= -2.7 in (if(x<0.) then x else -.x)*.2.(*mettre des points pour faire des floats après op et chiffre*)
                                                               (*exercice 3*)
type semaine=Lundi |Mardi |Mercredi|Jeudi|Vendredi|Samedi|Dimanche
type figure=Carre of float|Rectangle of float*float|Cercle of float

 type couleur = Rouge | Vert | Bleu | Jaune;;
type nombre = Zero | Un | Deux | Trois | Quatre | Cinq | Six | Sept | Huit | Neuf;;
type couleur_nombre = {couleur : couleur; nombre : nombre};;
type piocher_carte = Deux | Quatre;;
type special = Piocher of piocher_carte | Inverser | Passer;;
type carte = Special of special | Couleur_nombre of couleur_nombre;;
type list_carte = Nil | Cons of carte * list_carte;;                                                                                    (*exercice 4 *)

let carte1 = Couleur_nombre {couleur = Rouge; nombre = Zero};;
let carte2 = Couleur_nombre {couleur = Vert; nombre = Un};;
let carte3 = Couleur_nombre {couleur = Bleu; nombre = Deux};;
let carte4 = Couleur_nombre {couleur = Jaune; nombre = Trois};;
let carte5 = Couleur_nombre {couleur = Rouge; nombre = Quatre};;
let carte6 = Special (Piocher Quatre);;
let carte7 = Special (Inverser);;
let carte8 = Special (Passer);;

let main = Cons (carte1, Cons (carte2, Cons (carte3, Cons (carte4, Cons (carte5, Cons (carte6, Cons (carte7, Cons (carte8, Nil))))))));;

let rec length = fun l -> match l with
    | Nil -> 0
    | Cons (c, l) -> 1 + length l;;

length main;;s

let rec last_carte = fun l -> match l with
    | Nil -> failwith "Liste vide"
    | Cons (c, Nil) -> c
    | Cons (c, l) -> last_carte l;;

last_carte main;;

let first_carte = fun l -> match l with
    | Nil -> failwith "Liste vide"
    | Cons (c, l) -> c;;

first_carte main;;
                                                                                     (*exercice 5*)
let cube=fun a-> a*.a*.a
let positif=fun a->if(a>0)then true else false
let rec pair=fun a->if a=2 then true else if a<2 then false else pair(a/2)
let pair=fun x ->x mod 2=0
let signe=fun x->if x>0 then +1 else if x<0 then -1 else 0
                                                           (*exercice 6*)
let produit3=fun x->fun y->fun z->x*y*z
let somme3=fun x->fun y->fun z->x+y+z
                                      (*exercice 7*)
let pytha=fun x y z->x**2.+.y**2.=z**2. ||x**2.+.z**2.=y**2. ||z**2.+.y**2.=x**2.
let memesigne= fun x y->if x<0 &&y<0 then true else if x>0&&y>0 then true else if x=0 && y=0 then true else false
                                                                                                              (*exercice 9*)
let min2entiers=fun x y ->if x-y>0 then y else x

                                                 (*exercice 10*)
let min3entiers=fun x y z->if min2entiers(x y)>z then z else min2entiers(x y)

                                                                        (*exercice 11*)
type point2D={x:float;y:float}
type segment={p1:point2D;p2:point2D}(*p1 inférieur à p2*)


let milieu = fun seg -> {x = ((seg.p1.x +. seg.p2.x) /. 2.); y = ((seg.p1.y +. seg.p2.y) /. 2.)};;

let segment = let p1 : point2D = {x = 1.; y = 2.} in let p2 : point2D = {x = 21.; y = 12.} in let seg : segment = {p1 = p1; p2 = p2} in seg

                                                                                                                                          (*let appartientsegment=fun p3 seg ->let p3:point2D1={x1=1.;y1=1.} in  if p3.x>seg.p1.x &&  p3.x<seg.p2.x && p3.y>seg.p1.y &&  p3.y<seg.p2.y then true else false*)

                                                                                                                                          (*exercice 12*)

let testsemaine=fun jour->match jour with |Lundi ->false |Mardi->false |Mercredi ->false |Jeudi ->false |Vendredi-> false |Samedi -> true |Dimanche ->true

                                                                                                                                                        (*exercice 13*)
let aire =fun fig->match fig with |Carre(a)->a*.a|Rectangle(lg,la)->lg*.la|Cercle(a)->3.14*.a*.a

                                                                                                (*exercice 14 :*)

type couleur = Rouge | Vert | Bleu | Jaune;;
type nombre = Zero | Un | Deux | Trois | Quatre | Cinq | Six | Sept | Huit | Neuf;;
type couleur_nombre = {couleur : couleur; nombre : nombre};;
type piocher_carte = Deux | Quatre;;
type special = Piocher of piocher_carte | Inverser | Passer;;
type carte = Special of special | Couleur_nombre of couleur_nombre;;
type list_carte = Nil | Cons of carte * list_carte;;


let carte1 = Couleur_nombre {couleur = Rouge; nombre = Zero};;
let carte2 = Couleur_nombre {couleur = Vert; nombre = Un};;
let carte3 = Couleur_nombre {couleur = Bleu; nombre = Deux};;
let carte4 = Couleur_nombre {couleur = Jaune; nombre = Trois};;
let carte5 = Couleur_nombre {couleur = Rouge; nombre = Quatre};;
let carte6 = Special (Piocher Quatre);;
let carte7 = Special (Inverser);;
let carte8 = Special (Passer);;

let main = Cons (carte1, Cons (carte2, Cons (carte3, Cons (carte4, Cons (carte5, Cons (carte6, Cons (carte7, Cons (carte8, Nil))))))));;
    let carteprem =fun l->match l with |Nill->0 |Cons(c,l)->c

    let projoueurjouer =fun l -> match l with |Nill->0  |Cons(c,l)->match c with |Special ->True |False

    let cartejouerapres =fun c x -> 
let rec length = fun l -> match l with
    | Nil -> 0
    | Cons (c, l) -> 1 + length l;;

length main;;s

let rec last_carte = fun l -> match l with
    | Nil -> failwith "Liste vide"
    | Cons (c, Nil) -> c
    | Cons (c, l) -> last_carte l;;

last_carte main;;

let first_carte = fun l -> match l with
    | Nil -> failwith "Liste vide"
    | Cons (c, l) -> c;;

first_carte main;;

                                                                                                (*exercice 15*)
