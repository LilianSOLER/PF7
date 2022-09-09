let pi : float = atan(1.0) *. 4.0;;

let r = let x = 7 in 6 * x;;

let a = (r - 6) / 6 - 6;;

let u = let x = 9 in if (x < 9) then 9 / (x - x) else (x + x) / 9;;

let pi_sur_quatre = pi /. 4.0;;

let dans_l_ordre = 1 < 2 && 2 < 3;;

let positif = let a = 42 in if a >=0 then true else false;;

let double_absolu = let x = -2.7 in (if (x < 0.) then x else -.x) *. 2.0;;

type semaine = Lundi | Mardi | Mercredi | Jeudi | Vendredi | Samedi | Dimanche;;

type point2D = {x : float; y : float};;

let origin = {x = 0.0; y = 0.0};;

let random_point = fun max -> Random.self_init(); {x = Random.float max ; y = Random.float max};;


type segment = {p1 : point2D; p2 : point2D};;

let random_segment = {p1 = random_point 10.; p2 = random_point 20.};;
let random_segment2 = {p1 = random_point 30.; p2 = random_point 40.};;

let random_segment3 = {p1 = random_point 50.; p2 = random_point 60.};;

let random_segment4 = {p1 = random_point 70.; p2 = random_point 80.};;

type figure = segment list;; 

let random_figure = [random_segment; random_segment2; random_segment3; random_segment4];;

let distance = fun p1 p2 -> match p1, p2 with
    {x = x1; y = y1}, {x = x2; y = y2} -> sqrt((x1 -. x2) ** 2. +. (y1 -. y2) ** 2.);;

distance origin (random_point 10.);;

let perimeter = fun f -> f |> List.map (fun s -> distance s.p1 s.p2) |> List.fold_left (+.) 0.;;

perimeter random_figure;;


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

let rec length = fun l -> match l with
    | Nil -> 0
    | Cons (c, l) -> 1 + length l;;

length main;;

let rec last_carte = fun l -> match l with
    | Nil -> failwith "Liste vide"
    | Cons (c, Nil) -> c
    | Cons (c, l) -> last_carte l;;

last_carte main;;

let first_carte = fun l -> match l with
    | Nil -> failwith "Liste vide"
    | Cons (c, l) -> c;;

first_carte main;;

let cube = fun x -> x ** 3.;;
cube 2.;;

let pair = fun x -> x mod 2 = 0;;
pair 258;;
pair 259;;

let sign = fun x -> x > 0;;
sign 2;;
sign (-2);;

let sign_str = fun x -> if x > 0 then "positif" else "negatif";;
sign_str 2;;
sign_str (-2);;

let sign_part = fun x -> if x > 0 then 1 else if x < 0 then -1 else 0;;
sign_part 2;;
sign_part (-2);;
sign_part 0;;

let sum = fun x y -> x + y;;
sum 2 3;;

let sum = fun x y z -> x + y + z;;
sum 2 3 4;;

let produit = fun x y z -> x *. y *. z;;
produit 2. 3. 4.;;

let is_triplet_pythagoricien = fun a b c -> a * a + b * b = c * c || a * a + c * c = b * b || b * b + c * c = a * a;;
is_triplet_pythagoricien 3 4 5;;
is_triplet_pythagoricien 3 4 6;;
is_triplet_pythagoricien 4 3 5;;
is_triplet_pythagoricien 3 5 4;;

let is_same_sign = fun x y -> x >= 0. && y >= 0. || x < 0. && y < 0.;;
is_same_sign 2. 3.;;
is_same_sign 2. (-3.);;
is_same_sign (-2.) 3.;;
is_same_sign (-2.) (-3.);;
is_same_sign 0. 3.;;
is_same_sign 0. (-3.);;
is_same_sign 2. 0.;;
is_same_sign (-2.) 0.;;
is_same_sign 0. 0.;;

let min2 = fun x y -> if x < y then x else y;;
min2 2 3;;
min2 3 2;;

let min = fun x y z -> min2 (min2 x y) z;;
min 2 3 4;;
min 2 4 3;;
min 4 2 3;;
min 4 3 2;;
min 3 4 2;;
min 3 2 4;;

