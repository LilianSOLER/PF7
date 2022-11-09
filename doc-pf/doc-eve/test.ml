(* Exercice 3 *)

type semaine = Lundi | Mardi | Mercredi | Jeudi | Vendredi | Samedi | Dimanche

type point2D = {x: float; y: float}

let id = {x=0.0; y=0.0}

type segment = {a: point2D; b: point2D}

type figure = Carre of float | Rectangle of float*float | Cercle of float

(*Les figures sont défnies par leurs côtés/rayon*)

(* Exercice 4 *)

type couleur = Jaune | Bleu | Rouge | Vert

type carte = {color: couleur; number: int}

(* Exercice 5 *)

let cube = fun x -> x**3.

let positif = fun x -> x>0

let pair = fun x -> x mod 2 == 0

let signe = fun x -> match x with
                     | 0 -> 0
                     | c -> if c>0 then 1 else -1

(* Exercice 6 *)

let f1 = fun x -> fun y -> fun z -> x * y * z

let f2  = fun x -> fun y -> fun z -> x + y + z

(* Exercice 7 *)

let triplet = fun a -> fun b -> fun c -> (a*a)+(b*b) == (c*c)

let samesign = fun x -> fun y -> x*y > 0

(* Exercice 9 *)

let min2entiers = fun x -> fun y -> if (x<y) then x else y

(* Exercice 10 *)

let min3entiers x y z = if (min2entiers x y) == x then (min2entiers x z) else (min2entiers y z)

(* Exercice 11 *)

let milieuseg seg = {x=(seg.a.x+.seg.b.x)/.2.; y=(seg.a.y+.seg.b.y)/.2.}
