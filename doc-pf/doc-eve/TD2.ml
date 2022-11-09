type eopt =
  | E of int
  | R;;

(* EX 9*)
let rec pgcd = fun b -> fun c -> if (c < b)
                                 then pgcd (b - c) c
                                 else
                                   if (b < c)
                                   then pgcd b (c - b)
                                   else b;;


(* EX 23 *)
let rec appartient = fun l -> fun x -> match l with
                                       | [] -> false
                                       | y::s -> y = x || appartient s x;;


(* EX 24 *)
let rec annexe_min = fun l -> fun m -> match l with
                                       | [] -> E(m)
                                       | y::s -> if (y < m)
                                                 then annexe_min s y
                                                 else annexe_min s m;;

let min_ = fun l -> match l with
                   | [] -> R
                   | y::[] -> E(y)
                   | y::s -> annexe_min s y;;


(* EX 25 *)
let rec annexe_max = fun l -> fun m -> match l with
                                       | [] -> E(m)
                                       | y::s -> if (y > m)
                                                 then annexe_max s y
                                                 else annexe_max s m;;

let max_ = fun l -> match l with
                   | [] -> R
                   | y::[] -> E(y)
                   | y::s -> annexe_max s y;;


(* EX 26 *)
let rec annexe = fun l -> fun min -> fun max -> match l with
                                                | [] -> (E(min), E(max))
                                                | y::s -> if (y < min)
                                                          then annexe s y max
                                                          else
                                                            if (y > max)
                                                            then annexe s min y
                                                            else annexe s min max;;

let maxmin = fun l -> match l with
                      | [] -> (R, R)
                      | y::[] -> (E(y), E(y))
                      | y::s -> annexe s y y;;
