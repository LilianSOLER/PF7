(* POITEVIN Eve & REYGNER Etienne *)


(* FILES *)

(* Exercice 59 *)

type 'a file = 'a list;;

let file_vide : 'a file = [];;

let est_file_vide : ('a file -> bool) = fun f ->
  match f with
  | [] -> true
  | _ -> false;;

assert (est_file_vide file_vide);;
assert (est_file_vide [1, 2, 3] = false);;

let enfile : ('a -> 'a file -> 'a file) = fun x f -> [x] @ f ;;

let i = enfile 1 file_vide;;
let i = enfile 2 i;;

exception Pas_de_dernier;;

let rec reste_file : ('a file -> 'a file) = fun f ->
  match f with
  | [] -> raise Pas_de_dernier
  | x :: f' -> if f'=[] then f' else x::(reste_file f');;

let rec last : ('a file -> 'a) = fun f ->
  match f with
  | [] -> raise Pas_de_dernier
  | x :: [] -> x
  | x :: f' -> last f';;

last i;;

reste_file i;;

let defile : ('a file -> ('a * 'a file)) = fun f -> (last f, reste_file f);;

defile i;;

(* Exercice 60 *)

let rec enfileList = fun l f ->
	match l with
		| [] -> f
		| x::l' -> enfileList l' (enfile x f);;


let fv = file_vide;;

let l1 = 1::2::3::[];;

let r = enfileList l1 fv;;

let rec defileFile = fun f -> 
	match f with
		| [] -> []
		| x::f' -> x::(defileFile f');;

defileFile r;;

let rec renv = fun l -> match l with
                        | [] -> []
                        | x::l' -> renv l' @ (x::[]);;

let rec teste_file : ('a list -> bool) = fun l ->
  let file = enfileList l [] in let list = defileFile file in l = renv list;;

assert (teste_file l1);;

(* Exercice 61 *)

type 'a file_bis = 'a list * 'a list;;

let rec est_file_vide_bis = fun f ->
   match f with
  | ([], []) -> true
  | (_,_) -> false;;

assert (est_file_vide_bis ([], []));;

assert (est_file_vide_bis ([], [4]) = false);;

let enfile_bis : ('a -> 'a file_bis -> 'a file_bis) = fun x f -> let (l, r) = f in x::l,r;;

let fbis = enfile_bis 3 ([], []);;

let fbis2 = enfile_bis 4 fbis;;

let rec transfert : ('a list -> 'a list -> 'a list) = fun l1 l2 ->
  match l1 with
  | [] -> l2
  | x :: l' -> transfert l' (x :: l2);;

exception Impossible;;

let rec defile_bis : ('a file_bis -> ('a * 'a file_bis)) = fun f ->
  match f with
  | ([], []) -> raise Impossible
  | (_, []) -> let (lin, lout) = f in defile_bis ([], transfert lin lout)
  | lin, x :: lout' -> (x, (lin, lout'));;

defile_bis fbis;;

defile_bis fbis2;;

(* FILES À PRIORITÉ *)

(* Exercice 62 *)

type 'a fap = ('a * int) list;;

let fap_vide = [];;

let est_fap_vide : ('a fap -> bool) = fun f ->
  match f with
  | [] -> true
  | _ -> false;;

let fap1 = (2,2)::(3,1)::[];;

exception Error;;

let rec enleve_min = fun a l -> let (x, p) = a in
                                    match l with
                                    | [] -> []
                                    | u::l' -> let (x', p') = u in if x' = x && p = p' then enleve_min a l' else u::(enleve_min a l');;


let rec trouve_prio_min_bis = fun l a ->let (x, p) = a in match l with
                                    | [] -> a
                                    | fap::l' -> let (x', p') = fap in if p' < p then trouve_prio_min_bis l' fap else trouve_prio_min_bis l' a;;

let trouve_prio_min = fun l -> match l with
                          | [] -> raise Error
                          | a::l' -> let min = trouve_prio_min_bis l a in
                                    let p = enleve_min min l in (min, p);;

let rec tri_selection = fun l -> match l with
                                 | [] -> []
                                 | _ -> let (min, s) = trouve_prio_min l in min::(tri_selection s);;

let insere : ('a -> int -> 'a fap -> 'a fap) = fun x p f -> renv (tri_selection ([(x,p)] @ f));;

let fap1 = insere 7 3 fap1;;

let extrait : ('a fap -> ('a * 'a fap)) = fun f ->
  match f with
  | [] -> raise Error
  | x :: f' -> let (x', p') = x in (x', f');;

extrait fap1;;

(* Exercice 63 *)

let rec enfileList2 = fun l i f ->
	match l with
		| [] -> f
		| x::l' -> enfileList2 l' (i+1) (insere x (i+1) f);;


let fv2 = file_vide;;

let l2 = 4::2::10::[];;

let r2 = enfileList2 l2 0 fv2;;

let rec defileFile2 = fun f -> 
	match f with
		| [] -> []
		| x::f' -> let (x', p') = x in x'::(defileFile2 f');;

defileFile2 r2;;

let rec renv = fun l -> match l with
                        | [] -> []
                        | x::l' -> renv l' @ (x::[]);;

let rec teste_fap : ('a list -> bool) = fun l ->
  let file = enfileList2 l 0 [] in let list = defileFile2 file in l = renv list;;

assert (teste_fap l1);;
assert (teste_fap l2);;

(* Exercice 64 *)

type 'a abin =
  | F
  | N of 'a abin * ('a * int)  * 'a abin;;

type 'a fap_abr = 'a abin;;

let fap_abr_vide = F;;

let est_fap_abr_vide : ('a fap_abr -> bool) = fun f ->
  match f with
  | F -> true
  | N (_, _, _) -> false;;

assert (est_fap_abr_vide fap_abr_vide);;

let rec insere_fap_abr : ('a -> int -> 'a fap_abr -> 'a fap_abr) = fun x p f ->
  match f with
  | F -> N (F, (x, p), F)
  | N (g, (x', p'), d) ->
     if p < p'
     then N (insere_fap_abr x p g, (x',p'), d)
     else N (g, (x',p'), insere_fap_abr x p d);;

let f4 = insere_fap_abr 'o' 3 fap_abr_vide;;
let f4 = insere_fap_abr 'y' 9 f4;;
let f4 = insere_fap_abr 'u' 1 f4;;

exception File_vide;;
exception Error;;

let rec extrait_fap_abr : ('a fap_abr -> ('a * 'a fap_abr)) =
                                           fun f ->
                                           match f with
                                           | F -> raise File_vide
                                           | N (_, (x, _), F) -> (x, F)
                                           | N (g, (x,p), d) -> let (x', d') = extrait_fap_abr d in (x', N (g, (x, p), d'));;
                                          
extrait_fap_abr f4;;
