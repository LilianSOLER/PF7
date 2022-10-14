(*Pucci Jérémy*)

(*-------------------------------------------------------------------------------------
                            Exercice 4.1 : Structure de file
---------------------------------------------------------------------------------------*)

type 'a file = 'a list;;

let file_vide: ('a file)=[];;

let est_file_vide : ('a file -> bool) = 
   fun l -> match l with
      |[]->true
      |_->false
;;

let enfile: ('a -> 'a file ->'a file)=
  fun a -> fun file ->
    match file with
      |[]->a::[]
      |t::q->a::t::q
;;

(*Pour la fonction defile, on va utiliser deux fonctions auxiliaires.
   La première pour trouver le dernier élément, la seconde pour supprimer cet element.*)

let rec last_element: ('a file -> 'a)=
  fun file -> 
    match file with
    |[]->failwith "Liste vide"
    |[x]->x
    |t::q->last_element q 
;;

let rec suppr_last_element: ('a file -> 'a file)=
  fun file -> match file with
    |[]->failwith "File vide"
    |[x]->[]
    |t::q->t::suppr_last_element q
;;

let defile : ('a file -> ('a * 'a file)) =
  fun file -> (last_element file,suppr_last_element file)
 ;; 

 (*-------------------------------------------------------------------------------------
                                  Exercice 4.2
---------------------------------------------------------------------------------------*)

let rec list_to_file: ('a list -> 'a file)=
 fun liste -> let file = file_vide in match liste with
  |[]->file
  |t::q->enfile t (list_to_file q)
;;

let rec file_to_list: ('a file -> 'a list)=
  fun fil -> match fil with
    |[]->[]
    |t::q-> let (element_defile,reste_file)=defile (fil) in element_defile::file_to_list reste_file
;; 

(* On va créer la fonction de renversement d'une liste*)

let renversement:('a list -> 'a list) = 
fun l -> let rec renv_aux:('a list -> 'a list -> 'a list) =
    fun l1 -> fun l2 -> 
      match l1 with
      |[]->l2
      |t::q->renv_aux q (t::l2)
  in renv_aux l []
;;

(* On peut maintenant tester *)

let rec teste_file : ('a list -> bool) = 
  fun liste -> file_to_list (list_to_file liste) = renversement liste
;;

let liste_test = 13::2::6::3::35::46::7::[];;
let test_file = assert (teste_file liste_test = true);;

 (*-------------------------------------------------------------------------------------
                                  Exercice 4.3
---------------------------------------------------------------------------------------*)

type 'a file_2 = 'a list* 'a list ;;

let file_vide_2 : ('a file_2) = ([],[]);;

let est_file_vide_2: ('a file_2 -> bool ) =
  fun l -> match l with
           | ([], []) -> true
           | _ -> false
;;

let enfile_2: ( 'a -> 'a file_2 -> 'a file_2) =
  fun a -> fun (file_entree,file_sortie) ->
    match file_entree with
       |[]->(a::[],file_sortie)
       |t::q->(a::t::q,file_sortie)
;;

let rec defile_2:('a file_2 -> ('a * 'a file_2)) =
  fun (file_entree,file_sortie) ->
    match file_sortie with
      |[]->defile_2([],renversement (file_entree))
      |t::q->(t,(file_entree,q))
;;

 (*-------------------------------------------------------------------------------------
                          Exercice 4.4 : File à Priorités
---------------------------------------------------------------------------------------*)

type 'a fap = ('a*int) list;;

let fap_vide : ('a fap) = [];;

let est_fap_vide: ('a fap -> bool ) =
  fun f -> match f with
           | [] -> true
           | _ -> false
;;

let rec insere: ( 'a -> int -> 'a fap -> 'a fap) = 
  fun elem -> fun prio  -> fun f ->
  match f with
    |[] -> (elem,prio)::[]
    |(t, prio_t) :: q -> if prio>prio_t then (elem,prio)::(t,prio_t)::q
                         else  (t,prio_t) :: (insere elem prio q)
;;

let rec extrait: ('a fap -> ('a*'a fap))=
  fun f -> match f with
    |[]->failwith "Fap vide"
    |(t,prio_t)::q->(t,q)
;;

(*Fonctions de test*)

let fap_test = fap_vide;;

assert (est_fap_vide fap_test = true);;

(*J'insère un élement quelconque pour verifier insere et je le rajoute 
   dans une nouvelle fap*)
let fap_test1 = insere 2 3 fap_test;;

(*J'y insere un nouvel élément, il devrait être tout devant*)
let fap_test2 = insere 10 5 fap_test1;;

(*C'est bon, on peut maintenant inserer un element de priorité plus faible*)
let fap_test3 = insere 1 1 fap_test2;;

(*Enfin, on met un element de priorité moyenne entre deux autres elements*)
let fap_test4 = insere 4 4 fap_test3;;

(*Tout est bon, on a le bon ordre, testons maintenant extrait*)

let fap_test4_defile = extrait fap_test4;;

(*C'est parfait  :)  *)

(*-------------------------------------------------------------------------------------
                                     Exercice 4.5
---------------------------------------------------------------------------------------*)

(*J'ai déjà testé dans l'exo d'avant en moins propre, c'etait pour s'echauffer pour
   cet exo ... *)

let insere_fap_vide: ('a list -> 'a fap) = fun liste -> 
    let rec insere_fap_vide_aux: ('a list -> 'a fap -> int -> 'a fap)=
      fun liste_aux -> fun f -> fun prio -> 
        match liste_aux with
          |[]-> f 
          |t::q->insere_fap_vide_aux q (insere t prio f) (prio+1)
    in insere_fap_vide_aux liste [] 0
;; 

let rec defile_fap : ( 'a fap -> 'a list) =  
  fun f -> match f with
    |[] -> []
    |t::q->let (elem, fap_2)= extrait f in elem::defile_fap q
;;

let rec teste_fap : ('a list -> bool) = 
  fun liste -> defile_fap (insere_fap_vide liste) = renversement liste ;;
 
let fap_test = assert( teste_fap liste_test = true);;

(*C'est effectivement plus propre*)