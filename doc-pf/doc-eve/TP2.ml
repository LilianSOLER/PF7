(* TP2 : Manipulation de listes *)
exception InventaireVide;;

(* Les demenageurs OCaml *)
(* EX 17 *)
type contenu =
  | Meuble
  | Objet
  | Cadre
  | Plante;;

type solidite =
  | Fragile
  | Robuste
  | Simple;;

type paquet = Paquet of contenu * solidite * int;;

let inventaireVide = [];;
let inventaire = [Paquet(Meuble, Robuste, 20); Paquet(Cadre, Simple, 22); Paquet(Objet, Fragile, 2); Paquet(Meuble, Simple, 10); Paquet(Plante, Fragile, 1); Paquet(Plante, Fragile, 3); Paquet(Cadre, Simple, 1)];;
let inventaireOrdonne = [Paquet(Plante, Fragile, 1); Paquet(Cadre, Simple, 1); Paquet(Cadre, Simple, 2); Paquet(Objet, Fragile, 2); Paquet(Plante, Fragile, 3); Paquet(Meuble, Simple, 10); Paquet(Meuble, Robuste, 20)];;

(* EX 18 *)
let rec fragiles = fun i -> match i with
                            | [] -> 0
                            | Paquet(c, s, p)::ls -> if (s = Fragile)
                                                     then 1 + fragiles ls
                                                     else fragiles ls;;

fragiles inventaireVide;;
fragiles inventaire;;

(* EX 19 *)
let rec legers = fun i -> fun poids -> match i with
                                    | [] -> []
                                    | Paquet(c, s, p)::ls -> if (p <= poids)
                                                             then Paquet(c, s, p)::(legers ls poids)
                                                             else legers ls poids;;

legers inventaireVide 5;;
legers inventaire 5;;

(* EX 20 *)
let rec poids_plantes = fun i -> match i with
                                 | [] -> 0
                                 | Paquet(c, s ,p)::ls -> if (c = Plante)
                                                          then p + poids_plantes ls
                                                          else poids_plantes ls;;

poids_plantes inventaireVide;;
poids_plantes inventaire;;

(* EX 21 *)
let rec exposition = fun i -> match i with
                              | [] -> []
                              | Paquet(c, s ,p)::ls -> if (c = Cadre)
                                                       then exposition ls
                                                       else Paquet(c, s ,p)::(exposition ls);;

exposition inventaireVide;;
exposition inventaire;;

(* EX 22 *)
let rec inventorie = fun i -> fun elem -> let Paquet(ce, se, pe) = elem in match i with
                                                                           | [] -> elem::[]
                                                                           | Paquet(c, s, p)::ls -> if (pe < p)
                                                                                                    then elem::i
                                                                                                    else Paquet(c, s, p)::(inventorie ls elem);;

inventorie inventaireVide (Paquet(Objet, Robuste, 5));;
inventorie inventaireOrdonne (Paquet(Objet, Robuste, 5));;

(* EX 23 *)
let rec annexe_droma = fun i -> fun max -> let Paquet(_, _, poids) = max in match i with
                                                                            | [] -> max
                                                                            | Paquet(c, s, p)::ls -> if (p > poids)
                                                                                                     then annexe_droma ls (Paquet(c, s, p))
                                                                                                     else annexe_droma ls max;;

let dromadaire = fun i -> match i with
                           | [] -> raise InventaireVide
                           | elem::ls -> annexe_droma ls elem;;

dromadaire inventaireVide;;
dromadaire inventaire;;

(* EX 24 *)
let rec annexe_chameau = fun i -> fun max1 -> fun max2 -> let Paquet(_, _, poids) = max2 in match i with
                                          | [] -> max2
                                          | Paquet(c, s, p)::ls -> if ((max1 = max2) || (p > poids && Paquet(c, s, p) <> max1))
                                                                   then annexe_chameau ls max1 (Paquet(c, s, p))
                                                                   else annexe_chameau ls max1 max2;;

let chameau = fun i -> match i with
                       | [] -> raise InventaireVide
                       | elem::ls -> let max1 = dromadaire i in
                                     let max2 = annexe_chameau i max1 elem in
                                     (max1, max2);;

chameau inventaireVide;;
chameau inventaire;;
chameau [Paquet(Meuble, Robuste, 20)];;


(* Chez Tardy *)
(* EX 25 *)
type produit =
  | LecteurMP3
  | AppareilPhoto
  | Camera
  | TelephonePortable
  | OrdinateurPortable;;

type marque =
  | Alpel
  | Syno
  | Massung
  | Liphisp;;

type appareil =
  | Appareil of produit * marque * int * int;;

let inventaireVide = [];;
let inventaire = [Appareil(LecteurMP3, Liphisp, 30, 50); Appareil(Camera, Syno, 140, 10); Appareil(TelephonePortable, Alpel, 1100, 1000); Appareil(TelephonePortable, Syno, 300, 12); Appareil(LecteurMP3, Syno, 20, 50); Appareil(AppareilPhoto, Massung, 200, 3); Appareil(TelephonePortable, Massung, 1100, 1000)];;
let inventaireUn = [Appareil(LecteurMP3, Liphisp, 30, 50)];;

(* EX 26 *)
let rec est_en_stock = fun i -> fun (elem:produit * marque * int) -> let (prod, marq, prix) = elem in
                                                                     match i with
                                                                     | [] -> false
                                                                     | Appareil(p, m, c, s)::ls -> if (prod = p && marq = m && prix = c)
                                                                                                   then s > 0
                                                                                                   else est_en_stock ls elem;;

est_en_stock inventaireVide (Camera, Liphisp, 140);;
est_en_stock inventaire (Camera, Liphisp, 140);;
est_en_stock inventaire (Camera, Syno, 140);;

(* EX 27 *)
let rec ajoute_article = fun i -> fun elem -> let Appareil(prod, marq, prix, stock) = elem in
                                              match i with
                                              | [] -> elem::[]
                                              | Appareil(p, m, c, s)::ls -> if (p = prod && m = marq && c = prix)
                                                                            then Appareil(p, m, c, s + stock)::ls
                                                                            else Appareil(p, m, c, s)::(ajoute_article ls elem);;

ajoute_article inventaireVide (Appareil(OrdinateurPortable, Alpel, 6000, 1000));;
ajoute_article inventaire (Appareil(OrdinateurPortable, Alpel, 6000, 1000));;
ajoute_article inventaire (Appareil(LecteurMP3, Syno, 20, 100));;

(* EX 28 *)
let rec enleve_article = fun i -> fun elem -> let Appareil(prod, marq, prix, stock) = elem in
                                              match i with
                                              | [] -> []
                                              | Appareil(p, m, c, s)::ls -> if (p = prod && m = marq && c = prix)
                                                                            then ls
                                                                            else Appareil(p, m, c, s)::(enleve_article ls elem);;

enleve_article inventaireVide (Appareil(OrdinateurPortable, Alpel, 6000, 1000));;
enleve_article inventaire (Appareil(OrdinateurPortable, Alpel, 6000, 1000));;
enleve_article inventaire (Appareil(TelephonePortable, Alpel, 1100, 1000));;
enleve_article inventaireUn (Appareil(LecteurMP3, Liphisp, 30, 50));;

(* Tri par selection *)
(* EX 34 *)
let rec minimum = fun i -> fun min -> let Appareil(prod, marq, prix, stock) = min in
                                      match i with
                                      | [] -> min
                                      | Appareil(p, m, c, s)::ls -> if (c < prix)
                                                                    then minimum ls (Appareil(p, m, c, s))
                                                                    else minimum ls min;;

let rec suppr_min = fun i -> fun min -> match i with
                                       | [] -> []
                                       | elem::ls -> if (elem = min)
                                                     then ls
                                                     else elem::(suppr_min ls min);;

let trouve_min = fun i -> match i with
                              | [] -> raise InventaireVide
                              | elem::ls -> let min = minimum ls elem in
                                            let l = suppr_min i min in
                                            (min, l);;

trouve_min inventaireVide;;
trouve_min inventaire;;
trouve_min inventaireUn;;

(* EX 35 *)
let rec tri_selection = fun i -> match i with
                                 | [] -> []
                                 | _ -> let (min, s) = trouve_min i in
                                        min::(tri_selection s);;

tri_selection inventaireVide;;
tri_selection inventaire;;
tri_selection inventaireUn;;
