#load "qtparser.cmo";;
open Qtparser
                                                            (*exercice 5.1*)
let rec  rot_pos: quadtree->quadtree =fun q ->match q with |Feuille(x)->q
                                                      |Noeud(q1,q2,q3,q4)->Noeud(rot_pos(q2),rot_pos(q3),rot_pos(q4),rot_pos(q1))
(*exercice 5.2*)
let rec rot_neg: quadtree->quadtree =fun q ->match q with |Feuille(x)->q
                                                          |Noeud(q1,q2,q3,q4)->Noeud(rot_neg(q4),rot_neg(q1),rot_neg(q2),rot_neg(q3))


                                                                                    (*exercice 5.3*)
let rec miroir_hori : quadtree->quadtree =fun q -> match q with |Feuille(x)->q
                                                                |Noeud(q1,q2,q3,q4)->Noeud(miroir_hori(q4),miroir_hori(q3),miroir_hori(q2),miroir_hori(q1))

                                                                                          (*exercice 5.4*)

let rec miroir_vert : quadtree->quadtree =fun q -> match q with |Feuille(x)->q
                                                                |Noeud(q1,q2,q3,q4)->Noeud(miroir_vert(q2),miroir_vert(q1),miroir_vert(q4),miroir_vert(q3))

                                                                                          (*exercice 5.5*)
let rec inversion_video: quadtree->int->quadtree = fun q x->match q with |Feuille(y)->Feuille(x-y)
                                                                         |Noeud(q1,q2,q3,q4)->Noeud(inversion_video q1 x,inversion_video q2 x,inversion_video q3 x,inversion_video q4 x)


                                                                                                   (*exercice 5.6*)
let rec max_gris : quadtree->int =fun quadtree -> match quadtree with 
  | Feuille color -> color
  | Noeud (q1, q2, q3, q4) -> max (max (max (max_gris q1) (max_gris q2)) (max_gris q3)) (max_gris q4)

(*exercice 5.7*)
let testQuadtree : quadtree = Noeud (Noeud (Feuille 1, Feuille 2, Feuille 3, Feuille 4), Feuille 5, Feuille 6, Feuille 7);;
print_qt (testQuadtree)

let displayQuadtree = fun taille nbcoul quadtree fichier ->
  save_qt taille nbcoul quadtree fichier;
  load_qt fichier;
  print_string( "Quadtree sauvegarde dans le fichier " ^ fichier ^ " et charge depuis ce fichier");
  print_newline()
;;
displayQuadtree 2048 15 testQuadtree "testQuadtreeBase.pgm";;

let rec compare_quadtree:quadtree->quadtree->bool =fun quadtree1 quadtree2 -> match (quadtree1, quadtree2) with 
  | (Feuille color1, Feuille color2) -> if color1 = color2 then true else false
  | (Noeud (q11, q12, q13, q14), Noeud (q21, q22, q23, q24)) ->compare_quadtree q11 q21 && compare_quadtree q12 q22 && compare_quadtree q13 q23  && compare_quadtree q14 q24
