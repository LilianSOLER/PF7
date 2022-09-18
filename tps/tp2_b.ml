type abin=Nil|Cons of int*abin*abin
let abin1=Cons(10,Nil,Nil)
let abin2=Cons(15,abin1,abin1)
let abin3=Cons(20,abin1,abin2)

let rec noeud=fun a -> match a with |Nil ->0 |Cons(_,newa,newb)->noeud(newa)+noeud(newb)+1
let testnoeud=assert(noeud abin2=3)
let testnoeud2=assert(noeud abin1=1)

let rec haut=fun a->match a with |Nil ->0
                                 |Cons(_,newa,newb)->let x=haut newa in let y=haut newb in if x>=y then x+1 else y+1

let testhaut=assert(haut abin2=2)
let testhaut2=assert(haut abin3=3)

let rec produit=fun a ->match a with |Nil->1
                                     |Cons(x,newa,newb)->produit(newa)*produit(newb)*x

let testproduit=assert(produit abin1=10)
let testproduit2=assert(produit abin2=1500)

let rec somme=fun a ->match a with |Nil->0
                                   |Cons(x,newa,newb)->somme(newa)+somme(newb)+x


let testsomme=assert(somme abin1=10)
let testsomme=assert(somme abin2=35)

let rec determine=fun a e ->match a with|Nil->false
                                        |Cons(x,newa,newb)->if x=e then
                                        true else determine newa e || determine newb e

let testdeter=assert(determine abin1 10=true)
let testdeter2=assert(determine abin2 100=false)

let  max=fun l->let rec bis=fun current l->match l with |Nil->current
                                                        |Cons(x,y,l)->if current<x then bis x y else bis current y in bis min_int l

let testmax=assert(max abin1=10)
let testmax2=assert(max abin2=15)

let rec bin=fun a->match a with |Nil->0
                                |Cons(_,Nil,Nil)->0
                                |Cons(_,newa,newb)->bin(newa) + bin(newb) +1
                                |Cons(_,Nil,newb)-> bin(newb)
                                |Cons(_,newa,Nil)->bin(newa) 

let testbin=assert(bin abin1=0)
let testbin2=assert(bin abin2=1)
let testbin3=assert(bin abin3=2)


(*2.2*)
type abin=Nil|Cons of int*abin*abin
let abr=Cons(20,abr4,abr3)
let abr3=Cons(25,Nil,Nil)
let abr4=Cons(10,Nil,Nil)
                     (*2.2.1*)
let rec mem=fun a l ->match a with|Nil->false
                                  |Cons(x,newa,newb)->if x=l then true else if x>l then mem newa l else mem newb l

let testmem=assert(mem abr 20=true)
let testmen=assert(mem abr 30=false)
                  (*exerice 19 sur le tp de lilian*)

let rec verif=fun a->match a with |Nil->true
                                  |Cons(x,Nil,Nil)->true
                                  |Cons(x,_,newb)->match newb with
                                                     |Cons(y,newc,newd)->if x>y then verif newc && verif newd else false
                                                     |Cons(y,Nil,newd)->if x>y then verif newd else false
                                                     |Cons(y,newc,Nil)->if x>y then verif newc else false
                                                     |Cons(y,Nil,Nil)->if x>y then true else false
                                  |Cons(x,newa,_)->match newa with
                                                     |Cons(y,newc,newd)->if x>y then verif newc && verif newd else false
                                                     |Cons(y,Nil,newd)->if x>y then verif newd else false
                                                     |Cons(y,newc,Nil)->if x>y then verif newc else false
                                                     |Cons(y,Nil,Nil)->if x>y then true else false
