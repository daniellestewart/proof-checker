open Formulas

(* type definitions: sequents and proofs *)

type seq = Sequent of (formula list*formula list)

type proof = 
    Axiom of (seq) 
  | And_IS of (seq*proof*proof)
  | And_IA1 of (seq*proof)
  | And_IA2 of (seq*proof)
  | Or_IS1 of (seq*proof)
  | Or_IS2 of (seq*proof)
  | Or_IA of (seq*proof*proof)
  | Not_IA of (seq* proof)
  | Not_IS of (seq*proof)
  | Imply_IS of (seq*proof)
  | Imply_IA of (seq*proof*proof)
  | Exists_IS of (seq*proof*string*term*term)
  | Exists_IA of (seq*proof*string*term*term)
  | Forall_IS of (seq*proof*string*term*term)
  | Forall_IA of (seq*proof*string*term*term)
  | Thin_S of (seq*proof)
  | Thin_A of (seq*proof)
  | Contr_A of (seq*proof)
  | Contr_S of(seq*proof)
  | Interchange_A of (seq*proof)
  | Interchange_S of (seq*proof)
  | Cut of (seq*proof*proof)
	     
(* check_if_axiom : sequent -> bool
*  
*  This will check to see if we have an axoim. 
*  The axiom is one sequent. That sequent must have the same
*  atom on each side (or in each list).
*  Since we use the thin rule, we can assume it's an axiom only if the
*  first formula in the lists are equal. (The tail of the list is empty.) 
*  
*  Case 1: The antecedent is empty, return false
*  Case 2: The succedent is empty, return false
*  Case 3: Both antecedent and succedent are empty, return true
*  Case 4: Compare the head of each list and see if these are equal formulae. *)
let check_if_axiom s = 
  (match s with
    Sequent([], t1::tail1) -> false
  | Sequent(t2::tail2,[]) -> false
  | Sequent([],[]) -> true
  | Sequent(h1::tail1, h2::tail2) -> h1 = h2 )

 



 (* get_antecedent_head : proof -> formula
 * 
 * get_antededent_head will take in a proof and return a formula.
 * The proof is always of the form ProofType(Sequent(h1::tail1, h2::tail2),...)
 * We wish to capture the first formula in the antededent (h1).
 *)
 let get_antecedent_head p = 
   (match p with
   Axiom(Sequent(h::tail,_)) 
 | And_IS(Sequent(h::tail,_),_,_) 
 | And_IA1(Sequent(h::tail,_),_) 
 | And_IA2(Sequent(h::tail,_),_)
 | Or_IS1(Sequent(h::tail,_),_)
 | Or_IS2(Sequent(h::tail,_),_)
 | Or_IA(Sequent(h::tail,_),_,_)
 | Not_IA(Sequent(h::tail,_),_)
 | Not_IS(Sequent(h::tail,_),_)
 | Imply_IA(Sequent(h::tail,_),_,_)
 | Imply_IS(Sequent(h::tail,_),_)
 | Exists_IS(Sequent(h::tail,_),_,_,_,_)
 | Exists_IA(Sequent(h::tail,_),_,_,_,_)
 | Forall_IS(Sequent(h::tail,_),_,_,_,_)
 | Forall_IA(Sequent(h::tail,_),_,_,_,_)
 | Thin_S(Sequent(h::tail,_),_)
 | Thin_A(Sequent(h::tail,_),_)
 | Contr_A(Sequent(h::tail,_),_)
 | Contr_S(Sequent(h::tail,_),_)
 | Interchange_A(Sequent(h::tail,_),_)
 | Interchange_S(Sequent(h::tail,_),_)
 | Cut(Sequent(h::tail,_),_,_) -> h
 | _ -> Error("Unsuccessful get_antecedent_head"))  
 
 (* get_succedent_head : proof -> formula
 * 
 * get_succedent_head will take in a proof and return a formula.
 * The proof is always of the form ProofType(Sequent(h1::tail1, h2::tail2),...)
 * We wish to capture the first formula in the succedent (h2).
 *)
 let get_succedent_head p = 
   (match p with
   Axiom(Sequent(_,h::tail))
 | And_IS(Sequent(_,h::tail),_,_)
 | And_IA1(Sequent(_,h::tail),_)
 | And_IA2(Sequent(_,h::tail),_)
 | Or_IS1(Sequent(_,h::tail),_)
 | Or_IS2(Sequent(_,h::tail),_)
 | Or_IA(Sequent(_,h::tail),_,_)
 | Not_IA(Sequent(_,h::tail),_)
 | Not_IS(Sequent(_,h::tail),_)
 | Imply_IA(Sequent(_,h::tail),_,_)
 | Imply_IS(Sequent(_,h::tail),_)
 | Exists_IS(Sequent(_,h::tail),_,_,_,_)
 | Exists_IA(Sequent(_,h::tail),_,_,_,_)
 | Forall_IS(Sequent(_,h::tail),_,_,_,_)
 | Forall_IA(Sequent(_,h::tail),_,_,_,_)
 | Thin_S(Sequent(_,h::tail),_)
 | Thin_A(Sequent(_,h::tail),_)
 | Contr_A(Sequent(_,h::tail),_)
 | Contr_S(Sequent(_,h::tail),_)
 | Interchange_A(Sequent(_,h::tail),_)
 | Interchange_S(Sequent(_,h::tail),_)
 | Cut(Sequent(_,h::tail),_,_) -> h 
 | _ -> Error("Unsuccessful get_succedent_head")) 
 
 (* get_antecedent : proof -> formula list
 *
 * get_antecedent will take in a proof and return the list of formulas that 
 * make up the antecedent.  *)
  let get_antecedent p = 
   (match p with
   Axiom(Sequent(l,_)) 
 | And_IS(Sequent(l,_),_,_) 
 | And_IA1(Sequent(l,_),_) 
 | And_IA2(Sequent(l,_),_)
 | Or_IS1(Sequent(l,_),_)
 | Or_IS2(Sequent(l,_),_)
 | Or_IA(Sequent(l,_),_,_)
 | Not_IA(Sequent(l,_),_)
 | Not_IS(Sequent(l,_),_)
 | Imply_IA(Sequent(l,_),_,_)
 | Imply_IS(Sequent(l,_),_)
 | Exists_IS(Sequent(l,_),_,_,_,_)
 | Exists_IA(Sequent(l,_),_,_,_,_)
 | Forall_IS(Sequent(l,_),_,_,_,_)
 | Forall_IA(Sequent(l,_),_,_,_,_)
 | Thin_S(Sequent(l,_),_)
 | Thin_A(Sequent(l,_),_)
 | Contr_A(Sequent(l,_),_)
 | Contr_S(Sequent(l,_),_)
 | Interchange_A(Sequent(l,_),_)
 | Interchange_S(Sequent(l,_),_)
 | Cut(Sequent(l,_),_,_) -> l)   


 (* get_succedent : proof -> formula list
 * 
 * get_succedent will take in a proof and return the list of formulas that 
 * make up the succedent.  *) 
 let get_succedent p = 
   (match p with
   Axiom(Sequent(_,l))
 | And_IS(Sequent(_,l),_,_)
 | And_IA1(Sequent(_,l),_)
 | And_IA2(Sequent(_,l),_)
 | Or_IS1(Sequent(_,l),_)
 | Or_IS2(Sequent(_,l),_)
 | Or_IA(Sequent(_,l),_,_)
 | Not_IA(Sequent(_,l),_)
 | Not_IS(Sequent(_,l),_)
 | Imply_IA(Sequent(_,l),_,_)
 | Imply_IS(Sequent(_,l),_)
 | Exists_IS(Sequent(_,l),_,_,_,_)
 | Exists_IA(Sequent(_,l),_,_,_,_)
 | Forall_IS(Sequent(_,l),_,_,_,_)
 | Forall_IA(Sequent(_,l),_,_,_,_)
 | Thin_S(Sequent(_,l),_)
 | Thin_A(Sequent(_,l),_)
 | Contr_A(Sequent(_,l),_)
 | Contr_S(Sequent(_,l),_)
 | Interchange_A(Sequent(_,l),_)
 | Interchange_S(Sequent(_,l),_)
 | Cut(Sequent(_,l),_,_) -> l ) 
 

 (* get_gamma_antec : proof -> list of formula
 * 
 * get_gamma_antec will take in a proof and return a list formula.
 * The proof is always of the form ProofType(Sequent(h1::tail1, h2::tail2),...)
 * We wish to capture the tail in the antededent (tail1).
 *)
 let get_gamma_antec p = 
   (match p with
   Axiom(Sequent(h::tail,_)) 
 | And_IS(Sequent(h::tail,_),_,_) 
 | And_IA1(Sequent(h::tail,_),_) 
 | And_IA2(Sequent(h::tail,_),_)
 | Or_IS1(Sequent(h::tail,_),_)
 | Or_IS2(Sequent(h::tail,_),_)
 | Or_IA(Sequent(h::tail,_),_,_)
 | Not_IA(Sequent(h::tail,_),_)
 | Not_IS(Sequent(h::tail,_),_)
 | Imply_IA(Sequent(h::tail,_),_,_)
 | Imply_IS(Sequent(h::tail,_),_)
 | Exists_IS(Sequent(h::tail,_),_,_,_,_)
 | Exists_IA(Sequent(h::tail,_),_,_,_,_)
 | Forall_IS(Sequent(h::tail,_),_,_,_,_)
 | Forall_IA(Sequent(h::tail,_),_,_,_,_)
 | Thin_S(Sequent(h::tail,_),_)
 | Thin_A(Sequent(h::tail,_),_)
 | Contr_A(Sequent(h::tail,_),_)
 | Contr_S(Sequent(h::tail,_),_)
 | Interchange_A(Sequent(h::tail,_),_)
 | Interchange_S(Sequent(h::tail,_),_)
 | Cut(Sequent(h::tail,_),_,_) -> tail
 | _ -> [Error("Unsuccessful get_gamma_antec")]) 

 (* get_theta_succed : proof -> formula
 * 
 * get_theta_succed will take in a proof and return a list of formulae.
 * The proof is always of the form ProofType(Sequent(h1::tail1, h2::tail2),...)
 * We wish to capture the tail in the succedent (tail2).
 *)
 let get_theta_succed p = 
   (match p with
   Axiom(Sequent(_,h::tail))
 | And_IS(Sequent(_,h::tail),_,_)
 | And_IA1(Sequent(_,h::tail),_)
 | And_IA2(Sequent(_,h::tail),_)
 | Or_IS1(Sequent(_,h::tail),_)
 | Or_IS2(Sequent(_,h::tail),_)
 | Or_IA(Sequent(_,h::tail),_,_)
 | Not_IA(Sequent(_,h::tail),_)
 | Not_IS(Sequent(_,h::tail),_)
 | Imply_IA(Sequent(_,h::tail),_,_)
 | Imply_IS(Sequent(_,h::tail),_)
 | Exists_IS(Sequent(_,h::tail),_,_,_,_)
 | Exists_IA(Sequent(_,h::tail),_,_,_,_)
 | Forall_IS(Sequent(_,h::tail),_,_,_,_)
 | Forall_IA(Sequent(_,h::tail),_,_,_,_)
 | Thin_S(Sequent(_,h::tail),_)
 | Thin_A(Sequent(_,h::tail),_)
 | Contr_A(Sequent(_,h::tail),_)
 | Contr_S(Sequent(_,h::tail),_)
 | Interchange_A(Sequent(_,h::tail),_)
 | Interchange_S(Sequent(_,h::tail),_)
 | Cut(Sequent(_,h::tail),_,_) -> tail 
 | _ -> [Error("Unsuccessful get_theta_succed")]) 



