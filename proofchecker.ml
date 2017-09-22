open List
open Printf
open Formulas
open Sequents
open Substitute

(* To run:
*  ocamlc -c formulas.mli sequents.mli substitute.mli proofchecker.mli
*  ocamlc -c formulas.ml sequents.ml substitute.ml proofchecker.ml test.ml
*  ocamlc -o proof formulas.cmo sequents.cmo substitute.cmo proofchecker.cmo test.cmo
*  ./proof  
*)
 

(* proofchecker : proof -> bool
*
*  This is the proof checker. It will go through each rule and determine
*  whether or not the proof was valid. 
*
* I will describe the rule And_IA1 in detail: 
* First, And_IA1 consists of a sequent and a proof (seq, proof).
* The sequent must have for it's first element in it's first list
* a formula consisting of "And(f1, f2)". 
* The proof must have for it's first element in it's first sequent
* the same formula as f1 (in the previous And(f1,f2)). 
* To check this, we go through a series of nested match statements. 
* First, match the seqent of And_IA1(seq, proof) with the sequent
* that is empty in the antecedent. This is clearly an invalid proof.
* Now, we look at the case where we have Sequent(head::tail, _). 
* In this case, our head must be And(f1, f2). 
* Now we look at the proof. 
* Our proof must be any rule that has for it's first sequent
* another list. We call this _(Sequent(head2::tail2,_)). 
* This head2 has to be equal to the formula f1 in the And(f1,f2)
* case described above. 
* If it is, the rule is valid. In any other case, it returns false. 
*
* Note: For rules Exists_IS/IS and Forall_IS/IA:
*
* You can rename a term string (Var "x" -> Var "a")
* or you can replace a variable with a term (Var "x" -> Const "0")
* In order to use these rules, we need the following arguments:
* Exists_IS(sequent, proof, string, oldVariable, newTerm)
* If you are replacing only the string within all terms, 
*   you must state the string to replace as string = "a" for instance
*   and you can put any placeholder terms as oldVariable and newTerm.
* If you are replacing a variable with a term, leave the string field
*   as an empty string (this signals the rule checker that we are 
*   replacing the term) and put in oldVariable and newTerm as what you
*   will replace (oldVariable) with the newTerm.
*)

let rec proofchecker p =
  (match p with 
  
(* Simple case: if axiom, then true *)
    Axiom(s) -> check_if_axiom s
    
(*  And_IA1
* 
*  proof:  A, gamma -> theta
*         --------------------
*         A&B, gamma -> theta
*
* if: "&" appears as first list element in lower sequent
*     Upper sequent keeps "A" (not "B") 
*     gamma == gamma
*     theta == theta
* then: proof check upper proof
*)
  | And_IA1(seq, proof) -> 
    (match seq with 
      Sequent([],_) -> false
    | Sequent(head::tail,theta) -> 
          if ((check_formula head = "and") &&
             ((get_antecedent_head proof) = (match_form_1 head)) &&
             (theta = get_succedent proof) &&
             (tail = get_gamma_antec proof))
          then proofchecker proof 
          else false )
(*  And_IA2
* 
*  proof:  B, gamma -> theta
*         --------------------
*         A&B, gamma -> theta
*
* if: "&" appears as first list element in lower sequent
*     Upper sequent keeps "B" (not "A") 
*     gamma == gamma
*     theta == theta
* then: proof check upper proof
*)  
  | And_IA2(seq, proof) -> 
     (match seq with 
       Sequent([],_) -> false
     | Sequent(head::tail,theta) -> 
            if ((check_formula head = "and") &&
               ((get_antecedent_head proof) = (match_form_2 head)) &&
               (theta = get_succedent proof) &&
               (tail = get_gamma_antec proof))
            then proofchecker proof
            else false)
(*  Or_IS1
* 
*  proof:  gamma -> A, theta
*         --------------------
*         gamma -> A V B, theta
*
* if: "V" appears as first list element in lower sequent
*     Upper sequent keeps "A" (not "B") 
*     gamma == gamma
*     theta == theta
* then: proof check upper proof
*) 
  | Or_IS1(seq, proof) -> 
    (match seq with 
      Sequent(_,[]) -> false
    | Sequent(gamma,head::tail) -> 
             if ((check_formula head = "or") &&
                ((get_succedent_head proof) = (match_form_1 head)) &&
                (gamma = get_antecedent proof) && 
                (tail = get_theta_succed proof))
             then proofchecker proof
             else false)
(*  Or_IS2
* 
*  proof:  gamma -> B, theta
*         --------------------
*         gamma -> A V B, theta
*
* if: "V" appears as first list element in lower sequent
*     Upper sequent keeps "B" (not "A") 
*     gamma == gamma
*     theta == theta
* then: proof check upper proof
*) 
  | Or_IS2(seq, proof) -> 
     (match seq with 
       Sequent(_,[]) -> false
     | Sequent(gamma,head::tail) -> 
            if ((check_formula head = "or") &&
              ((get_succedent_head proof) = (match_form_2 head)) &&
              (gamma = get_antecedent proof) && 
              (tail = get_theta_succed proof))
            then proofchecker proof
            else false)
(*  Or_IA
 * 
 *          A, gamma -> theta      B, gamma -> theta
 *         -----------------------------------------
 *                  A V B, gamma -> theta
 *  
 * if: "V" appears as first list element in lower sequent
 *     Upper right sequent starts with "A"
 *     Upper left sequent starts with "B"
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Or_IA(seq, proof1, proof2) ->
     (match seq with
       Sequent([],_) -> false
     | Sequent(head::tail,theta) -> 
            if ((check_formula head = "or") &&
              ((match_form_1 head) = (get_antecedent_head proof1)) && 
              ((match_form_2 head) = (get_antecedent_head proof2)) &&
              (tail = get_gamma_antec proof1) &&
              (tail = get_gamma_antec proof2) &&
              (theta = get_succedent proof1) &&
              (theta = get_succedent proof2))
            then proofchecker proof1 && proofchecker proof2
            else false)			  			
  
(*  Not_IA
 * 
 *  proof:  gamma -> A, theta
 *         --------------------
 *          ~A, gamma -> theta
 *
 * if: "~" appears as first list element in lower sequent
 *     Upper sequent has "A" in succedent 
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Not_IA(seq, proof) -> 
     (match seq with 
       Sequent([],_) -> false
     | Sequent(head::tail,theta) -> 
             if ((check_formula head = "not") &&
                ((get_succedent_head proof) = (match_form_1 head)) &&
                (theta = get_theta_succed proof) &&
                (tail = get_antecedent proof))
             then proofchecker proof
             else false)
(*  Not_IS
 * 
 *  proof:  A, gamma -> theta
 *         --------------------
 *          gamma -> ~A, theta
 *
 * if: "~" appears as first list element in lower sequent succedent
 *     Upper sequent has "A" in antecedent 
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Not_IS(seq, proof) -> 
     (match seq with 
       Sequent(_,[]) -> false
     | Sequent(gamma,head::tail) -> 
              if ((check_formula head = "not") &&
                 ((get_antecedent_head proof) = (match_form_1 head)) &&
                 (gamma = get_gamma_antec proof) &&
                 (tail = get_succedent proof))
              then proofchecker proof
              else false)

(*  Imply_IS
 * 
 *  proof:  A, gamma -> B, theta
 *         --------------------
 *          gamma -> A=>B, theta
 *
 * if: "=>" appears as first list element in lower sequent succedent
 *     Upper sequent has "A" in antecedent, "B" in succedent 
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Imply_IS(seq, proof) -> 
     (match seq with 
       Sequent(_,[]) -> false
     | Sequent(gamma,head::tail) -> 
           if ((check_formula head = "imply") &&
              ((get_antecedent_head proof) = (match_form_1 head)) &&
              ((get_succedent_head proof) = (match_form_2 head)) &&
              (gamma = get_gamma_antec proof) &&
              (tail = get_theta_succed proof))
           then proofchecker proof
           else false)
(*  Imply_IA
 * 
 *  proof:  gamma -> A, theta    B, gamma -> theta
 *         ---------------------------------------
 *                A=>B, gamma -> theta
 *
 * if: "=>" appears as first list element in lower sequent antecedent
 *     Upper sequent has "A" in succedent, "B" in antecedent 
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Imply_IA(seq, proof1, proof2) ->
     (match seq with
       Sequent([],_) -> false
     | Sequent(head::tail,theta) -> 
             if ((check_formula head = "imply") &&
               ((match_form_1 head) = (get_succedent_head proof1)) && 
               ((match_form_2 head) = (get_antecedent_head proof2)) &&
               (theta = get_theta_succed proof1) &&
               (theta = get_succedent proof2) &&
               (tail = get_antecedent proof1) &&
               (tail = get_gamma_antec proof2))
             then proofchecker proof1 && proofchecker proof2
             else false)

  			                          
(*  Thin_A
 * 
 *  proof:   gamma -> theta
 *         --------------------
 *          A, gamma -> theta
 *
 * if: head of antecedent does not appear in upper sequent
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Thin_A(seq, proof) -> 
     (match seq with 
       Sequent([],_) -> false
     | Sequent(head::tail,theta) -> 
            if (tail = (get_antecedent proof) &&
                (theta = get_succedent proof))
            then proofchecker proof
            else false)
  			
(*  Thin_S
 * 
 *  proof:   gamma -> theta
 *         --------------------
 *          gamma -> A, theta
 *
 * if: head of succedent does not appear in upper sequent
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
   | Thin_S(seq, proof) -> 
     (match seq with 
       Sequent(_,[]) -> false
     | Sequent(gamma,head::tail) -> 
               if (tail = (get_succedent proof) &&
                  (gamma = get_antecedent proof))
               then proofchecker proof
               else false)
  			
(*  Contr_A
 * 
 *  proof:   A, A, gamma -> theta
 *           --------------------
 *            A, gamma -> theta
 *
 * if: head of antecedent appears twice in upper sequent
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Contr_A(seq, proof) -> 
     (match seq with 
       Sequent([],_) -> false
     | Sequent(head::tail,_) -> 
         (match get_antecedent proof with
            [] -> false
          | head2::tail2 -> 
                  if (head = head2) && (tail2 = (head::tail))
                  then proofchecker proof
                  else false))
  			
(*  Contr_S
 * 
 *  proof:   gamma -> A,A, theta
 *           --------------------
 *             gamma -> A, theta
 *
 * if: head of succedent appears twice in upper sequent
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Contr_S(seq, proof) -> 
     (match seq with 
       Sequent(_,[]) -> false
     | Sequent(_,head::tail) -> 
         (match get_succedent proof with
            [] -> false
          | head2::tail2 -> 
                 if (head = head2) && (tail2 = (head::tail))
                 then proofchecker proof
                 else false))
  						  
(*  Interchange_A
 * 
 *  proof:    A,B, gamma -> theta
 *           --------------------
 *             B,A,gamma -> theta
 *
 * if: head of succedent appears twice in upper sequent
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Interchange_A(seq, proof) -> 
     (match seq with 
       Sequent([],_) -> false
     | Sequent(l1,theta) -> 
            if formula_list_equals l1 (get_antecedent proof)
            then proofchecker proof
            else false)
  			
(*  Interchange_S
 * 
 *  proof:   gamma -> A,B, theta
 *           --------------------
 *             gamma -> B,A, theta
 *
 * if: head of succedent appears twice in upper sequent
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Interchange_S(seq, proof) -> 
     (match seq with 
       Sequent(_,[]) -> false
     | Sequent(gamma,l1) -> 
            if (formula_list_equals l1 (get_succedent proof))
            then proofchecker proof
            else false)
  			

(*  Cut
 * 
 *  proof:  gamma -> A, theta    A, gamma -> theta
 *         ---------------------------------------
 *                  gamma -> theta
 *
 * if: Upper left sequent has "A" in succedent, upper right "A" in antecedent 
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Cut(seq, proof1, proof2) -> 
     (match seq with 
       Sequent([],_) -> false
     | Sequent(_,[]) -> false
     | Sequent(h1::tail1,h2::tail2) -> 
            if ((get_antecedent_head proof1) = h1) &&
               ((get_succedent_head proof1) = (get_antecedent_head proof2)) &&
               ((get_succedent_head proof2) = h2) 
            then (proofchecker proof1 && proofchecker proof2)
            else false)
  												

(*  Exists_IS
 * 
 *  proof:     gamma -> Fa, theta
 *             --------------------
 *             gamma -> ExFx, theta
 *
 * if: "exists" appears in head of succedent
 *     Check to see if we are replacing term or string
 *     renaming of x to a is okay/renaming of variable to term is okay
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
  | Exists_IS(seq, proof, str, oldVar, newTerm) -> 
     (match seq with
        Sequent(_,[]) -> false
      | Sequent(gamma,h::tail) -> 
              if (check_formula h = "exists")
              then if String.length str == 0
                   then ((substituteTerm h oldVar newTerm) = 
                     (get_succedent_head proof)) && 
                     (gamma = get_antecedent proof) &&
                     (tail = get_theta_succed proof) &&
                     (proofchecker proof)
                   else  
                     ((replacement (match_form_2 h) [(getBoundVar h,str)]) =
                     (get_succedent_head proof)) &&
                     (gamma = get_antecedent proof) &&
                     (tail = get_theta_succed proof) &&
                     proofchecker proof
              else false )	
                        
                	

(*  Exists_IA
 * 
 *  proof:     Fa, gamma -> theta
 *             --------------------
 *             ExFx, gamma -> theta
 *
 * if: "exists" appears in head of antecedent
 *     Check to see if we are replacing term or string
 *     renaming of x to a is okay/renaming of variable to term is okay
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
 	| Exists_IA(seq, proof, str, oldVar, newTerm) -> 
 	    (match seq with
 	      Sequent([],_) -> false
 	    | Sequent(h2::tail2,[]) -> 
 	       if (check_formula h2 = "exists") 
 	       then if String.length str == 0
 	            then ((substituteTerm h2 oldVar newTerm) =
 	                 (get_antecedent_head proof)) &&
 	                 (tail2 = get_gamma_antec proof) &&
 	    							 (proofchecker proof)
 	            else ((replacement (match_form_2 h2) [(getBoundVar h2,str)]) =
 	    							 (get_antecedent_head proof)) &&
 	    							 (tail2 = get_gamma_antec proof) &&
 	    							 (proofchecker proof)
 	    		else false 
 	    
 	    | Sequent(h1::tail1,l) -> 
 	       if (check_formula h1 = "exists") 
 	       then if String.length str == 0
 	            then (substituteTerm h1 oldVar newTerm) = 
 	                 (get_antecedent_head proof) &&
 	                 (l = get_succedent proof) &&
 	    							 (tail1 = get_gamma_antec proof) &&
 	    							 (proofchecker proof)
 	            else not(checkFormulaListVariables l str) &&
 	    						  ((replacement (match_form_2 h1) [(getBoundVar h1,str)]) =
 	    							(get_antecedent_head proof)) &&
 	    							(l = get_succedent proof) &&
 	    							(tail1 = get_gamma_antec proof) &&
 	    							(proofchecker proof)
 	    		 else false)
 	    											   
(*  Forall_IA
 * 
 *  proof:     Fa, gamma -> theta
 *             --------------------
 *             AxFx, gamma -> theta
 *
 * if: "forall" appears in head of antecedent
 *     Check to see if we are replacing term or string
 *     renaming of x to a is okay/renaming of variable to term is okay
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
 	| Forall_IA(seq, proof, str, oldVar, newTerm) -> 
 	    (match seq with
 	      Sequent([],_) -> false
 	    | Sequent(h::tail,theta) -> 
 	       if (check_formula h = "forall") 
 	       then if String.length str == 0
 	            then ((substituteTerm h oldVar newTerm) =
 	                 (get_antecedent_head proof)) &&
 	                 (theta = get_succedent proof) &&
 	                 (tail = get_gamma_antec proof) &&
 	                 (proofchecker proof)
 	            else ((replacement (match_form_2 h) [(getBoundVar h,str)]) =
 	    							 (get_antecedent_head proof)) &&
 	    							 (theta = get_succedent proof) &&
 	    							 (tail = get_gamma_antec proof) &&
 	    							 proofchecker proof
        else false)
(*  Forall_IS
 * 
 *  proof:     gamma -> Fa, theta
 *             --------------------
 *             gamma -> AxFx, theta
 *
 * if: "forall" appears in head of succedent
 *     Check to see if we are replacing term or string
 *     renaming of x to a is okay/renaming of variable to term is okay
 *     gamma == gamma
 *     theta == theta
 * then: proof check upper proof
 *)
 	| Forall_IS(seq, proof, str, oldVar, newTerm) -> 
 	    (match seq with
        Sequent(_,[]) -> false
      | Sequent([],h2::tail2) -> 
         if (check_formula h2 = "forall") 
         then if String.length str == 0
              then (substituteTerm h2 oldVar newTerm) = 
                   (get_succedent_head proof) &&
                   (tail2 = get_theta_succed proof) && 
                   proofchecker proof
              else ((replacement (match_form_2 h2) [(getBoundVar h2,str)]) =
                   (get_succedent_head proof)) &&
                   (tail2 = get_theta_succed proof) && 
                   proofchecker proof
        else false
 	               
 	               
      | Sequent(l,h2::tail2) -> 
          if (check_formula h2 = "forall") 
          then if String.length str == 0
               then (substituteTerm h2 oldVar newTerm) = 
                    (get_succedent_head proof) &&
                    (l = get_antecedent proof) &&
                    (tail2 = get_theta_succed proof) &&
                    proofchecker proof
               else not(checkFormulaListVariables l str) &&
                    ((replacement (match_form_2 h2) [(getBoundVar h2,str)]) =
                    (get_succedent_head proof)) &&
                    (l = get_antecedent proof) &&
                    (tail2 = get_theta_succed proof) &&
                    proofchecker proof
         else false)  

  | _ -> false)
  							



