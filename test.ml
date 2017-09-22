open Printf
open List
open Formulas
open Sequents
open Substitute
open Proofchecker

  
 let fx = Atom("f",[Var "p"; Const "z"; Var "x"]);;
 let theta = [("y","z");("x","w")];;
 


 let fn = Fn("f",[Var "y"; Const "x"; Var "w"; Const "y"]);;
 let orXY = Or(Atom("x",[]), Atom("y",[]));;
 let andXXY = And(Atom("x",[]), orXY);;
 
 let th = [("x","p")];; 

 



let atomA = Atom("A",[]);;
let atomB = Atom("B",[]);;
let atomC = Atom("C",[]);;
let andAB = 	And(Atom("A",[]), Atom("B",[]));;	
let orAB = Or(Atom("A",[]), Atom("B",[]));;	
let notA = Not(Atom("A",[]));;
let implyAA = Imply(Atom("A",[]), Atom("A",[]));;
let sequent0 = Sequent([atomA;atomA],[atomA]);;
let sequent1 = Sequent([andAB; atomC],[atomA]);;
let sequent2 = Sequent([atomC;atomA],[atomA]);;
let sequent3 = Sequent([atomA],[atomA]);;
let sequent4 = Sequent([atomB],[atomB]);;
let sequent5 = Sequent([andAB],[atomB]);;
let sequent6 = Sequent([atomA],[orAB]);;
let sequent7 = Sequent([atomB],[orAB]);;
let sequent8 = Sequent([notA; atomA],[]);;
let sequent9 = Sequent([],[notA; atomA]);;
let sequent10 = Sequent([],[implyAA]);;
let sequent11 = Sequent([atomA; atomA],[atomA]);;
let sequent12 = Sequent([atomA],[atomA; atomB]);;
let sequent13 = Sequent([atomA],[atomB; atomA]);;
let sequent14 = Sequent([atomB; atomA],[atomA]);;
let sequent15 = Sequent([Imply(atomA,atomB);atomA],[atomA]);;
let sequent16 = Sequent([atomA],[atomA;atomB]);;
let sequent17 = Sequent([atomA],[atomA;atomB;atomC]);;
let sequent18 = Sequent([atomB],[atomA;atomB;atomC]);;
let sequent19 = Sequent([atomB],[atomB;atomC]);;
let sequent20 = Sequent([atomB],[atomC;atomB]);;
let sequent21 = Sequent([atomA],[atomA;atomB;atomB]);;
let sequent22 = Sequent([atomA],[atomB;atomA;atomB]);;
let sequent23 = Sequent([atomA],[atomB;atomB;atomA]);;

(* axiom_A: 
 

  ------- Axiom
   A -> A           

*)

let axiom_A = Axiom(sequent3);;

(*  thin_A: 

    ------- Axiom
     A -> A
   ---------- Thin_A
    C, A -> A
*)




let thin_A = Thin_A(sequent2, axiom_A);;

(*  and_IA1: 


       A -> A
      --------- Thin_A
      A, C -> A
   --------------  And_IA1
    A&B, C -> A
*)

let and_IA1 = And_IA1(sequent1, thin_A);;

(* axiom_B: 
 

  ------- Axiom
   B -> B           

*)

let axiom_B = Axiom(sequent4);;

(* and_IA2: 
 
      --------- 
       B -> B
   --------------  And_IA2
      A&B -> B          

*)

let and_IA2 = And_IA2(sequent5, axiom_B);;

(* and_IA2_False: 

     ------- Axiom
      A -> A
    ---------- Thin_A
     A, C -> A
   --------------  And_IA1
    A&B, C -> A         

*)


let and_IA2_False = And_IA2(sequent1, thin_A);;	

(* or_IS1: 

    ---------- 
       A -> A
   --------------  Or_IS1
      A -> AVB         

*)

let or_IS1 = Or_IS1(sequent6, axiom_A);;

(* or_IS1_False: 

       A -> A
      --------- Thin_A
      A,C -> A
   --------------  And_IA1
    A&B, C -> A
   --------------  Or_IS1
      A -> AVB         

*)

let or_IS1_False = Or_IS1(sequent6, thin_A);;

(* or_IS2: 

    ---------- 
       B -> B
   --------------  Or_IS2
      B -> AVB         

*)

let or_IS2 = Or_IS2(sequent7, axiom_B);;

(* not_IA: 

    ---------- 
       A -> A
   --------------  Not_IA
      ~A, A ->          

*)

let not_IA = Not_IA(sequent8, axiom_A);;

(* not_IA_False: 

      --------- 
       B -> B
   --------------  Not_IA
      ~A, A ->          

*)

let not_IA_False = Not_IA(sequent8, axiom_B);;

(* not_IS: 

     --------- 
      A -> A
   --------------  Not_IS
       -> ~A, A         

*)

let not_IS = Not_IS(sequent9, axiom_A);;

(* imply_IS: 

     --------- 
      A -> A
   --------------  Imply_IS
       -> A => A         

*)

let imply_IS = Imply_IS(sequent10, axiom_A);;

(* thin_A2: 

      --------- 
       A -> A
   --------------  Thin_A
      B, A -> A          

*)

let thin_A2 = Thin_A(sequent14, axiom_A);;

(* thin_S: 

      --------- 
       A -> A
   --------------  Thin_S
      A -> B, A          

*)

let thin_S = Thin_S(sequent13, axiom_A);;

(* contraction: 

       A -> A
     ---------- Thin_A
      A,A -> A
   --------------  Contr_A
      A -> A          

*)

let contraction = Contr_A(sequent3, Thin_A(sequent0, axiom_A));;

(* interchange_S: 

      --------- 
       A -> A
   --------------  Thin_S
      A -> B, A 
   --------------  Interchange_S
      A -> A, B         

*)

let interchange_S = Interchange_S(sequent16, thin_S);;

(* proofs used in cut (left):

thin_S_a1

    A -> A
   ------------ Thin_S
   A -> B, A 
   
thin_S_a2

   A -> B, A                   
   ------------ Thin_S       
   A -> B, B, A 

interchange_S2

   A -> B, B, A              
   ------------ IterchS      
   A -> B, A, B 
   

   
*)

let thin_S_a1 = Thin_S(sequent13, axiom_A);;
let thin_S_a2 = Thin_S(sequent23, thin_S_a1);;
let interchange_S2 = Interchange_A(sequent22, thin_S_a2);;

(*
proofs used in cut (right)

thin_S_b1 

     B -> B
   ------------ Thin_S
    B -> C, B
    
interchange_S3 

   B -> C, B
  -------------  InterchS
   B -> B, C
   
thin_Sb 

      B -> B, C
    -------------- Thin_S
     B -> A, B, C


 *)
 
let axiomB = Axiom(sequent4);;
let thin_S_b1 = Thin_S(sequent20, axiomB);;
let interchange_S3 = Interchange_S(sequent19, thin_S_b1);;
let thin_Sb = Thin_S(sequent18, interchange_S3);;


(* cut: 

    
      A -> A                   B -> B
   ------------ Thin_S       ------------ Thin_S
    A -> B, A                   B -> C, B
   ------------ Thin_S      -------------  InterchS
    A -> B, B, A               B -> B, C
   ------------ InterchS     -------------- Thin_S
    A -> B, A, B              B -> A, B, C 
   ----------------------------------------  Cut
             A -> A, B, C         

*)

let cut = Cut(sequent17, interchange_S2, thin_Sb);;

 (*
 Proof existIS:
 
   Fa -> Fa
 -------------- E-IS, "a"
   Fa -> ExFx
 *)
 let atomFa = Atom("f",[Const "a"]);;
 let atomFx = Atom("f",[Var "x"]);;
 let v1 = Const "a" 
 let v2 = Var "x"
 let axiomfa = Axiom(Sequent([atomFa], [atomFa]));;
 let existsX = Exists("x",atomFx);;
 let seq = Sequent([atomFa],[existsX]);;
 let str = "";;
 let existIS = Exists_IS(seq, axiomfa,str,v1,v2);;

 (*
 Proof exists_ia:
 
      ------
      A -> A
    ------------  Thin-S
      A -> Fb,A
   --------------   Thin-A
    Fa,A -> Fb,A
  -------------------- E-IA,"a"
    ExFx, A -> Fb, A  
 
  *)
 

 let v1 = Const "a" 
 let v2 = Var "x"
 let atomA = Atom("A",[]);;
 let fb = Atom("f",[Var "b"]);;
 let fa = Atom("f",[Var "a"]);;
 let fx1 = Atom("f",[Var "x"]);;
 let existsfx = Exists("x",fx1);;
 let seqAA = Sequent([atomA],[atomA]);;
 let axiomAA = Axiom(seqAA);;
 let seqAfbA = Sequent([atomA],[fb; atomA]);;
 let thinS = Thin_S(seqAfbA, axiomAA);;
 let seqfaAfbA = Sequent([fa;atomA],[fb; atomA]);;
 let thinA = Thin_A(seqfaAfbA,thinS);;
 let seqExists = Sequent([existsfx;atomA],[fb;atomA]);;
 let exists_ia = Exists_IA(seqExists, thinA,"a",v1,v2);;


let () = 
  output_string stdout (string_of_bool (proofchecker exists_ia))

		
	
		
		
		
