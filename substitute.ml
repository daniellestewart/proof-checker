open Formulas
open Sequents



(* inTheta : 
*
* inTheta takes in a string and a list theta.
* If the string is found in the list as (s, x)
* for any value x (i.e. s is the first element
* in a tuple found in theta) then we return true.
*
* *)
let rec inTheta s t = 
  (match t with
    h::tail -> 
      (match h with
         (a,b) -> if s = a 
                  then true
                  else inTheta s tail)
  | [] -> false)

(* check_double_replacement :  'a -> ('a * 'b) list -> bool
 * 
 * Takes in a string and a list theta
 * and checks to see if there is a double replacement
 * that will occur.
 * For instance: 
 * Theta = [(x,p);(z,d);(y,p)]
 * This is a bad replacement since both x and y 
 * will be renamed to p. 
 * The check will be check_double_replacement "p" theta
 * and will come back true - yes, p is already there. 
 * Used in the badNewName function below. 
 *)
 let rec check_double_replacement s t = 
    (match t with 
      h::tail -> let (a,b) = h 
                 in if s = b 
                    then true 
                    else check_double_replacement s tail
    | [] -> false)

(* badNewName : 'a -> ('b * 'a) list -> bool
*
* badNewName takes in a string and a list theta of replacements.
* It will see if there is a renaming clash. 
* For instance, say the string is "c" and theta = [(x,c)]
* This tells us that a replacement is coming that
* will replace all occurrances of x with c in the formula that 
* "c" appears in. 
* This obviously will be incorrect and the substitution is 
* not okay. 
*  
* If the substitution is okay, returns true. Else false. 
*
* Used in functions substitutionOK & substitutionTermOK
*
 *)
let rec badNewName str t = 
  (match t with 
    [] -> false
  | h::[] -> let (a,b) = h 
             in str = b 
  	| h::tail -> let (a,b) = h 
               in if (str = b) || (check_double_replacement b tail) 
                  then true
                  else badNewName str tail)
  							  
 							  
(* substituteNameOK : term list -> ('a * string) list -> bool
*
* substituteNameOK takes in a term list and a list theta of replacements.
* It will check to make sure that any replacements made
* will not capture free variables. 
* If the substitution is okay, returns true. Else false. 
*
* Used in function substitutionOK
*
 *)
 let rec substituteNameOK l t = 
   (match l with
     h::[] -> 
       (match h with
          Var(s) 
        | Const(s) -> 
              if badNewName s t 
              then false 
              else true
        | Fn(s,l1) -> substituteNameOK l1 t)
   							
   | h::tail -> 
        (match h with 
           Var(s) 
         | Const(s) -> 
               if badNewName s t 
               then false
               else (substituteNameOK tail t)
         | Fn(s,l1) -> substituteNameOK l1 t)
   | _ -> false)
  
   							 							 

(* substituteOK : formula -> ('a * string) list -> bool
*
* substituteOK takes in a formula and a list theta of replacements.
* It will check to make sure that any replacements made
* will not capture free variables. 
* If the substitution is okay, returns true. Else false. 
*
 *)
let rec substituteOK f t = 
  (match f with
    True
  | False -> true
  | Atom(s,l1) -> substituteNameOK l1 t
  | Imply(f1,f2)
  | And(f1,f2)
  | Or(f1,f2) -> (substituteOK f1 t) && (substituteOK f2 t)
  | Exists(s,f1) 
  | Forall(s,f1) -> not(badNewName s t) && (substituteOK f1 t)
  | Not(f1) -> substituteOK f1 t
  | Error(s) -> false)
  						 

  
(* getFromTheta : 
*
* getFromTheta takes in a string s and returns 
* a list containing the tuple from theta corresponding to 
* s as the first element and it's replacement
* as the second element. 
*
* For example, if s = "x" and theta = [("y","p");("x","w")]
* then this function will return [("x","w")]
 *)
let rec getFromTheta s t = 
  (match t with 
    h::tail -> 
       (match h with
           (a,b) -> if s = a 
                    then [(a,b)]
                    else getFromTheta s tail)
  | [] -> []) 


 
(* getElement : term -> string * string -> term list
*
* getElement will take in a nonrecursive term and a replacement
 * list theta. It will either make the replacement if it's in the list
 * or it will return the term as is (if not in list) 
 *)
let getElement el theta= 
  (match el, theta with 
    Var(s),(a,b) -> 
        if s = a 
        then [Var(b)]
        else [Var(s)]
  	| Const(s),(a,b) -> 
        if s = a 
        then [Const(b)]
        else [Const(s)]
  	| _,(a,b) -> [])
  	
  	
(* functionReplace : term list -> (string * string) list -> term list
   
   functionReplace processes recursively a term of the form
   Fn s termList
   It will take in the term list and the theta list
   making necessary replacements.
   It returns a list of terms with replacements made.
  *) 
 
let rec functionReplace l theta = 
   match l,theta with
     (h1::t1),(h2::t2) -> 
       (match h1 with
     			Var s 
     		| Const s -> 
            (termReplace h1 theta)@(functionReplace t1 theta)
     		| Fn(s,termList) -> 
     		    functionReplace termList theta) 
   | _,_ -> [] 
   
(* termReplace : term -> (string * string) list -> term list

   termReplace will take in a term (el) and a list (t). 
   The list is comprised of ordered pairs that tell which
   replacement is occuring. 
   Return value is a list containing the replacement term.
   The term will contain a string. That string will be converted
   to the replacement in theta (t) or it will be sent back if
   there is no appropriate conversion.
   t = [("x","y");("a","b")]
   el1 = Var "x"
   Return value will be [Var "y"] for el1
   el2 = Var "z"
   Return value will be [Var "z"] for el2
 *)
and termReplace el t = 
  (match el,t with 
    Var(s),(h::tail) ->  let (a,b) = h 
           in if s = a 
              then [Var b]
              else [Var(s)]@(termReplace el tail)
  | Const(s), (h::tail) -> let (a,b) = h 
           in if s = a 
              then [Const b]
              else [Var(s)]@(termReplace el tail)
  | Fn(s, termList), t -> functionReplace termList t 
  | _, [] -> [])
  	  	



(* termListReplace : 
*
* termListReplace takes in a list of terms and a replacement
* list theta. 
* It will perform the replacement according to the 
* tuples in theta. 
*
* For instance, if l = [Var "x"; Var "y"; Const "z"]
* and theta = [("x","p");("y","n")]
* the return list is [Var "p"; Var "n"; Const "z"]
*
 *)
let rec termListReplace l t = 
  (match l with 
    h::tail -> 
      (match h with 
        Var(s) ->    
          if not(badNewName s t) && (inTheta s t)
    				then (match getFromTheta s t with
    				        [(a,b)] -> [Var b]@(termListReplace tail t)
    				      | _ -> [Var s]@(termListReplace tail t))
    				else [Var s]@(termListReplace tail t)
      | Const(s) -> 
          if not(badNewName s t) && (inTheta s t)
    				then (match getFromTheta s t with
    				        [(a,b)] -> [Const b]@(termListReplace tail t)
    				      | _ -> [Const s]@(termListReplace tail t))
    				else [Const s]@(termListReplace tail t)
    		| Fn(s,l) -> [Fn(s, termListReplace l t)])
   | [] -> [])
    							 
 
 
(* replacement : formula -> (string * string) list -> string -> formula
*
* replacement will take in a formula, a replacement list theta, and a string
* telling what the new variable will be after replacement. 
*)  
  
let rec replacement f t = 
  (match f with 
    True -> True
  | False -> False
  | Atom(s,l) -> Atom(s, termListReplace l t)
  | Imply(f1, f2) -> Imply(replacement f1 t, replacement f2 t)
  | Or(f1,f2) -> Or(replacement f1 t, replacement f2 t)
  | And(f1,f2) -> And(replacement f1 t, replacement f2 t)
  | Not(f1) -> Not(replacement f1 t)

  | Exists(s,f1) -> 
       if inTheta s t
       then (match getFromTheta s t with
               [(a,b)] -> Exists(b, replacement f1 t)
             | _ -> Error("replacement issue"))
       else Error("something wrong in replacement")
       
  | Forall(s,f1) -> 
       if inTheta s t 
       then (match getFromTheta s t with
               [(a,b)] -> Forall(b, replacement f1 t)
             | _ -> Error("replacement issue"))
       else Error("something wrong in replacement")
       
  | Error(s) -> Error("something wrong in replacement"))

(*
* get_term_variables : term list -> string list
* Takes in a list of terms and returns a list of strings.
* These strings are all variables or constant strings
* found in every term in term list. 
* For example: tlist = [Var "x"; Const "1"; Fn("f",{Var "y"])]
* Return value = ["x"; "1"; "y"]
* Used in term replacement to make sure that no 
* free variables in the formula are captured by given
 * term replacement.
*)
let rec get_term_variables tlist = 
   (match tlist with 
      h::tail -> 
        (match h with 
          Var(s) 
        | Const(s) -> s::(get_term_variables tail)  
        | Fn(_, tlist2) -> (get_term_variables tlist2)@(get_term_variables tail) )
    | [] -> []);;  


(* check_if_var_present_t : term -> term list -> bool
* check_if_var_present_t takes in a list of terms and 
* checks to see if one of them is a variable (Var "s")
* If so, returns true. Else false. 
*)
let rec check_if_var_present_t oldVar tlist = 
   (match tlist with 
      h::tail -> 
        (match h with 
          Var(s) -> if Var s = oldVar 
                    then true
                    else check_if_var_present_t oldVar tail
        | Const(s) -> check_if_var_present_t oldVar tail  
        | Fn(_, tlist2) -> 
            (check_if_var_present_t oldVar tlist2) || (check_if_var_present_t oldVar tail))
    | [] -> false);;

(* check_if_var_present_f : term -> formula -> bool
* check_if_var_present_f takes in a formula and 
* checks to see if in it is equal to term.
* If so, returns true. Else false. 
*)
let rec check_if_var_present_f term form = 
  (match form with 
    True 
  | False -> false
  | Atom(str, termList) -> check_if_var_present_t term termList
  | And(f1, f2) 
  | Or(f1, f2) 
  | Imply(f1, f2) -> (check_if_var_present_f term f1) || 
                  (check_if_var_present_f term f2)
  | Exists(str, f1) 
  | Forall(str, f1) -> (check_if_var_present_f term f1)
  | Not(f1) -> (check_if_var_present_f term f1)
  | _ -> false)

(* replace_old_var : term -> term list -> term list
* replace_old_var will take in a term - the term Var "s"
* which will be replaced, the new term to replace Var "s", 
* a term list which contains the old variable Var "s",
* and will return the list with replacement made.
* Used in substitute_term.
*)
let rec replace_old_var oldVar newTerm termList = 
  (match termList with 
    h::tail -> 
      (match h with
        Var s -> if Var s = oldVar
                 then newTerm::tail
                 else h::(replace_old_var oldVar newTerm tail)
      | Const s -> h::(replace_old_var oldVar newTerm tail)
      | Fn(s, tl) -> 
        [Fn(s, (replace_old_var oldVar newTerm tl))]@(replace_old_var oldVar newTerm tail))
  | [] -> [])


(* replace_term_ok term -> term list -> bool
* replace_term_ok takes in two string lists. 
* It will make sure that none of the strings in the
* first list are found in the second list.
* This will prevent capture of free variables
* in term replacement. 
*)
let rec replace_term_ok newVarList oldVarList = 
  (match newVarList with 
    h::tail -> if List.mem h oldVarList
               then false
               else replace_term_ok tail oldVarList
  | [] -> true)
  

(* substituteTerm : formula -> term -> term -> formula
* substituteTerm takes in a formula in which a variable will
* be replaced by a term, the variable to replace, and 
* the term that will replace the variable. 
* It will return a formula with the replacement made. 
* If the replacement is not safe (capture of free variables, 
* or there is no variable to replace in the formula)
* then the return formula will be Error("not okay to replace").
* This will create a false "value" in the proof_checker function.
*)
let rec substituteTerm f oldVar newTerm = 
  (match f with
    True -> True
  | False -> False
  | Atom(str, termList) -> 
      if (check_if_var_present_t oldVar termList) && 
         (replace_term_ok (get_term_variables [newTerm]) (get_term_variables termList))
      then Atom(str, (replace_old_var oldVar newTerm termList))
      else Error("Not okay to replace term.")
  | Imply(f1,f2) -> 
      Imply((substituteTerm f1 oldVar newTerm), (substituteTerm f2 oldVar newTerm))
  | Or(f1, f2) -> 
      if (check_if_var_present_f oldVar f1)
      then Or((substituteTerm f1 oldVar newTerm), f2)
      else if (check_if_var_present_f oldVar f2)
           then Or(f1, (substituteTerm f2 oldVar newTerm))
           else Error("Not okay to replace term.")
  | And(f1, f2) -> 
      if (check_if_var_present_f oldVar f1)
      then And((substituteTerm f1 oldVar newTerm), f2)
      else if (check_if_var_present_f oldVar f2)
           then And(f1, (substituteTerm f2 oldVar newTerm))
           else Error("Not okay to replace term.")
  | Exists(str, f1) -> Exists(str, (substituteTerm f1 oldVar newTerm))
  | Forall(str, f1) -> Forall(str, (substituteTerm f1 oldVar newTerm))
  | Not(f1) -> Not((substituteTerm f1 oldVar newTerm))
  | Error(str) -> Error(str))
      
 
