(* type definitions: terms and formulas *)

type term = 
    Var of string 
  | Fn of (string*term list) 
  | Const of string

type formula = 
    True 
  | False 
  | Atom of (string*term list) 
  | Imply of (formula*formula)
  | Or of (formula*formula) 
  | And of (formula*formula) 
  | Exists of (string*formula) 
  | Forall of (string*formula ) 
  | Not of (formula)
  | Error of (string)   

(* check_formula : formula -> string
*  
*  check_formula will look at a formula and return a string 
*  that shows which formula it matches with. This is used in the formula_check
*  functions later. *)
let check_formula t1 = 
  (match t1 with
    True -> "true"
  | False -> "false"
  | Atom(_,_) -> "atom"
  | Imply(_,_) -> "imply"
  | Or(_,_) -> "or"
  | And(_,_) -> "and"
  | Exists(_,_) -> "exists"
  | Forall(_,_) -> "forall"
  | Not(_) -> "not"
  | Error(em) -> em) 

  
(* match_formula_1 : formula -> formula
*
* match_formula_1 will take in a formula and return a formula
* The formula type contains the following:
* And(form1, form2), Or(form1, form2), Imply(form1, form2), Not(form1)
* For these formula types, we return the first formula form1.
*
*)
let match_form_1 f = 
  (match f with
    And(f1, _) 
  | Or(f1,_) 
  | Imply(f1,_) 
  | Not(f1) -> f1
  | _ -> Error("unsuccessful match_form_1"))
	     
(* match_formula_2 : formula -> formula
*
* match_formula_2 will take in a formula and return a formula
* The formula type contains the following:
* And(form1, form2), Or(form1, form2), Imply(form1, form2),
* Atom(str,termList), Exists(str,form2), Forall(str,form2).
* For these formula types, we return the second formula form1.
*
*)    
let match_form_2 f = 
  (match f with
    And(_, f2) 
  | Or(_,f2) 
  | Imply(_,f2) 
  | Exists(_,f2) 
  | Forall(_,f2)-> f2
  | _ -> Error("unsuccessful match_form_2"))
  
  
(* getBoundVar : formula -> string
 * 
 * getBoundVar will return the variable used in existential
 * or universal statements: Exists("x", Atom(_)) -> "x" *)
let getBoundVar f = 
  (match f with
    Exists(x,_) 
  | Forall(x,_) -> x
  | _ -> "error in getBoundVar")
  
   

(* getStringTerm : term list -> string list
   
   getStringTerm will take in a term list and return a list of strings
   [Var "s"] -> ["s"] etc. 
   Used for checking free variables. *)
let rec getStringTerm tl =
  (match tl with 
    (h::tail) -> 
       (match h with  
          Var(s) 
        | Const(s) -> [s]@(getStringTerm tail)
        | Fn(str, termlist) -> getStringTerm termlist)
   | _ -> [])


(* checkFormulaVariables : formula -> string -> bool

   checkFormulaVariables will take in a formula and a string. 
   It will check to see if that string is contained within that formula.
   It is used to check for capture of free variables.  
   If string is in formula, returns true, else false. *)

let rec checkFormulaVariables f str = 
  (match f with
    True 
  | False -> false
  | Atom(s, l) -> if (List.length l = 0) then s = str else List.mem str (getStringTerm l)
  | Or(f1,f2) 
  | And(f1,f2)
  | Imply(f1,f2) -> (checkFormulaVariables f1 str) || (checkFormulaVariables f2 str)
  | Forall(str2,f2)
  | Exists(str2,f2) -> (str = str2) || (checkFormulaVariables f2 str)
  | Not(f1) -> checkFormulaVariables f1 str
  | Error(_) -> false)
  
(* checkFormulaListVariables : formula list -> string -> bool

   checkFormulaListVariables will take in a list of formulae and a string.
   It will check to see if that string is contained in any of the formulae.
   True if so, false if not. *)
let rec checkFormulaListVariables formlist str = 
  (match formlist with 
    [] -> false
  | (h::tail) -> 
        if checkFormulaVariables h str 
        then true 
        else checkFormulaListVariables tail str)


(* formula_list_equals : formula list -> formula list -> bool
 *
 * Checks to see if the lists are equal
 * with no regard to order
 * Used in interchange rule
  *)   
let rec formula_list_equals l1 l2 = 
  (match l1 with 
    h::tail -> 
        if List.mem h l2 
        then formula_list_equals tail l2
        else false
  | [] -> true)
  
(* getStringTerm : term list -> string list
   
   getStringTerm will take in a term list and return a list of strings
   [Var "s"] -> ["s"] etc. 
   Used for checking free variables. *)
let rec getStringTerm tl =
  (match tl with 
    (h::tail) -> 
       (match h with  
         Var(s) 
       | Const(s) -> [s]@(getStringTerm tail)
       | Fn(str, termlist) -> getStringTerm termlist)
  | _ -> [])

(* checkFormulaVariables : formula -> string -> bool

   checkFormulaVariables will take in a formula and a string. 
   It will check to see if that string is contained within that formula.
   It is used to check for capture of free variables.  
   If string is in formula, returns true, else false. *)

let rec checkFormulaVariables f str = 
  (match f with
    True 
  | False -> false
  | Atom(s, l) -> 
        if (List.length l = 0) 
        then s = str 
        else List.mem str (getStringTerm l)
  | Or(f1,f2) 
  | And(f1,f2)
  | Imply(f1,f2) -> 
      (checkFormulaVariables f1 str) || (checkFormulaVariables f2 str)
  | Forall(str2,f2)
  | Exists(str2,f2) -> 
      (str = str2) || (checkFormulaVariables f2 str)
  | Not(f1) -> checkFormulaVariables f1 str
  | Error(_) -> false)


  
(* checkFormulaListVariables : formula list -> string -> bool

   checkFormulaListVariables will take in a list of formulae and a string.
   It will check to see if that string is contained in any of the formulae.
   True if so, false if not. *)
let rec checkFormulaListVariables formlist str = 
  (match formlist with 
    [] -> false
  | (h::tail) -> 
          if checkFormulaVariables h str 
          then true 
          else checkFormulaListVariables tail str)


(* formula_list_equals : formula list -> formula list -> bool
 *
 * Checks to see if the lists are equal
 * with no regard to order
 * Used in interchange rule
  *)   
let rec formula_list_equals l1 l2 = 
  (match l1 with 
    h::tail -> 
      if List.mem h l2 
      then formula_list_equals tail l2
      else false
  | [] -> true)
  
  
  
  

 
