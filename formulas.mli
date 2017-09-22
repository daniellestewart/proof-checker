type term = Var of string | Fn of (string * term list) | Const of string
type formula =
    True
  | False
  | Atom of (string * term list)
  | Imply of (formula * formula)
  | Or of (formula * formula)
  | And of (formula * formula)
  | Exists of (string * formula)
  | Forall of (string * formula)
  | Not of formula
  | Error of string
val check_formula : formula -> string
val match_form_1 : formula -> formula
val match_form_2 : formula -> formula
val getBoundVar : formula -> string
val getStringTerm : term list -> string list
val checkFormulaVariables : formula -> string -> bool
val checkFormulaListVariables : formula list -> string -> bool
val formula_list_equals : 'a list -> 'a list -> bool
