val inTheta : 'a -> ('a * 'b) list -> bool
val check_double_replacement : 'a -> ('b * 'a) list -> bool
val badNewName : 'a -> ('b * 'a) list -> bool
val substituteNameOK : Formulas.term list -> ('a * string) list -> bool
val substituteOK : Formulas.formula -> ('a * string) list -> bool
val getFromTheta : 'a -> ('a * 'b) list -> ('a * 'b) list
val getElement : Formulas.term -> string * string -> Formulas.term list
val functionReplace :
  Formulas.term list -> (string * string) list -> Formulas.term list
val termReplace :
  Formulas.term -> (string * string) list -> Formulas.term list
val termListReplace :
  Formulas.term list -> (string * string) list -> Formulas.term list
val replacement :
  Formulas.formula -> (string * string) list -> Formulas.formula
val get_term_variables : Formulas.term list -> string list
val check_if_var_present_t : Formulas.term -> Formulas.term list -> bool
val check_if_var_present_f : Formulas.term -> Formulas.formula -> bool
val replace_old_var :
  Formulas.term -> Formulas.term -> Formulas.term list -> Formulas.term list
val replace_term_ok : 'a list -> 'a list -> bool
val substituteTerm :
  Formulas.formula -> Formulas.term -> Formulas.term -> Formulas.formula
