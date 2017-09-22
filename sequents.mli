type seq = Sequent of (Formulas.formula list * Formulas.formula list)
type proof =
    Axiom of seq
  | And_IS of (seq * proof * proof)
  | And_IA1 of (seq * proof)
  | And_IA2 of (seq * proof)
  | Or_IS1 of (seq * proof)
  | Or_IS2 of (seq * proof)
  | Or_IA of (seq * proof * proof)
  | Not_IA of (seq * proof)
  | Not_IS of (seq * proof)
  | Imply_IS of (seq * proof)
  | Imply_IA of (seq * proof * proof)
  | Exists_IS of (seq * proof * string * Formulas.term * Formulas.term)
  | Exists_IA of (seq * proof * string * Formulas.term * Formulas.term)
  | Forall_IS of (seq * proof * string * Formulas.term * Formulas.term)
  | Forall_IA of (seq * proof * string * Formulas.term * Formulas.term)
  | Thin_S of (seq * proof)
  | Thin_A of (seq * proof)
  | Contr_A of (seq * proof)
  | Contr_S of (seq * proof)
  | Interchange_A of (seq * proof)
  | Interchange_S of (seq * proof)
  | Cut of (seq * proof * proof)
val check_if_axiom : seq -> bool
val get_antecedent_head : proof -> Formulas.formula
val get_succedent_head : proof -> Formulas.formula
val get_antecedent : proof -> Formulas.formula list
val get_succedent : proof -> Formulas.formula list
val get_gamma_antec : proof -> Formulas.formula list
val get_theta_succed : proof -> Formulas.formula list
