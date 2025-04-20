import Verbose.Portuguese.Fix

open Lean Elab Tactic

syntax "Assuma₁ " colGt assumeDecl : tactic
syntax "Assuma " "que"? (colGt assumeDecl)+ : tactic
syntax "Assuma" ", para chegar em uma contradição, " (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Assuma₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Assuma₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Assuma₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Assuma₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Assuma $[que]? $decl:assumeDecl) => `(tactic| Assuma₁ $decl)
  | `(tactic| Assuma $[que]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Assuma₁ $decl; Assuma $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Assuma, para chegar em uma contradição, $x:ident : $type) => forContradiction x.getId type


example (P Q : Prop) : P → Q → True := by
  Assuma hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Assuma que hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Assuma que hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "Não há hipótese para introduzir."
    Assuma n
  intro n
  Assuma H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assuma hP
  Assuma, para chegar em uma contradição, hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assuma hP
  Assuma, para chegar em uma contradição, hnQ : ¬ Q
  exact h hnQ hP

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "O alvo é uma negação. Não tem porquê demonstrá-lo por contradição. Você pode assumir 0 = 1."
    Assuma, para chegar em uma contradição, h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Assuma h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Assuma, para chegar em uma contradição, h : 0 = 1
  norm_num at h

-- Check type ascriptions are not needed
example : ¬ (2 : ℝ) * -42 = 2 * 42 := by
  Assuma hyp : 2 * -42 = 2 * 42
  linarith
