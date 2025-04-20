import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Seja₁ " colGt fixDecl : tactic
syntax "Seja " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Seja₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Seja₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Seja₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Seja₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Seja₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Seja₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Seja₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Seja₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Seja₁ $decl:fixDecl))


macro_rules
  | `(tactic| Seja $decl:fixDecl) => `(tactic| Seja₁ $decl)

macro_rules
  | `(tactic| Seja $decl:fixDecl $decls:fixDecl*) => `(tactic| Seja₁ $decl; Seja $decls:fixDecl*)

implement_endpoint (lang := en) noObjectIntro : CoreM String :=
pure "Não há objetos para introduzir."

implement_endpoint (lang := en) noHypIntro : CoreM String :=
pure "Não há hipótese para introduzir."

implement_endpoint (lang := en) negationByContra (hyp : Format) : CoreM String :=
pure s!"O alvo é uma negação. Não tem porquê demonstrá-lo por contradição. \
Você pode assumir {hyp}."

implement_endpoint (lang := en) wrongNegation : CoreM String :=
pure "This is not what you should assume for contradiction, even after pushing negations."

macro_rules
| `(ℕ) => `(Nat)


example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Seja b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Seja (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Seja (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Seja n
  success_if_fail_with_msg "Não há objetos para introduzir."
    Seja h
  intro hn
  Seja k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/-
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Seja (n > 0)
  success_if_fail_with_msg ""
    Seja n
  Seja k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Seja n > 0
  success_if_fail_with_msg ""
    Seja n
  Seja k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Seja n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Seja n ∈ A
  trivial
