import Verbose.Tactics.Common

open Lean

namespace Verbose.Portuguese

declare_syntax_cat appliedTo
syntax "aplicado em " sepBy(term, " e ") : appliedTo

def appliedToTerm : TSyntax `appliedTo → Array Term
| `(appliedTo| aplicado em $[$args]e*) => args
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat usingStuff
syntax " usando " sepBy(term, " e ") : usingStuff
syntax " usando que " term : usingStuff

def usingStuffToTerm : TSyntax `usingStuff → Array Term
| `(usingStuff| usando $[$args]e*) => args
| `(usingStuff| usando que $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat maybeApplied
syntax term (appliedTo)? (usingStuff)? : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $f:term) => pure f
| `(maybeApplied| $f:term $args:appliedTo) => `($f $(appliedToTerm args)*)
| `(maybeApplied| $f:term $args:usingStuff) => `($f $(usingStuffToTerm args)*)
| `(maybeApplied| $f:term $args:appliedTo $extras:usingStuff) =>
  `($f $(appliedToTerm args)* $(usingStuffToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeApplied

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeApplied)
| [x] => `(maybeApplied|$x:term)
| [x, y] => `(maybeApplied|$x:term aplicado em $y)
| [x, y, z] => `(maybeApplied|$x:term aplicado em $y usando que $z)
| x::y::l => `(maybeApplied|$x:term aplicado em $y:term usando que [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuff
syntax (ppSpace colGt maybeTypedIdent)* : newStuff
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent : newStuff
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent " e "
       ppSpace colGt maybeTypedIdent : newStuff

def newStuffToArray : TSyntax `newStuff → Array MaybeTypedIdent
| `(newStuff| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuff| $x:maybeTypedIdent tal que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuff| $x:maybeTypedIdent tal que $y:maybeTypedIdent e $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatEN : List MaybeTypedIdent → MetaM (TSyntax `newStuff)
| [x] => do `(newStuff| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuff| $(← x.stx):maybeTypedIdent tal que $(← y.stx'))
| [x, y, z] => do `(newStuff| $(← x.stx):maybeTypedIdent tal que $(← y.stx) e $(← z.stx))
| _ => pure default

declare_syntax_cat newFacts
syntax colGt namedType : newFacts
syntax colGt namedType " e "  colGt namedType : newFacts
syntax colGt namedType ", "  colGt namedType " e "  colGt namedType : newFacts

def newFactsToArray : TSyntax `newFacts → Array NamedType
| `(newFacts| $x:namedType) => #[toNamedType x]
| `(newFacts| $x:namedType e $y:namedType) =>
    #[toNamedType x, toNamedType y]
| `(newFacts| $x:namedType, $y:namedType e $z:namedType) =>
    #[toNamedType x, toNamedType y, toNamedType z]
| _ => #[]

def newFactsToTypeTerm : TSyntax `newFacts → MetaM Term
| `(newFacts| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFacts| $x:namedType e $y) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    `($xT ∧ $yT)
| `(newFacts| $x:namedType, $y:namedType e $z) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $yT ∧ $zT)
| _ => throwError "Could not convert the description of new facts into a term."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsToRCasesPatt : TSyntax `newFacts → RCasesPatt
| `(newFacts| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFacts| $x:namedType e $y:namedType) => namedTypeListToRCasesPatt [x, y]
| `(newFacts|  $x:namedType, $y:namedType e $z:namedType) => namedTypeListToRCasesPatt [x, y, z]
| _ => default

declare_syntax_cat newObject
syntax maybeTypedIdent "tal que " maybeTypedIdent : newObject
syntax maybeTypedIdent "tal que " maybeTypedIdent colGt " e " maybeTypedIdent : newObject

def newObjectToTerm : TSyntax `newObject → MetaM Term
| `(newObject| $x:maybeTypedIdent tal que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObject| $x:maybeTypedIdent tal que $new₁ e $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "Could not convert the new object description into a term."

-- TODO: create helper functions for the values below
open Tactic Lean.Elab.Tactic.RCases in
def newObjectToRCasesPatt : TSyntax `newObject → RCasesPatt
| `(newObject| $x:maybeTypedIdent tal que $new) => maybeTypedIdentListToRCasesPatt [x, new]
| `(newObject| $x:maybeTypedIdent tal que $new₁ e $new₂) => maybeTypedIdentListToRCasesPatt [x, new₁, new₂]
| _ => default

declare_syntax_cat facts
syntax term : facts
syntax term " e " term : facts
syntax term ", " term " e " term : facts
syntax term ", " term ", " term " e " term : facts

def factsToArray : TSyntax `facts → Array Term
| `(facts| $x:term) => #[x]
| `(facts| $x:term e $y:term) => #[x, y]
| `(facts| $x:term, $y:term e $z:term) => #[x, y, z]
| `(facts| $x:term, $y:term, $z:term e $w:term) => #[x, y, z, w]
| _ => #[]

def arrayToFacts : Array Term → CoreM (TSyntax `facts)
| #[x] => `(facts| $x:term)
| #[x, y] => `(facts| $x:term e $y:term)
| #[x, y, z] => `(facts| $x:term, $y:term e $z:term)
| #[x, y, z, w] => `(facts| $x:term, $y:term, $z:term e $w:term)
| _ => default

end Verbose.Portuguese

/-- Convert an expression to a `maybeApplied` syntax object, in `MetaM`. -/
def Lean.Expr.toMaybeApplied (f : Expr) : MetaM (TSyntax `maybeApplied) := do
  let fn := f.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match f.getAppArgs.toList with
  | [] => `(maybeApplied|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeApplied|$fnS:term aplicado em $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeApplied|$fnS:term aplicado em [$arr:term,*])

implement_endpoint (lang := en) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"TO nome {n} já está em uso."

implement_endpoint (lang := en) notDefEq (f val : MessageData) : CoreM MessageData :=
pure m!"O termo {f}\nNão é intensionamente igual ao {val} esperado."

implement_endpoint (lang := en) notAppConst : CoreM String :=
pure "Não é uma aplicação de definição."

implement_endpoint (lang := en) cannotExpand : CoreM String :=
pure "Não foi possível expandir."

implement_endpoint (lang := en) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"O termo {tgt} não parece ser inferível a partir de no máximo um dado local."

implement_endpoint (lang := en) couldNotProve (goal : Format) : CoreM String :=
pure s!"Não foi possível demonstrar:\n{goal}"

implement_endpoint (lang := en) failedProofUsing (goal : Format) : CoreM String :=
pure s!"Falha ao demonstrar isso usando os fatos providos.\n{goal}"
