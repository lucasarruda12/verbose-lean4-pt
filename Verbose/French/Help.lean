import Verbose.Tactics.Help
import Verbose.French.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.French

open Lean.Parser.Tactic in
elab "aide" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "La tactique d’aide n’est pas activée."
match h with
| some h => do
        let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
        if s.isEmpty then
          logInfo (msg.getD "Pas de suggestion")
        else
          Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Aide")
| none => do
   let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
   if s.isEmpty then
          logInfo (msg.getD "Pas de suggestion")
    else
      Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Aide")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "un nombre réel"
| "ℕ" => "un nombre entier naturel"
| "ℤ" => "un nombre entier relatif"
| t => "une expression de type " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "des nombres réels"
| "ℕ" => "des nombres entiers naturels"
| "ℤ" => "des nombres entiers relatifs"
| t => "des expressions de type " ++ t

def libre (s : Ident) : String := s!"Le nom {s.getId} peut être choisi librement parmi les noms disponibles."

def printIdentList (l : List Ident) : String := commaSep (l.toArray.map (toString ·.getId)) "et"

def libres (ls : List Ident) : String :=
s!"Les noms {printIdentList ls} peuvent être choisis librement parmi les noms disponibles."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} est de la forme « {headDescr} »"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} commence par « {headDescr} »"

implement_endpoint (lang := fr) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := fr) helpSinceExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (hypS ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $hypS:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := fr) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... et ..."
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := fr) helpSinceConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... et ..."
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $p₁S:term et $p₂S on obtient ($h₁I : $p₁S) et ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := fr) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  describeHypShape hyp "... ou ..."
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute en utilisant $hyp.ident:term)

implement_endpoint (lang := fr) helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit := do
  describeHypShape hyp "... ou ..."
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute selon que $p₁S:term ou $p₂S)

implement_endpoint (lang := fr) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une implication"
  if closes then do
    pushCom "La conclusion de cette implication est le but courant"
    pushCom "On peut donc utiliser cette hypothèse avec :"
    pushTac `(tactic| Par $hyp.ident:term il suffit de montrer $(← le.stx))
    flush
    pushCom "Si vous disposez déjà d'une preuve {HN} de {← le.fmt} alors on peut utiliser :"
    pushTac `(tactic|On conclut par $hyp.ident:term appliqué à $HN.ident)
  else do
    pushCom "La prémisse de cette implication est {← le.fmt}"
    pushCom "Si vous avez une démonstration {HN} de {← le.fmt}"
    pushCom "vous pouvez donc utiliser cette hypothèse avec :"
    pushTac `(tactic|Par $hyp.ident:term appliqué à $HN.ident:term on obtient $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := fr) helpSinceImplicationSuggestion (stmt goalS leS : Term) (hyp H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une implication"
  if closes then do
    pushCom "La conclusion de cette implication est le but courant"
    pushCom "On peut donc utiliser cette hypothèse avec :"
    pushTac `(tactic| Comme $stmt:term il suffit de montrer que $(← le.stx):term)
    flush
    pushCom "Si vous disposez déjà d'une preuve de {← le.fmt} alors on peut utiliser :"
    pushTac `(tactic|Comme $stmt:term et $(← le.stx):term on conclut que $goalS)
  else do
    pushCom "La prémisse de cette implication est {← le.fmt}"
    pushCom "Si vous avez une démonstration de {← le.fmt}"
    pushCom "vous pouvez donc utiliser cette hypothèse avec :"
    pushTac `(tactic|Comme $stmt:term et $leS:term on obtient $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := fr) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une équivalence"
  pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {← l.fmt}) par le membre de droite  (c'est à dire {← r.fmt}) dans le but par :"
  pushTac `(tactic|On réécrit via $hyp.ident:term)
  flush
  pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
  pushTac `(tactic|On réécrit via ← $hyp.ident)
  flush
  pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
  pushTac `(tactic|On réécrit via $hyp.ident:term dans l'hypothèse $hyp'N.ident:ident)
  flush
  pushCom " ou "
  pushTac `(tactic|On réécrit via ← $hyp.ident:term dans l'hypothèse $hyp'N.ident:ident)

implement_endpoint (lang := fr) helpSinceEquivalenceSuggestion
    (hyp : Name) (stmt : Term) (l r : Expr) (hyp' : Ident) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une équivalence"
  pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {← l.fmt}) par le membre de droite  (c'est à dire {← r.fmt}) dans le but (ou vice-versa) par :"
  pushTac `(tactic|Comme $stmt:term il suffit de montrer que ?_)
  pushCom "en remplaçant le point d'interrogation par le nouveau but."
  flush
  pushCom "On peut aussi effectuer de tels remplacements dans un fait qui découle directement des hypothèses courantes par"
  pushTac `(tactic|Comme $stmt:term et ?_ on obtient $hyp':ident : ?_)
  pushCom "en remplaçant le premier point d'interrogation par le fait dans lequel on veut effectuer le remplacement et le second par le nouveau fait obtenu."
  pushComment <| libre hyp'

implement_endpoint (lang := fr) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : String) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une égalité"
  if closes then
    pushComment <| s!"Le but courant en découle immédiatement"
    pushComment   "On peut l'utiliser avec :"
    pushTac `(tactic|On conclut par $hyp.ident:ident)
  else do
    pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {l}) par le membre de droite  (c'est à dire {r}) dans le but par :"
    pushTac `(tactic|On réécrit via $hyp.ident:ident)
    flush
    pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
    pushTac `(tactic|On réécrit via ← $hyp.ident:ident)
    flush
    pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'} par"
    pushTac `(tactic|On réécrit via $hyp.ident:ident dans l'hypothèse $hyp'.ident:ident)
    flush
    pushCom " ou "
    pushTac `(tactic|On réécrit via ← $hyp.ident:ident dans l'hypothèse $hyp'.ident:ident)
    flush
    pushCom "On peut aussi s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
    pushTac `(tactic| On combine [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités."

implement_endpoint (lang := fr) helpSinceEqualSuggestion (hyp : Name) (news : Ident)
    (closes : Bool) (l r : String) (leS reS goalS : Term) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une égalité"
  let eq ← `($leS = $reS)
  if closes then
    pushComment <| s!"Le but courant en découle immédiatement"
    pushComment   "On peut l'utiliser avec :"
    pushTac `(tactic|Comme $eq:term on conclut que $goalS)
  else do
    pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {l}) par le membre de droite  (c'est à dire {r}) (ou dans l’autre sens) dans le but par :"
    pushTac `(tactic|Comme $eq:term il suffit de montrer que ?_)
    pushCom "en écrivant bien sûr le nouveau but à la place du ?_"
    flush
    pushCom "On peut aussi effectuer de tels remplacements dans dans un fait qui découle directement des hypothèses courantes  par"
    pushTac `(tactic|Comme $eq:term et ?_ on obtient $news:ident : ?_)
    pushCom "où le premier ?_ est à remplacer par l’affirmation de ce fait et le second par la nouvelle information obtenue."

implement_endpoint (lang := fr) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une inégalité"
  if closes then
    pushCom "Le but courant en découle immédiatement"
    pushCom "On peut l'utiliser avec :"
    pushTac `(tactic|On conclut par $hyp.ident:ident)
  else do
    pushCom "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
    pushTac `(tactic| On combine [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités ou inégalités."

implement_endpoint (lang := fr) helpSinceIneqSuggestion (hyp : Name) (stmt goal : Term) (closes : Bool) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une inégalité"
  if closes then
    pushCom "Le but courant en découle immédiatement"
    pushCom "On peut l'utiliser avec :"
    pushTac `(tactic|Comme $stmt:term on conclut que $goal)
  else do
    flush
    pushCom "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
    pushTac `(tactic| Comme $stmt:term et ?_ on conclut que $goal)
    pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités ou inégalités."

implement_endpoint (lang := fr) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une intersection"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := fr) helpSinceMemInterSuggestion (stmt : Term) (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une intersection"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient ($h₁.ident : $elemS ∈ $p₁S) et ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := fr) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une réunion"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute en utilisant $hyp.ident)

implement_endpoint (lang := fr) helpSinceMemUnionSuggestion (elemS leS reS : Term) (hyp : Name) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une réunion"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute selon que $elemS ∈ $leS ou $elemS ∈ $reS)

implement_endpoint (lang := fr) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance"

implement_endpoint (lang := fr) helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "Cette hypothèse est une contradiction."
  pushCom "On peut en déduire tout ce qu'on veut par :"
  pushTac `(tactic|(Montrons une contradiction
                    On conclut par $hypId:ident))

implement_endpoint (lang := fr) helpSinceContradictionSuggestion
     (stmt goal : Term) : SuggestionM Unit := do
  pushComment <| "Cette hypothèse est une contradiction."
  pushCom "On peut en déduire le but par :"
  pushTac `(tactic|Comme $stmt:term on conclut que $goal)

implement_endpoint (lang := fr) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} affirme l'inclusion de {l} dans {← r.fmt}."
  pushCom "On peut s'en servir avec :"
  pushTac `(tactic| Par $hyp.ident:ident appliqué à $x.ident en utilisant $hx.ident on obtient $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "où {x} est {describe ambientTypePP} et {hx} est une démonstration du fait que {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := fr) helpSinceSubsetSuggestion (hyp x hx' : Name) (stmt : Term)
    (l r : Expr) (ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} affirme l'inclusion de {← l.fmt} dans {← r.fmt}."
  pushCom "On peut s'en servir avec :"
  pushTac `(tactic| Comme $stmt:term et $x.ident ∈ $(← l.stx) on obtient $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "où {x} est {describe ambientTypePP}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := fr) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "Cette hypothèse est exactement ce qu'il faut démontrer"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On conclut par $hypId:ident)

implement_endpoint (lang := fr) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Cette hypothèse commence par l'application d'une définition."
  pushCom "On peut l'expliciter avec :"
  pushTac `(tactic|On reformule l'hypothèse $hypId:ident en $expandedHypTypeS)
  flush

implement_endpoint (lang := fr) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $n₀.ident en utilisant $hn₀.ident on obtient $var_name'.ident:ident tel que ($ineqIdent : $ineqS) et ($hn'S : $p'S))
  pushCom "où {n₀} est {describe t} et {hn₀} est une démonstration du fait que {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := fr) helpSinceForAllRelExistsRelSuggestion (stmt :
    Term) (hyp var_name' n₀ : Name) (stmtn₀ : Term)
    (stmtn₀Str headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $stmtn₀ on obtient $var_name'.ident:ident tel que ($ineqIdent : $ineqS) et ($hn'S : $p'S))
  pushCom "où {n₀} est {describe t} et la relation {stmtn₀Str} doit découler directement d’une hypothèse."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := fr) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $n₀.ident en utilisant $hn₀.ident on obtient $n'.ident:ident tel que ($hn'.ident : $p'S))
  pushCom "où {n₀} est {describe t} et h{n₀} est une démonstration du fait que {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := fr) helpSinceForAllRelExistsSimpleSuggestion (stmt : Term)
  (hyp n' hn' n₀ : Name)
  (stmtn₀ : Term) (stmtn₀Str headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $stmtn₀ on obtient $n'.ident:ident tel que ($hn'.ident : $p'S))
  pushCom "où {n₀} est {describe t} et la relation {stmtn₀Str} doit découler directement d’une hypothèse."
  pushComment <| libres [n'.ident,  hn'.ident]

implement_endpoint (lang := fr) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $n₀.ident en utilisant $hn₀.ident on obtient ($newsI : $pS))
  pushCom "où {n₀} est {describe t} et {hn₀} est une démonstration du fait que {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := fr) helpSinceForAllRelGenericSuggestion (stmt : Term) (hyp n₀ : Name)
  (stmtn₀ : Term)
  (stmtn₀Str headDescr : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $stmtn₀ on obtient ($newsI : $pS))
  pushCom "où {n₀} est {describe t} et {stmtn₀Str} découle directement d’une hypothèse."
  pushComment <| libre newsI

implement_endpoint (lang := fr) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident on obtient $var_name'.ident:ident tel que (ineqIdent : $ineqS) et ($hn'S : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := fr) helpSinceForAllSimpleExistsRelSuggestion (stmt : Term) (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient $var_name'.ident:ident tel que (ineqIdent : $ineqS) et ($hn'S : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := fr) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident on obtient $var_name'.ident:ident tel que ($hn'.ident : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := fr) helpSinceForAllSimpleExistsSimpleSuggestion (stmt : Term) (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient $var_name'.ident:ident tel que ($hn'.ident : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := fr) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident et $var_name'₀.ident en utilisant $H.ident on obtient ($h.ident : $p'S))
  pushCom "où {nn₀} et {var_name'₀} sont {describe_pl t} et {H} est une démonstration de {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := fr) helpSinceForAllSimpleForAllRelSuggestion (stmt rel₀S : Term) (hyp nn₀ var_name'₀ h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $rel₀S on obtient ($h.ident : $p'S))
  pushCom "où {nn₀} et {var_name'₀} sont {describe_pl t} et {rel₀} découle immédiatement d’une hypothèse."
  pushComment <| libre h.ident

implement_endpoint (lang := fr) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident on obtient ($hn₀.ident : $pS))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
  pushTac `(tactic|On applique $hyp.ident:ident à $nn₀.ident)

implement_endpoint (lang := fr) helpSinceForAllSimpleGenericSuggestion (stmt : Term) (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient ($hn₀.ident : $pS))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
  pushTac `(tactic|On applique $hyp.ident:ident à $nn₀.ident)

implement_endpoint (lang := fr) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeAppliedFR
  pushCom "Comme le but est {but}, on peut utiliser :"
  pushTac `(tactic|On conclut par $prfS)

implement_endpoint (lang := fr) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic| Par $hyp.ident:term on obtient $n.ident:ident tel que ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := fr) helpSinceExistsSimpleSuggestion (stmt : Term) (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic| Comme $stmt:term on obtient $n.ident:ident tel que ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := fr) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"L'objet {hyp}" ++ match t with
          | "ℝ" => " est un nombre réel fixé."
          | "ℕ" => " est un nombre entier naturel fixé."
          | "ℤ" => " est un nombre entier relatif fixé."
          | s => s!" : {s} est fixé."

implement_endpoint (lang := fr) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "Je n'ai rien à déclarer à propos de cette hypothèse."
  flush

implement_endpoint (lang := fr) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "Je n'ai rien à déclarer à propos de ce but."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "Le but commence par « {headDescr} »"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "Le but est de la forme « {headDescr} »"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Une démonstration directe commence donc par :"

implement_endpoint (lang := fr) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Le but commence par l’application d’une définition."
  pushCom "On peut l’expliciter par :"
  pushTac `(tactic|Montrons que $expandedGoalTypeS)
  flush

implement_endpoint (lang := fr) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "L’étape suivante est d'annoncer :"
  pushTac `(tactic| Montrons maintenant que $actualGoalS)

implement_endpoint (lang := fr) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Soit $ineqS)

implement_endpoint (lang := fr) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Montrons que $n₀.ident convient : $fullTgtS)
  pushCom "où {n₀} est {describe t}"

implement_endpoint (lang := fr) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Montrons que $nn₀.ident convient : $tgt)
  pushCom "où {nn₀} est {describe t}"

implement_endpoint (lang := fr) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... et ..."
  descrDirectProof
  pushTac `(tactic|Montrons d'abord que $p)
  pushCom "Une fois cette première démonstration achevée, il restera à montrer que {← p'.fmt}"
  flush
  pushCom "On peut aussi commencer par"
  pushTac `(tactic|Montrons d'abord que $p')
  pushCom "puis, une fois cette première démonstration achevée, il restera à montrer que {← p.fmt}"

implement_endpoint (lang := fr) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... ou ..."
  pushCom "Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :"
  pushTac `(tactic|Montrons que $p)
  flush
  pushCom "ou bien :"
  pushTac `(tactic|Montrons que $p')

implement_endpoint (lang := fr) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Supposons $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

implement_endpoint (lang := fr) helpEquivalenceGoalSuggestion (mpF mrF : Format) (mpS mrS : Term) :
    SuggestionM Unit := do
  pushCom "Le but est une équivalence. On peut annoncer la démonstration de l'implication de la gauche vers la droite par :"
  pushTac `(tactic|Montrons d'abord que $mpS)
  pushCom "Une fois cette première démonstration achevée, il restera à montrer que {mrF}"
  flush
  pushCom "On peut aussi commencer par"
  pushTac `(tactic|Montrons d'abord que $mrS)
  pushCom "puis, une fois cette première démonstration achevée, il restera à montrer que {mpF}"

implement_endpoint (lang := fr) helpSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité entre ensembles"
  pushCom "On peut la démontrer par réécriture avec la commande"
  pushTac `(tactic|On réécrit via ?_)
  flush
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $lS:term = $rS par?)
  flush
  pushCom "On peut aussi la démontrer par double inclusion."
  pushCom "Dans ce cas la démonstration commence par :"
  pushTac `(tactic|Montrons d'abord que $lS ⊆ $rS)

implement_endpoint (lang := fr) helpSinceSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité entre ensembles"
  pushCom "On peut la démontrer par réécriture avec la commande"
  pushTac `(tactic|Comme ?_ il suffit de montrer que ?_)
  flush
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $lS:term = $rS par?)
  flush
  pushCom "On peut aussi la démontrer par double inclusion."
  pushCom "Dans ce cas la démonstration commence par :"
  pushTac `(tactic|Montrons d'abord que $lS ⊆ $rS)

implement_endpoint (lang := fr) helpEqGoalSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité"
  pushCom "On peut la démontrer par réécriture avec la commande"
  pushTac `(tactic|On réécrit via ?_)
  flush
  pushCom "ou bien commencer un calcul par"
  pushTac `(tactic|Calc $lS:term = $rS par?)
  flush
  pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses avec"
  pushTac `(tactic|On combine [?_, ?_])

implement_endpoint (lang := fr) helpSinceEqGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité"
  pushCom "On peut la démontrer par réécriture "
  pushTac `(tactic|Comme ?_ on conclut que $goal)
  flush
  pushCom "ou bien commencer un calcul par"
  pushTac `(tactic|Calc $goal:term par?)

implement_endpoint (lang := fr) helpIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "Le but est une inégalité"
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $goal:term par?)
  pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
  pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
  pushCom "doivent s'enchaîner pour donner {rel}"
  flush
  pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses avec"
  pushTac `(tactic| On combine [?_, ?_])

implement_endpoint (lang := fr) helpSinceIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "Le but est une inégalité"
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $goal:term par?)
  pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
  pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
  pushCom "doivent s'enchaîner pour donner {rel}"
  flush
  pushCom "Si cette inégalité découle immédiatement d’une hypothèse on peut utiliser"
  pushTac `(tactic|Comme ?_ on conclut que $goal)
  pushCom "en remplaçant le point d’interrogation par l’énoncé de l’hypothèse"

implement_endpoint (lang := fr) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "Le but est l'appartenance de {← elem.fmt} à l'intersection de {← le.fmt} avec un autre ensemble."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Montrons d'abord que $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := fr) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "Le but est l'appartenance de {← elem.fmt} à la réunion de {← le.fmt} et {← re.fmt}."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Montrons que $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "ou bien par"
  pushTac `(tactic|Montrons que $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := fr) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "Pas d’idée."

implement_endpoint (lang := fr) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "Le but est l’inclusion {l} ⊆ {r}"
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Soit $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := fr) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "Le but est de montrer une contradiction."
  pushCom "On peut par exemple appliquer une hypothèse qui est une négation"
  pushCom "c'est à dire, par définition, de la forme P ⇒ False."

implement_endpoint (lang := fr) helpSinceFalseGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "Le but est de montrer une contradiction."
  pushCom "On peut par exemple appliquer une hypothèse qui est une négation"
  pushCom "c'est à dire, par définition, de la forme P ⇒ False."
  pushCom "On peut également combiner deux faits qui se contredise directement par :"
  pushTac `(tactic|Comme ?_ et ?_ on conclut que $goal)
  pushCom "en remplaçant les points d’interrogation par deux faits qui se contredisent directement et découlent immédiatement d’hypothèses."
  flush
  pushCom "On peut également invoquer un fait manifestement faux (comme par exemple `0 = 1`) qui découle directement des hypothèses :"
  pushTac `(tactic|Comme ?_ on conclut que $goal)
  pushCom "en remplaçant le points d’interrogation par ce fait manifestement faux."

implement_endpoint (lang := fr) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "Le but est une implication."
  pushCom "On peut débuter une démonstration par contraposition par :"
  pushTac `(tactic| On contrapose)

implement_endpoint (lang := fr) helpShowContrapositiveGoalSuggestion (stmt : Term) :
    SuggestionM Unit := do
  pushCom "Le but est une implication."
  pushCom "On peut débuter une démonstration par contraposition par :"
  pushTac `(tactic| Montrons la contraposée : $stmt)

implement_endpoint (lang := fr) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "On peut débuter une démonstration par l’absurde par :"
  pushTac `(tactic| Supposons par l'absurde $hyp:ident : $assum)

implement_endpoint (lang := fr) helpNegationGoalSuggestion (hyp : Ident) (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {p}, c’est à dire montrer que {p} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Supposons $hyp:ident : $assum)
  pushCom "Il restera à montrer une contradiction."

implement_endpoint (lang := fr) helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident):
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {l} = {r}, c’est à dire montrer que {l} = {r} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Supposons $Hyp:ident : $lS = $rS)
  pushCom "Il restera à montrer une contradiction."

set_option linter.unusedVariables false

setLang fr

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Aide
• Par h appliqué à n₀ en utilisant hn₀ on obtient (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  aide h
  apply h
  norm_num

/--
info: Aide
• Par h on obtient n tel que (n_pos : n > 0) et (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  aide h
  trivial

/--
info: Aide
• Par h on obtient ε tel que (ε_pos : ε > 0) et (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à n₀ on obtient (hn₀ : P n₀ → Q n₀)
• On applique h à n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  aide h
  exact h 2 h'

/--
info: Aide
• Par h appliqué à n₀ on obtient (hn₀ : P n₀)
• On applique h à n₀
• On conclut par h appliqué à 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  aide h
  exact h 2

/--
info: Aide
• Par h il suffit de montrer P 1
• On conclut par h appliqué à H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  aide h
  exact h h'

/--
info: Aide
• Par h appliqué à H on obtient H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  aide h
  trivial

/--
info: Aide
• Par h on obtient (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
• On réécrit via h
• On réécrit via ← h
• On réécrit via h dans l'hypothèse hyp
• On réécrit via ← h dans l'hypothèse hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  aide h
  trivial

/--
info: Aide
• Montrons d'abord que True
• Montrons d'abord que 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  aide
  exact ⟨trivial, rfl⟩

/--
info: Aide
• On discute en utilisant h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
• Montrons que True
• Montrons que False
-/
#guard_msgs in
example : True ∨ False := by
  aide
  left
  trivial

/-- info: Je n'ai rien à déclarer à propos de cette hypothèse. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  aide h
  trivial

-- TODO: Improve this help message (low priority since it is very rare)
/--
info: Aide
• (
  Montrons une contradiction
  On conclut par h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à H on obtient H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à k₀ en utilisant hk₀ on obtient n tel que (n_sup : n ≥ 3) et (hn : ∀ (l : ℕ), l - n = 0 → P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Par h appliqué à 2 en utilisant le_rfl on obtient n tel que (n_sup : n ≥ 3) et (hn : ∀ (l : ℕ), l - n = 0 → P l 2)
  trivial

/--
info: Aide
• Par h appliqué à k₀ et n₀ en utilisant H on obtient (h_1 : ∀ (l : ℕ), l - n₀ = 0 → P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à k₀ en utilisant hk₀ on obtient
  n_1 tel que (n_1_sup : n_1 ≥ 3) et (hn_1 : ∀ (l : ℕ), l - n = 0 → P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Par h appliqué à 2 en utilisant le_rfl on obtient n' tel que (n_sup : n' ≥ 3) et (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Aide
• Par h on obtient n tel que (n_sup : n ≥ 5) et (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à k₀ en utilisant hk₀ on obtient n tel que (n_sup : n ≥ 3) et (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  aide h
  trivial

/--
info: Aide
• Par h on obtient n tel que (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à k₀ on obtient n tel que (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

/--
info: Aide
• Par h appliqué à k₀ en utilisant hk₀ on obtient n tel que (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

/--
info: Aide
• Montrons que n₀ convient : P n₀ → True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  aide
  use 0
  tauto

/--
info: Aide
• Supposons hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  aide
  exact fun _ ↦ h

/--
info: Aide
• Soit n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  aide
  intros
  trivial

/--
info: Aide
• Soit n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  aide
  exact Nat.zero_le

/--
info: Aide
• Montrons que n₀ convient : 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  aide
  use 1
  exact Nat.zero_le 1

/--
info: Aide
• Montrons que n₀ convient : n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  aide
  use 1

/-- info: Je n'ai rien à déclarer à propos de cette hypothèse. -/
#guard_msgs in
example (h : Odd 3) : True := by
  aide h
  trivial

/--
info: Aide
• Soit x ∈ s
---
info: Aide
• Par h appliqué à x_1 en utilisant hx on obtient hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  aide
  Soit x ∈ s
  aide h
  exact h x_mem

/--
info: Aide
• Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Aide
• Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Aide
• Montrons d'abord que x ∈ t
---
info: Aide
• Montrons maintenant que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  aide
  Montrons d'abord que x ∈ t
  exact h'
  aide
  Montrons maintenant que x ∈ s
  exact h_1

/--
info: Aide
• On discute en utilisant h
---
info: Aide
• Montrons que x ∈ t
• Montrons que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  aide h
  On discute en utilisant h
  Supposons hyp : x ∈ s
  aide
  Montrons que x ∈ s
  exact hyp
  Supposons hyp : x ∈ t
  Montrons que x ∈ t
  exact  hyp

/--
info: Aide
• Supposons hyp : False
-/
#guard_msgs in
example : False → True := by
  aide
  simp

/-- info: Je n'ai rien à déclarer à propos de ce but. -/
#guard_msgs in
example : True := by
  aide
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Aide
• Supposons hyp : False
• On contrapose
-/
#guard_msgs in
example : False → True := by
  aide
  On contrapose
  simp

/-- info: Je n'ai rien à déclarer à propos de ce but. -/
#guard_msgs in
example : True := by
  aide
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Aide
• Supposons par l'absurde hyp : ¬True
-/
#guard_msgs in
example : True := by
  aide
  trivial

/--
info: Aide
• Par h on obtient x_1 tel que (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  aide h
  trivial

/--
info: Aide
• Par h on obtient x_1 tel que (x_1_dans : x_1 ∈ s) et (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  aide h
  trivial

/--
info: Aide
• Supposons hyp : P
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  aide
  exact h

/--
info: Aide
• Supposons hyp : x = y
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  aide
  exact h

allowProvingNegationsByContradiction

/--
info: Aide
• Supposons par l'absurde hyp : P
• Supposons hyp : P
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  aide
  exact h

/--
info: Aide
• Supposons par l'absurde hyp : x = y
• Supposons hyp : x = y
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  aide
  exact h

configureHelpProviders SinceHypHelp SinceGoalHelp helpShowContrapositiveGoal
/--
info: Aide
• Comme ∀ n > 0, P n et n₀ > 0 on obtient (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  aide h
  apply h
  norm_num

/--
info: Aide
• Comme ∃ n > 0, P n on obtient n tel que (n_pos : n > 0) et (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∃ ε > 0, P ε on obtient ε tel que (ε_pos : ε > 0) et (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∀ (n : ℕ), P n → Q n on obtient (hn₀ : P n₀ → Q n₀)
• On applique h à n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  aide h
  exact h 2 h'

/--
info: Aide
• Comme ∀ (n : ℕ), P n on obtient (hn₀ : P n₀)
• On applique h à n₀
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  aide h
  exact h 2

/--
info: Aide
• Comme P 1 → Q 2 il suffit de montrer que P 1
• Comme P 1 → Q 2 et P 1 on conclut que Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  aide h
  exact h h'

/--
info: Aide
• Comme P 1 → Q 2 et P 1 on obtient H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  aide h
  trivial

/--
info: Aide
• Comme P 1 et Q 2 on obtient (h_1 : P 1) et (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
• Comme (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l il suffit de montrer que ?_
• Comme (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l et ?_ on obtient hyp : ?_
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∀ (x y : ℝ), x ≤ y → f x ≤ f y on obtient (hx₀ : ∀ (y : ℝ), x₀ ≤ y → f x₀ ≤ f y)
• On applique h à x₀
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x y, x ≤ y → f x ≤ f y) (a b : ℝ) (h' : a ≤ b) : True := by
  Comme ∀ x y, x ≤ y → f x ≤ f y et a ≤ b on obtient H : f a ≤ f b
  aide h
  trivial

/--
info: Aide
• Comme ∀ x > 0, x = 1 → f x ≤ 0 et x₀ > 0 on obtient (hyp : x₀ = 1 → f x₀ ≤ 0)
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x > 0, x = 1 → f x ≤ 0) (a b : ℝ) (h' : a ≤ b) : True := by
  aide h
  trivial

/--
info: Aide
• Comme l - n = 0 → P l k et l - n = 0 on obtient H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k et k₀ ≥ 2 on obtient
  n tel que (n_sup : n ≥ 3) et (hn : ∀ (l : ℕ), l - n = 0 → P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Comme ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k et 2 ≥ 2 on obtient
    n tel que (n_sup : n ≥ 3) et (hn : ∀ (l : ℕ), l - n = 0 → P l 2)
  trivial

-- FIXME: completely broken case
/--
info: Aide
• Comme ∀ (k n : ℕ), n ≥ 3 → ∀ (l : ℕ), l - n = 0 → P l k et n ≥ 3 on obtient (h_1 : ∀ (l : ℕ), l - n₀ = 0 → P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

-- FIXME: completely broken case
/--
info: Aide
• Comme ∀ (k n : ℕ), n ≤ k → f n ≤ f k et n ≤ k on obtient (h_1 : f n₀ ≤ f k₀)
-/
#guard_msgs in
example (f : ℕ → ℕ) (h : ∀ k n, n ≤ k → f n ≤ f k) : True := by
  aide h
  trivial

-- FIXME: in hn_1, n is not replaced by n_1. This is an issue in
-- helpSinceForAllRelExistsRelSuggestion (or rather the function calling it)
/--
info: Aide
• Comme ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k et k₀ ≥ 2 on obtient
  n_1 tel que (n_1_sup : n_1 ≥ 3) et (hn_1 : ∀ (l : ℕ), l - n = 0 → P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Par h appliqué à 2 en utilisant le_rfl on obtient n' tel que (n_sup : n' ≥ 3) et (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Aide
• Comme ∃ n ≥ 5, P n on obtient n tel que (n_sup : n ≥ 5) et (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∀ k ≥ 2, ∃ n ≥ 3, P n k et k₀ ≥ 2 on obtient n tel que (n_sup : n ≥ 3) et (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∃ n, P n on obtient n tel que (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  aide h
  trivial

/--
info: Aide
• Comme ∀ (k : ℕ), ∃ n, P n k on obtient n tel que (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

/--
info: Aide
• On discute selon que P 1 ou Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
• Comme x ∈ s ∩ t on obtient (h_1 : x ∈ s) et (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Aide
• Comme x ∈ s ∩ t on obtient (h_1 : x ∈ s) et (h' : x ∈ t)
---
info: Aide
• Montrons d'abord que x ∈ t
---
info: Aide
• Montrons maintenant que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  aide
  Montrons d'abord que x ∈ t
  exact h'
  aide
  Montrons maintenant que x ∈ s
  exact h_1

/--
info: Aide
• On discute selon que x ∈ s ou x ∈ t
---
info: Aide
• Montrons que x ∈ t
• Montrons que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  aide h
  On discute en utilisant h
  Supposons hyp : x ∈ s
  aide
  Montrons que x ∈ s
  exact hyp
  Supposons hyp : x ∈ t
  Montrons que x ∈ t
  exact  hyp

/--
info: Aide
• Comme ε > 0 on conclut que ε / 2 > 0
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  aide h
  linarith

/--
info: Aide
• Calc
  ε / 2 > 0 par?
• Comme ?_ on conclut que ε / 2 > 0
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  aide
  Comme ε > 0 on conclut que ε / 2 > 0

/--
info: Aide
• Comme P ↔ Q il suffit de montrer que ?_
• Comme P ↔ Q et ?_ on obtient hyp : ?_
-/
#guard_msgs in
example (P Q : Prop) (h : P ↔ Q) (h' : P) : Q := by
  aide h
  Comme P ↔ Q il suffit de montrer que P
  exact h'

/--
info: Aide
• Comme A ⊆ B et x ∈ A on obtient hx : x ∈ B
-/
#guard_msgs in
example (A B : Set ℕ) (h : A ⊆ B) : True := by
  aide h
  trivial

/--
info: Aide
• Comme False on conclut que 0 = 1
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  aide h
  Comme False on conclut que 0 = 1

/--
info: Aide
• Comme ?_ et ?_ on conclut que False
• Comme ?_ on conclut que False
-/
#guard_msgs in
example (h : 0 = 1) : False := by
  aide
  Comme 0 = 1 on conclut que False

/--
info: Aide
• Calc
  a ≤ c par?
• Comme ?_ on conclut que a ≤ c
-/
#guard_msgs in
example (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  aide
  exact le_trans h h'

/--
info: Aide
• Supposons hyp : False
• Montrons la contraposée : ¬True → ¬False
-/
#guard_msgs in
example : False → True := by
  aide
  Montrons la contraposée : ¬True → ¬False
  simp
