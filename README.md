# Verbose Lean 4 (em português)

Esse projeto é uma tradução (quase que direta) do [verbose-lean](https://github.com/PatrickMassot/verbose-lean4), um projeto que provê ˋtacticsˋ e ˋcommandsˋ para o
[Lean](https://leanprover-community.github.io/) em uma linguagem natural controlada.

## To do

| **Traduzir as táticas** | 4/17 |
| ----------------------- | ---- |
| All.lean              | Ok |
| Assume.lean           | Ok |
| By.lean               |  |
| Calc.lean             |  |
| Claim.lean            |  |
| Common.lean           | Ok |
| ExampleLib.lean       |  |
| Examples.lean         |  |
| Fix.lean              | Ok |
| Help.lean             |  |
| Lets.lean             |  |
| Set.lean              |  |
| Since.lean            |  |
| Statements.lean       |  |
| Tactics.lean          |  |
| We.lean               |  |
| Wdigets.lean          |  |

## A few issues

- Algumas syntaxes sujam o contexto do Lean. Então, como eu preciso do `e` pra bastante coisa relacionada às táticas, eu acabo perdendo a possiblidade de nomear minhas variáveis `e : Expr`, por exemplo. Acho que isso não é um problema no inglês, mas achei bem chato no portguês. seria legal encontrar uma forma de resolver :(.

- Also, como o Verbose Lean ainda está sendo updateado com muita frequência, eu tô tentando ir atualizando as traduções e verificando diferenças entre versões. Se esse repositório estiver muito atrás do original, é por conta disso.
