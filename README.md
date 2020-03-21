# sequents

A blatant ripoff of [Logitext], with variants implementing the propositional
fragments of systems LK, LJ, two-sided classical linear logic, and one-sided
classical linear logic (both forms of CLL as presented [here][CLLCalc], except
that the one-sided version only allows the Axiom rule to be applied to atoms
(this is currently a bug, not a feature 🙁)). Try it out: [LK], [LJ], [CLL],
[RCLL].

NOTE: The {,R}CLL variant actually supports second-order quantifiers
(basically, System F); need to document this.

[Logitext]: http://logitext.mit.edu/main
[CLLCalc]: http://llwiki.ens-lyon.fr/mediawiki/index.php/Sequent_calculus
[LK]:   https://sarahzrf.github.io/sequents/?system=lk
[LJ]:   https://sarahzrf.github.io/sequents/?system=lj
[CLL]:  https://sarahzrf.github.io/sequents/?system=cll
[RCLL]: https://sarahzrf.github.io/sequents/?system=rcll

## Usage
### Interaction
Just like in Logitext, the fundamental interaction model is that you click on a
formula to apply a rule introducing it. To apply the Axiom rule, left-click the
turnstile (except in one-sided CLL, where you must click on the non-negated
atom); to reset a subproof, right-click the turnstile.

There are some special cases:

- To apply contraction in LK or LJ, right-click the formula.
- To apply weakening in LK or LJ, middle-click the formula or left-click it
  while holding Ctrl.
- When there is more than one applicable logical rule:
  * If the connective is `∧`, `∨`, `&`, or `⊕`, click either the left or right
    subformula to choose between the two applicable rules.
  * If the connective is an exponential, right click the formula to apply
    contraction, click the connective itself to apply weakening, and click the
    operand to apply dereliction.
- When the rule requires the side formulas to be split between the premises
  (e.g., the left rule for `→`), the conclusion will enter a mode where
  clicking on side formulas toggles which premise they are distributed to. To
  choose a new formula to introduce, you will need to explicitly cancel this
  mode first by right-clicking the turnstile.

### Syntax for entering goals
Goals take the form `A, ..., B |- C, ..., D` where `A, B, C, D` are formulas;
empty lists are allowed on either side. You can also enter just `A` for `|- A`.
Any sequence of alphanumeric characters can be an atomic formula. For LK and
LJ, the connectives are `->`, `/\`, `\/`, and `~` (negation), from low to high
precedence. For CLL, the connectives are `-o` (implication), `+`, `&`
(additives), `@`, `*` (multiplicatives), `~`, `!`, and `?`, from low to high
precedence. CLL also allows units `1`, `F` (multiplicatives), `0`, and `T`
(additives), which will not be parsed as atomic formulas.

The parser is a bit janky, and you may have to use more parentheses than you
should really need to (e.g., `~~P` needs to be `~(~P)`). Maybe I'll improve it
someday...

