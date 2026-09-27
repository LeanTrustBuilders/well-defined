# WellDefined

The well-definedness analyzer of the [LeanTrustBuilders](https://github.com/LeanTrustBuilders)
suite: it checks statements against what their definitions are declared to mean. See
`well-definedness.md` in [the design notes](https://github.com/LeanTrustBuilders/design/tree/main/AI_initial_docs).

Depends on Lean core and [TrustAnnotations](https://github.com/LeanTrustBuilders/annotations), whose
attributes it reads. A project does not depend on it: the tools that analyze a project do. The
extractor runs it on a whole library (`trust-extract welldefined`), and a site shows the results.

## What it checks

A definition's author declares where it is meant to apply, with TrustAnnotations' `@[domain]`:

```lean
@[domain (0 < n) "the predecessor of 0 is 0, by convention"]
def pred' (n : Nat) : Nat := n - 1
```

A catalogue does the same for a library it cannot edit (`attribute [domain (Integrable f μ)]
MeasureTheory.integral`). Each application of such a definition in a statement then carries an
**obligation**: its arguments are in the domain, given what is in scope where the application
sits.

What is in scope is read as Event-B reads well-definedness conditions:
* the theorem's hypotheses, and hypotheses inside the statement (`∀ x, 0 < x → …`), for what
  follows them;
* the left side of `∧` on its right, and the negation of the left side of `∨` on its right;
* the condition of an `if` in its branches.

A variable bound inside the statement (`∫ x, Real.log (f x) ∂μ`) has no hypothesis about it, and
the report says the obligation is for every value of it.

A domain that is a conjunction gives one obligation per part, each with the parts before it in
scope. So for `condExp`, whose domain is `∃ hm : m ≤ m₀, SigmaFinite (μ.trim hm) ∧ Integrable f μ`,
the report says which part is left open.

Each obligation comes out as one of:

| status | meaning | example |
|---|---|---|
| `discharged` | proved from what is in scope, by a hypothesis or a discharger | `strong_law_ae`: `Integrable (X 0) μ`, by its hypothesis `hint` |
| `irrelevant` | the statement says the same whatever value the application takes: with the use replaced by `c`, `∀ c, F[c] ↔ F` is proved, `F` being the hypothesis or conclusion it sits in | `0 * pred' n = 0` |
| `refuted` | its negation is proved: the statement is about the value outside the domain | `integral_undef`, whose hypothesis is `¬Integrable f μ` |
| `open` | neither: what the statement leaves unsaid about the domain | `integral_neg : ∫ -f = -∫ f`, with no integrability |
| `unapplied` | the definition is used as a function, with too few arguments to state its domain | `Tendsto Real.log atTop atTop` |

`open` is not a verdict. In library lemmas a use outside the domain is often deliberate: `add_div`
needs no `c ≠ 0` because `x / 0 = 0`. It matters in the results a project puts forward, its
claims, where it is what the claim leaves unsaid.

## Dischargers

Tactics, named as text and parsed in the analyzed environment, so that one runs only if the
library imports it. The default list is `omega`, `infer_instance`, `positivity`, `fun_prop`,
`norm_num`, `simp_all`: the Mathlib ones are skipped for a project without Mathlib.

They know nothing of the facts particular to a domain: that a random variable in L² is integrable,
or a martingale's values. A catalogue that declares domains can define a tactic for them, and name
it as a discharger: the Mathlib catalogue's `mathlib_catalogue_discharger` is a `solve_by_elim` over
such lemmas. Each gets a budget of heartbeats per
obligation (2000, in the unit of `maxHeartbeats`: a hundredth of Lean's default). What is open
depends on them, so a report names the dischargers it used.

Proofs and instances inside a statement are not walked.

## Use

In a file, `#well_defined thm` lists the obligations of `thm`'s statement:

```
WellDefined.Test.nested:
  conclusion: pred' (pred' n), needs 0 < pred' n: open
  conclusion: pred' n, needs 0 < n: discharged by omega
```

From Lean, `(Analyzer.new env cfg).obligationsOf decl`, and `Obligation.asJson` for the rows of the
dataset facet `welldefined/1`.

## Not yet

* The *inside* obligation: under its declared domain, a definition's body stays inside the domains
  of what it uses, or the value there does not matter.
* Obligations for choice (`@[noncanonical]`) and for invariance under `@[up_to]` relations.
* Hypotheses under binders: `∑ i ∈ s, f i` does not bring `i ∈ s` in scope, nor does `∀ᵐ x ∂μ`
  bring anything about `x`.

## Tests

`lake build WellDefinedTest` runs the `#guard_msgs` checks in `WellDefined/Test`.
