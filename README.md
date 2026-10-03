# WellDefined

A well-definedness analyzer for Lean: it checks statements against where their definitions are
declared to apply.

Depends on Lean core and [TrustAnnotations](https://github.com/LeanTrustBuilders/annotations), whose
attributes it reads. A project does not depend on it: the tools that analyze a project do, such as
the [extractor](https://github.com/LeanTrustBuilders/extractor) (`trust-extract welldefined`).

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

Binders bring something about the variable they bind, by a table (Mathlib's, by default):
* `∑ i ∈ s`, `∏ i ∈ s`, `s.sup f`, `s.inf f` and `s.indicator f` bring `i ∈ s`;
* `∫ x, f x ∂μ` and `∫⁻` need their body only almost everywhere, and `∀ᶠ x in l` and
  `Tendsto f l l'` only eventually along `l`. An obligation about such a variable becomes
  `∀ᵐ x ∂μ, …` or `∀ᶠ x in l, …`, with whatever the statement assumes about `x` inside it: a
  hypothesis `∀ᵐ x ∂μ, 0 < f x` discharges `∫ x, Real.log (f x) ∂μ`, and so does `∀ x, 0 < f x`.

Any other bound variable (`fun k => …`, `∑' i`) has no hypothesis about it, and the report says the
obligation is for every value of it.

A domain that is a conjunction gives one obligation per part, each with the parts before it in
scope. So for `condExp`, whose domain is `∃ hm : m ≤ m₀, SigmaFinite (μ.trim hm) ∧ Integrable f μ`,
the report says which part is left open.

Each obligation comes out as one of:

| status | meaning | example |
|---|---|---|
| `discharged` | proved from what is in scope, by a hypothesis or a discharger | `strong_law_ae`: `Integrable (X 0) μ`, by its hypothesis `hint` |
| `irrelevant` | where the domain fails, the statement says the same whatever value the application takes: with the use replaced by `c`, `∀ c, ¬domain → (F[c] ↔ F)` is proved, `F` being the hypothesis or conclusion it sits in | `0 * pred' n = 0` |
| `refuted` | its negation is proved: the statement is about the value outside the domain | `integral_undef`, whose hypothesis is `¬Integrable f μ` |
| `open` | neither: what the statement leaves unsaid about the domain | `integral_neg : ∫ -f = -∫ f`, with no integrability |
| `unapplied` | the definition is used as a function, with too few arguments to state its domain | `Tendsto Real.log atTop atTop` |

## Definitions' bodies

A definition with a declared domain carries the *inside* obligation: under its domain, each use in
its body is inside the domain of what it uses, or its value does not matter there. Irrelevance is
`∀ c, ¬domain → body[c] = body`: `n * pred' n` is fine at `n = 0`, where `pred'` is outside its
domain, because the product is `0` whatever `pred' 0` is. A definition by cases, or a recursive one,
is read through its equation lemmas, one case at a time, with the case's pattern in the domain:

```
WellDefined.Test.Bodies.countDown:
  body, case 2: countDown n, needs 0 < n: open
```

(`countDown (n + 1) = countDown n + 1` calls itself at `0`, outside its domain `0 < n`.) An `open`
or `refuted` obligation in a body is a definition that may rely on a junk value inside its own
domain; a `refuted` one does.

`open` is not a verdict. In library lemmas a use outside the domain is often deliberate: `add_div`
needs no `c ≠ 0` because `x / 0 = 0`. It matters in the results a project puts forward, its
claims, where it is what the claim leaves unsaid.

## Dischargers

Tactics, named as text and parsed in the analyzed environment, so that one runs only if the
library imports it. The default list is `omega`, `infer_instance`, `positivity`, `fun_prop`,
`norm_num`, `simp_all`: the Mathlib ones are skipped for a project without Mathlib.

They know nothing of the facts particular to a domain, such as that a random variable in L² is
integrable. A catalogue that declares domains can define a tactic for them (a `solve_by_elim` over
such lemmas, say) and name it as a discharger. Each gets a budget of heartbeats per obligation
(10000, in the unit of `maxHeartbeats`). What is open depends on them, so a report names the
dischargers it used.

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

## Limits

* The obligations are those of declared domains only: a definition with no `@[domain]` has none, and
  `@[up_to]` relations give no obligation.
* Only the binders of the table bring a hypothesis, and only membership or a filter.

## Versions

`main` is on the Lean toolchain of Mathlib's master. Every hour, the workflow Follow Mathlib's
toolchain checks: when Mathlib has moved, it keeps the old toolchain on a branch
`lean-v<toolchain>`, moves `main` to the new one once it builds with its tests, after TrustAnnotations has moved, and tags it
`v<toolchain>`. A build that fails opens an issue labelled `toolchain` instead. The branches of older
toolchains get no further changes.

## Tests

`lake build WellDefinedTest` runs the `#guard_msgs` checks in `WellDefined/Test`.
