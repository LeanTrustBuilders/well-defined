import WellDefined.Obligations

/-!
# `#well_defined`: a declaration's obligations, in the editor

`#well_defined thm` lists the uses of definitions with a declared domain in `thm`'s statement, and
what became of each obligation. For a definition with a declared domain, `#well_defined d` lists
those in its body instead, under its domain. The tools produce the same analysis for a whole library, as the
dataset facet `welldefined`.
-/

open Lean Elab Command

namespace WellDefined

/-- `#well_defined thm`: the obligations of `thm`'s statement, one per use of a definition with a
declared domain. -/
syntax (name := wellDefinedCmd) "#well_defined " ident : command

@[command_elab wellDefinedCmd]
def elabWellDefined : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  -- a definition with a declared domain: its body; anything else: its statement
  let obs ← liftTermElabM do
    let a := Analyzer.new (← getEnv)
    if a.domains.contains n && (← getConstInfo n).isDefinition then a.bodyObligationsOf n
    else a.obligationsOf n
  if obs.isEmpty then
    logInfo m!"{n}: no use of a definition with a declared domain"
  else
    logInfo m!"{n}:{String.join (obs.toList.map (s!"\n  " ++ ·.line))}"

end WellDefined
