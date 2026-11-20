import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FX

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. A detailed English derivation is pending.
-/
theorem inertInSec : InertInSec := by
  intro E _ _ _ S hS w hw
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases h : u = w
  · exact h ▸ huS
  · exact absurd ⟨u, h, hu⟩ hw

end PositivityTheory.Rg.BcB.F.FX

end
