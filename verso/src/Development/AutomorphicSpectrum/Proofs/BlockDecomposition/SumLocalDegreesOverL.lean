import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles

/- English proof (translation)
Introduce `F _ _ l _ T hT`. Set `_ : Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}` to `Fintype.subtype T hT`. Rewrite using `[Finset.sum_subtype T hT]`. Conclude with `GlobalTheory.Proof.LocalDegreeSum.sum_locDeg F l`.
-/
theorem sum_locDeg_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime]
    (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) →
    ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  intro F _ _ l _ T hT
  let _ : Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} := Fintype.subtype T hT
  rw [Finset.sum_subtype T hT]
  exact GlobalTheory.Proof.LocalDegreeSum.sum_locDeg F l

end GlobalTheory.CompanionTheory.GreenbergWiles
