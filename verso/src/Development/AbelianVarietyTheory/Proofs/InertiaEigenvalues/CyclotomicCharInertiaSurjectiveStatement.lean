import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import ReciprocityTheory.GaloisValuations.Global
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCyclotomicCharInertiaSurjective.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.cyclotomicChar_inertia_surjective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ v : ℤ_[l]ˣ, ∃ σ ∈ Ine (F := ℚ) A, cycZ (F := ℚ) (Ω := Ω) l σ = v := by
  first | exact @GlobalTheory.CycInertia.cycZ_Ine_surjective | exact GlobalTheory.CycInertia.cycZ_Ine_surjective | (intros; apply GlobalTheory.CycInertia.cycZ_Ine_surjective <;> assumption)
