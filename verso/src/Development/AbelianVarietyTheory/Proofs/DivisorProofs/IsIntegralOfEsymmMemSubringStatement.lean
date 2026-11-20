import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.isIntegral_of_esymm_mem_subring : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by
  first | exact @GlobalTheory.QFam.isIntegral_of_esymm_mem | exact GlobalTheory.QFam.isIntegral_of_esymm_mem | (intros; apply GlobalTheory.QFam.isIntegral_of_esymm_mem <;> assumption)
