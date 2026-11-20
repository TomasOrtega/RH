import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.SuperdiagSgnConj

open Finset

open scoped ComplexConjugate

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic PI.GGConvScalarW

/- English proof (translation)
Rewrite using `[← AddChar.map_neg_eq_inv, AddChar.map_neg_eq_conj]`.
-/
theorem addChar_inv_eq_conj {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (a : F) :
    (ψ₀ a)⁻¹ = conj (ψ₀ a) := by
  rw [← AddChar.map_neg_eq_inv, AddChar.map_neg_eq_conj]

/- English proof (translation)
Unfold `psiNat`. Distinguish the cases in `hu : IsUni k u`. Rewrite using `[if_pos (isUni_inv hu), if_pos hu]`. Rewrite using `[eq_inv_of_mul_eq_one_left (psiU_inv_mul ψ₀ hu)]`. Unfold `psiU`.

Conclude with `addChar_inv_eq_conj ψ₀ _`. Establish `hu' : ¬ IsUni k u⁻¹` using `fun h => hu (by simpa using isUni_inv h)`. Rewrite using `[if_neg hu', if_neg hu, map_zero]`.
-/
theorem psiNat_inv {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiNat ψ₀ u⁻¹ = conj (psiNat ψ₀ u) := by
  unfold psiNat
  by_cases hu : IsUni k u
  · rw [if_pos (isUni_inv hu), if_pos hu]
    rw [eq_inv_of_mul_eq_one_left (psiU_inv_mul ψ₀ hu)]
    unfold psiU
    exact addChar_inv_eq_conj ψ₀ _
  · have hu' : ¬ IsUni k u⁻¹ := fun h => hu (by simpa using isUni_inv h)
    rw [if_neg hu', if_neg hu, map_zero]

end PI.GGMatBoundW
