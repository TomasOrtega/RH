import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBasisConstruction

def lieSubR (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := by
    intro X Y hX hY
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * _ + _ * X) + (Yᴴ * _ + _ * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by
    unfold B.inLie
    simp
  smul_mem' := by
    intro c X hX
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

end LieBasisConstruction

/- English proof (translation)
Introduce `k r`. Set `S` to `LieBasisConstruction.lieSubR k r`. Set `b` to `Module.finBasis ℝ S`. Set `L0 : (Fin (Module.finrank ℝ S) → ℝ) →ₗ[ℝ] B.Mat k r` to `S.subtype ∘ₗ b.equivFun.symm.toLinearMap`. Establish `hinj : LinearMap.ker L0 = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot]`. Conclude with `S.injective_subtype.comp b.equivFun.symm.injective`. Take `⟨M0, hM0⟩` from `L0.exists_leftInverse_of_injective hinj`. Establish `hML : ∀ y, M0 (L0 y) = y` using `fun y => LinearMap.congr_fun hM0 y`. Use `⟨Module.finrank ℝ S, LinearMap.toContinuousLinearMap L0, LinearMap.toContinuousLinearMap M0, fun x => (b.equivFun.symm x).2, fun x => hML x, fun X hX => ?_⟩` and prove the remaining obligations.

Establish `e : L0 (b.equivFun ⟨X, hX⟩) = X` using `by simp [L0]`. Use `show L0 (M0 X) = X`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lie_basis_holds : LieBasis := by
  intro k r
  let S := LieBasisConstruction.lieSubR k r
  let b := Module.finBasis ℝ S
  let L0 : (Fin (Module.finrank ℝ S) → ℝ) →ₗ[ℝ] B.Mat k r := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hinj : LinearMap.ker L0 = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact S.injective_subtype.comp b.equivFun.symm.injective
  obtain ⟨M0, hM0⟩ := L0.exists_leftInverse_of_injective hinj
  have hML : ∀ y, M0 (L0 y) = y := fun y => LinearMap.congr_fun hM0 y
  refine ⟨Module.finrank ℝ S, LinearMap.toContinuousLinearMap L0, LinearMap.toContinuousLinearMap M0,
    fun x => (b.equivFun.symm x).2, fun x => hML x, fun X hX => ?_⟩
  have e : L0 (b.equivFun ⟨X, hX⟩) = X := by simp [L0]
  show L0 (M0 X) = X
  calc L0 (M0 X) = L0 (M0 (L0 (b.equivFun ⟨X, hX⟩))) := by rw [e]
    _ = X := by rw [hML, e]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
