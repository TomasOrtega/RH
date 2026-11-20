import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnitNormAllOfCore
import Formalism.FormalDegreeBessel.FinalBF

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `hinv : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)`. Establish `hinv' : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)`. Establish `hJ` using `hP.1.2`. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Use `show (P * g * P⁻¹)ᴴ * _ * (P * g * P⁻¹) = _`.

Establish `e1 : (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e1, hJ, hg', ← hJ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Formalism.REAL.Jm ε := by rw [hinv']; simp`.
-/
theorem conj_mem_UJ {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hJ := hP.1.2
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * _ * (P * g * P⁻¹) = _
  have e1 : (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) =
      (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg', ← hJ]
  calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hinv']; simp

/- English proof (translation)
Establish `hinv : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) (g : Mx k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [hinv]; simp

/- English proof (translation)
Take `⟨P, hP, hDS⟩` from `hσ`. Take `⟨-, -, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, -⟩` from `hDS`. Establish `hinv : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `h1` using `[hinv]`.

Introduce `a ha b hb`. Establish `h` using `hmul _ (conj_mem_UJ hP ha) _ (conj_mem_UJ hP hb)`. Establish `e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [e, conj_back hP] at h`.

Conclude with `h`. Introduce `a ha v`. Establish `h` using `hnorm _ (conj_mem_UJ hP ha) v`. Simplify using `only [conj_back hP] at h`. Conclude with `h`.

Introduce `v`. Establish `hc : Continuous (fun g : Mx k r => P * g * P⁻¹)` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Establish `h` using `(hcont v).comp hc.continuousOn (fun g hg => conj_mem_UJ hP hg)`. Use `h.congr (fun g _ => ?_)` and prove the remaining obligations. Use `show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v`.

Rewrite using `[conj_back hP]`.
-/
theorem ds_rep {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
      (∀ a ∈ UH (Hpk k r), ∀ v : H, ‖σ a v‖ = ‖v‖) ∧
      ∀ v : H, ContinuousOn (fun g => σ g v) (UH (Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, -⟩ := hDS
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hinv] using h1
  · intro a ha b hb
    have h := hmul _ (conj_mem_UJ hP ha) _ (conj_mem_UJ hP hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (a * b) * P⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    simp only [e, conj_back hP] at h
    exact h
  · intro a ha v
    have h := hnorm _ (conj_mem_UJ hP ha) v
    simp only [conj_back hP] at h
    exact h
  · intro v
    have hc : Continuous (fun g : Mx k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h := (hcont v).comp hc.continuousOn (fun g hg => conj_mem_UJ hP hg)
    refine h.congr (fun g _ => ?_)
    show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
    rw [conj_back hP]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end PI.WBL.FSW
