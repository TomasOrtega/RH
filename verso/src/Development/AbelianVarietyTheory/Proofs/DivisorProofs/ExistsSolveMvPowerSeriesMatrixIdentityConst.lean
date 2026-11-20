import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

open Matrix

/- English proof (translation)
Introduce `n R _ J hJ b`. Set `M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) R)` to `Matrix.of J`. Establish `hM : (MvPowerSeries.constantCoeff (σ` using `Fin n) (R := R)).mapMatrix M = 1 := by`. Use extensionality with `i j`. Simplify using `[M, Matrix.one_apply, hJ]`.

Establish `hdet : IsUnit M.det`. Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hM, Matrix.det_one]`. Conclude with `isUnit_one`. Use `⟨M⁻¹ *ᵥ b, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (Matrix.mulVec_mulVec b M M⁻¹) i`.

Rewrite `h` using `[Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Rewrite using `[← h]`. Simplify using `only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`.
-/
theorem powerSeries_matrix_solve : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  intro n R _ J hJ b
  let M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) R) := Matrix.of J
  have hM : (MvPowerSeries.constantCoeff (σ := Fin n) (R := R)).mapMatrix M = 1 := by
    ext i j
    simp [M, Matrix.one_apply, hJ]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hM, Matrix.det_one]
    exact isUnit_one
  refine ⟨M⁻¹ *ᵥ b, fun i => ?_⟩
  have h := congrFun (Matrix.mulVec_mulVec b M M⁻¹) i
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end GlobalTheory
