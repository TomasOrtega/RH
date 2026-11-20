import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedRootRealSignatureOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

/- English proof (translation)
Establish `hgu : IsUnit (G.gram v).det` using `isUnit_iff_ne_zero.mpr (G.gram_det v)`. Establish `hgg : G.gram v * (G.gram v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hgu`. Establish `hgg' : (G.gram v)⁻¹ * G.gram v = 1` using `Matrix.nonsing_inv_mul _ hgu`. Establish `hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹`. Introduce `x`.

Establish `e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v` using `G.psi_star v x`. Rewrite using `[e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]`. Establish `hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ = algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C)`. Apply `(Units.mul_right_inj (P.γ * P.β)).mp` to reduce the goal to its premises. Rewrite using `[Units.val_mul, ← Algebra.smul_def]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by`. Rewrite using `[P.sim, ← Algebra.smul_def]`. Simplify using `only [smul_mul_assoc]`.

Use `_ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by`. Rewrite using `[Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]`. Use `_ = _ := by rw [mul_smul_comm, mul_assoc]`. Rewrite using `[hH]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hgg', mul_one, map_mul, map_mul]`. Use `_ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by`. Rewrite using `[hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]`. Use `_ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]`.
-/
theorem DPair.form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) :
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v P.γ
      = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKDef
