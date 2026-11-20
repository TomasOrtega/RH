import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

/- English proof (translation)
Introduce `p _ G P v`. Establish `hgu : IsUnit (G.gram v).det` using `isUnit_iff_ne_zero.mpr (G.gram_det v)`. Establish `hgg : G.gram v * (G.gram v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hgu`. Establish `hgg' : (G.gram v)⁻¹ * G.gram v = 1` using `Matrix.nonsing_inv_mul _ hgu`. Establish `hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹`.

Introduce `x`. Establish `e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v` using `G.psi_star v x`. Rewrite using `[e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]`. Establish `hshb : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C)`. Establish `h1 : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * sh G (P.β : G.C) = 1`.

Simplify using `only [sh]`. Rewrite using `[← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]`. Rewrite `h1` using `[P.sym]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, Units.mul_inv, mul_one]`.

Use `_ = _ := by rw [h1, one_mul]`. Establish `hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ = algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C)`. Apply `(Units.mul_right_inj (P.γ * P.β)).mp` to reduce the goal to its premises. Rewrite using `[Units.val_mul, ← Algebra.smul_def]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by`. Rewrite using `[P.sim, ← Algebra.smul_def]`. Simplify using `only [smul_mul_assoc]`. Use `_ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by`.

Rewrite using `[Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]`. Use `_ = _ := by rw [mul_smul_comm, mul_assoc]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))ᴴ = _`. Rewrite using `[conjTranspose_mul, (G.gram_herm v).eq, hH, hshb, mul_assoc, hgg', mul_one]`.

Establish `hb : IsUnit (G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))` using `(Units.isUnit _).map (G.psi v)`. Rewrite using `[det_mul]`. Conclude with `mul_ne_zero (G.gram_det v) ((Matrix.isUnit_iff_isUnit_det _).mp hb).ne_zero`. Rewrite using `[hH]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hgg', mul_one, map_mul, map_mul]`. Use `_ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by`. Rewrite using `[hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]`. Use `_ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]`.
-/
theorem pair_form_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G P v
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu

  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hshb : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * sh G (P.β : G.C) = 1 := by
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    rw [P.sym] at h1
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C)
        = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]

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
  refine ⟨?_, ?_, ?_⟩
  ·
    change (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))ᴴ = _
    rw [conjTranspose_mul, (G.gram_herm v).eq, hH, hshb, mul_assoc, hgg', mul_one]
  ·
    have hb : IsUnit (G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := (Units.isUnit _).map (G.psi v)
    rw [det_mul]
    exact mul_ne_zero (G.gram_det v) ((Matrix.isUnit_iff_isUnit_det _).mp hb).ne_zero
  ·
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

end GlobalTheory.LKMid
