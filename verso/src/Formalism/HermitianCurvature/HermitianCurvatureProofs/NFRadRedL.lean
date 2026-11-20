import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedR

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

variable {k r : ℕ}

def cinv (g : Q.Mx k r) : Q.Mx k r := (g + 1)⁻¹ * (g - 1)

/- English proof (translation)
Simplify using `[cinv]`.
-/
theorem cinv_one : cinv (1 : Q.Mx k r) = 0 := by
  simp [cinv]

/- English proof (translation)
Rewrite using `[cinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]`.
-/
theorem add_one_mul_cinv {g : Q.Mx k r} (hg : IsUnit (g + 1).det) : (g + 1) * cinv g = g - 1 := by
  rw [cinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[cinv, Matrix.mul_assoc, show (g - 1) * (g + 1) = (g + 1) * (g - 1) by noncomm_ring, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]`.
-/
theorem cinv_mul_add_one {g : Q.Mx k r} (hg : IsUnit (g + 1).det) : cinv g * (g + 1) = g - 1 := by
  rw [cinv, Matrix.mul_assoc, show (g - 1) * (g + 1) = (g + 1) * (g - 1) by noncomm_ring,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]

/- English proof (translation)
Establish `k1 : g₁ * (1 - cinv g₁) = 1 + cinv g₁`. Establish `h` using `add_one_mul_cinv h₁`. Rewrite `h` using `[add_mul, Matrix.one_mul]`. Rewrite using `[mul_sub, mul_one, eq_sub_of_add_eq h]`. Normalize the expressions using the abelian group laws.

Establish `k2 : g₂ * (1 - cinv g₁) = 1 + cinv g₁`. Establish `h` using `add_one_mul_cinv h₂`. Rewrite `h` using `[add_mul, Matrix.one_mul]`. Rewrite using `[he, mul_sub, mul_one, eq_sub_of_add_eq h]`. Normalize the expressions using the abelian group laws.

Establish `hL : ((1 / 2 : ℂ) • (g₁ + 1)) * (1 - cinv g₁) = 1`. Rewrite using `[Matrix.smul_mul, mul_sub, mul_one, add_one_mul_cinv h₁, show g₁ + 1 - (g₁ - 1) = (2 : ℂ) • (1 : Q.Mx k r) by rw [two_smul]; abel, smul_smul]`. Evaluate the numerical expressions. Establish `hR : (1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1)) = 1` using `mul_eq_one_comm.mp hL`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cinv_inj {g₁ g₂ : Q.Mx k r} (h₁ : IsUnit (g₁ + 1).det) (h₂ : IsUnit (g₂ + 1).det)
    (he : cinv g₁ = cinv g₂) : g₁ = g₂ := by
  have k1 : g₁ * (1 - cinv g₁) = 1 + cinv g₁ := by
    have h := add_one_mul_cinv h₁
    rw [add_mul, Matrix.one_mul] at h
    rw [mul_sub, mul_one, eq_sub_of_add_eq h]; abel
  have k2 : g₂ * (1 - cinv g₁) = 1 + cinv g₁ := by
    have h := add_one_mul_cinv h₂
    rw [add_mul, Matrix.one_mul] at h
    rw [he, mul_sub, mul_one, eq_sub_of_add_eq h]; abel
  have hL : ((1 / 2 : ℂ) • (g₁ + 1)) * (1 - cinv g₁) = 1 := by
    rw [Matrix.smul_mul, mul_sub, mul_one, add_one_mul_cinv h₁,
      show g₁ + 1 - (g₁ - 1) = (2 : ℂ) • (1 : Q.Mx k r) by rw [two_smul]; abel, smul_smul]
    norm_num
  have hR : (1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1)) = 1 := mul_eq_one_comm.mp hL
  calc g₁ = g₁ * ((1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1))) := by rw [hR, mul_one]
    _ = g₂ * ((1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1))) := by rw [← mul_assoc, k1, ← k2, mul_assoc]
    _ = g₂ := by rw [hR, mul_one]

/- English proof (translation)
Take `⟨hU, hfix, hz⟩` from `hg`. Establish `fixv : ∀ v, g *ᵥ v = v → cinv g *ᵥ v = 0`. Introduce `v hv`. Simplify using `only [cinv]`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self, Matrix.mulVec_zero]`.

Use `⟨⟨?_, fun a _ => ⟨fixv _ (hfix a).1, fixv _ (hfix a).2⟩⟩, fixv _ hz⟩` and prove the remaining obligations. Establish `hU' : gᴴ * Hpk k r * g = Hpk k r` using `hU`. Establish `hAH : IsUnit (g + 1)ᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact hu.star`. Establish `e1 : (g + 1) * (g + 1)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `e2 : ((g + 1)ᴴ)⁻¹ * (g + 1)ᴴ = 1` using `Matrix.nonsing_inv_mul _ hAH`.

Establish `hc : cinv g = (g - 1) * (g + 1)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `mid : (g - 1)ᴴ * Hpk k r * (g + 1) + (g + 1)ᴴ * Hpk k r * (g - 1) = 0`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]`. Establish `: (gᴴ - 1) * Hpk k r * (g + 1) + (gᴴ + 1) * Hpk k r * (g - 1) = (gᴴ * Hpk k r * g - Hpk k r) + (gᴴ * Hpk k r * g - Hpk k r)` using `by noncomm_ring`.

Rewrite using `[this, hU', sub_self, add_zero]`. Establish `t1 : ((g + 1)ᴴ)⁻¹ * ((g - 1)ᴴ * Hpk k r * (g + 1)) * (g + 1)⁻¹ = ((g + 1)ᴴ)⁻¹ * (g - 1)ᴴ * Hpk k r`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e1, Matrix.mul_one]`. Establish `t2 : ((g + 1)ᴴ)⁻¹ * ((g + 1)ᴴ * Hpk k r * (g - 1)) * (g + 1)⁻¹ = Hpk k r * ((g - 1) * (g + 1)⁻¹)`.

Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[e2, Matrix.one_mul]`. Rewrite using `[hc, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← t1, ← t2, ← add_mul, ← mul_add, mid, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem cinv_lie {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) (hu : IsUnit (g + 1).det) :
    InLieW k r z (cinv g) := by
  obtain ⟨hU, hfix, hz⟩ := hg
  have fixv : ∀ v, g *ᵥ v = v → cinv g *ᵥ v = 0 := by
    intro v hv
    simp only [cinv]
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self, Matrix.mulVec_zero]
  refine ⟨⟨?_, fun a _ => ⟨fixv _ (hfix a).1, fixv _ (hfix a).2⟩⟩, fixv _ hz⟩
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have hAH : IsUnit (g + 1)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have e1 : (g + 1) * (g + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e2 : ((g + 1)ᴴ)⁻¹ * (g + 1)ᴴ = 1 := Matrix.nonsing_inv_mul _ hAH
  have hc : cinv g = (g - 1) * (g + 1)⁻¹ := by
    calc cinv g = cinv g * ((g + 1) * (g + 1)⁻¹) := by rw [e1, mul_one]
      _ = (g - 1) * (g + 1)⁻¹ := by rw [← mul_assoc, cinv_mul_add_one hu]
  have mid : (g - 1)ᴴ * Hpk k r * (g + 1) + (g + 1)ᴴ * Hpk k r * (g - 1) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    have : (gᴴ - 1) * Hpk k r * (g + 1) + (gᴴ + 1) * Hpk k r * (g - 1) =
        (gᴴ * Hpk k r * g - Hpk k r) + (gᴴ * Hpk k r * g - Hpk k r) := by noncomm_ring
    rw [this, hU', sub_self, add_zero]
  have t1 : ((g + 1)ᴴ)⁻¹ * ((g - 1)ᴴ * Hpk k r * (g + 1)) * (g + 1)⁻¹ = ((g + 1)ᴴ)⁻¹ * (g - 1)ᴴ * Hpk k r := by
    simp only [Matrix.mul_assoc]; rw [e1, Matrix.mul_one]
  have t2 : ((g + 1)ᴴ)⁻¹ * ((g + 1)ᴴ * Hpk k r * (g - 1)) * (g + 1)⁻¹ = Hpk k r * ((g - 1) * (g + 1)⁻¹) := by
    simp only [← Matrix.mul_assoc]; rw [e2, Matrix.one_mul]
  rw [hc, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← t1, ← t2, ← add_mul, ← mul_add, mid,
    Matrix.mul_zero, Matrix.zero_mul]

end Formalism.FourierDecayAlt.P.NFRadRedL
