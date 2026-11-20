import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

/- English proof (translation)
Introduce `p _ G v β _ hR`. Take `⟨z, hz⟩` from `hR`. Establish `hc : ∃ Z : GL (Fin G.n) ℂ, herm G v β = (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ)`. Use `⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩` and prove the remaining obligations. Use `set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm`.

Express the relevant statement in the definitionally equal form `G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm`. Establish `hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C)`. Express the relevant statement in the definitionally equal form `G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _`. Rewrite using `[psiR_tmul, one_smul]`. Establish `h1` using `congrArg (G.psiR v) hz`.

Rewrite `h1` using `[map_mul, map_mul, psiR_starT, hb]`. Simplify using `only [Units.val_one, map_one] at h1`. Rewrite `h1` using `[← hZm]`. Establish `hg : IsUnit (G.gram v).det` using `isUnit_iff_ne_zero.2 (G.gram_det v)`. Use `set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)`.

Establish `hMb : M * G.psi v (β : G.C) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1`. Use `mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 : Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc]`.

Establish `h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3]`. Simplify using `only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]`. Take `⟨Z, hZ⟩` from `hc`.

Use `⟨?_, ?_, Z, hZ⟩` and prove the remaining obligations. Rewrite using `[hZ]`. Conclude with `isHermitian_conjTranspose_mul_mul _ (G.gram_herm v)`. Rewrite using `[hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `hZd : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0` using `(Matrix.isUnit_det_of_left_inverse (show ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * Z = 1 by`.

Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one])).ne_zero`. Conclude with `mul_ne_zero (mul_ne_zero (star_ne_zero.2 hZd) (G.gram_det v)) hZd`.
-/
theorem herm_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → (herm G v β).IsHermitian ∧ (herm G v β).det ≠ 0 ∧
      ∃ Z : GL (Fin G.n) ℂ, herm G v β =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G v β _ hR
  obtain ⟨z, hz⟩ := hR
  have hc : ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
    set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
    change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
    have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
      change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
      rw [psiR_tmul, one_smul]
    have h1 := congrArg (G.psiR v) hz
    rw [map_mul, map_mul, psiR_starT, hb] at h1
    simp only [Units.val_one, map_one] at h1
    rw [← hZm] at h1
    have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
    set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
    have hMb : M * G.psi v (β : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
      have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
        Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
      simpa [Matrix.mul_assoc] using this
    have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
      calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
    rw [h3]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ := hc
  refine ⟨?_, ?_, Z, hZ⟩
  · rw [hZ]
    exact isHermitian_conjTranspose_mul_mul _ (G.gram_herm v)
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hZd : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse
      (show ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * Z = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one])).ne_zero
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hZd) (G.gram_det v)) hZd

end GlobalTheory.LKCx
