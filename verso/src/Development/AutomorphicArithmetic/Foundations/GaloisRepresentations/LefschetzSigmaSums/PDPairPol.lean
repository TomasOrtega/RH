import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian

open UpperTheory.Gal.LocalSmoothExtension

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Use `set a : G.C := algebraMap ℚ G.C s with ha`. Establish `hcomm : ∀ x : G.C, a * x = x * a` using `fun x => Algebra.commutes s x`. Establish `hsh : sh G (u : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β)`. Rewrite using `[← hy]`. Simplify using `[mul_assoc]`.

Establish `key : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C) = a * ((β⁻¹ : G.Cˣ) : G.C)`. Rewrite using `[hsh]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[mul_assoc]`. Use `_ = ((β⁻¹ : G.Cˣ) : G.C) * (((u⁻¹ : G.Cˣ) : G.C) * (u : G.C)) * a := by`.

Rewrite using `[hcomm]`. Simplify using `only [mul_assoc]`. Use `_ = a * ((β⁻¹ : G.Cˣ) : G.C) := by`. Rewrite using `[hcomm]`. Simplify using the standard rewrite rules.

Establish `hpa : G.psi v a = (s : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ)`. Rewrite using `[ha, IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]`. Establish `hΓ : G.gram v * (G.gram v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v))`.

Establish `hUΓ : (G.psi v (u : G.C))ᴴ * G.gram v = G.gram v * G.psi v (sh G (u : G.C))`. Rewrite using `[show sh G (u : G.C) = MulOpposite.unop (G.star (u : G.C)) from rfl, G.psi_star]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hΓ, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_mul, ← Matrix.mul_assoc, hUΓ]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by`. Rewrite using `[key, map_mul, hpa, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]`.
-/
private theorem sim_herm {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β u : G.Cˣ) (s : ℚ)
    (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) :
    (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
      (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
  set a : G.C := algebraMap ℚ G.C s with ha
  have hcomm : ∀ x : G.C, a * x = x * a := fun x => Algebra.commutes s x
  have hsh : sh G (u : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) := by
    rw [← hy]
    simp [mul_assoc]
  have key : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C) = a * ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [hsh]
    calc ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C)
        = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * (u : G.C)) := by
          simp [mul_assoc]
      _ = ((β⁻¹ : G.Cˣ) : G.C) * (((u⁻¹ : G.Cˣ) : G.C) * (u : G.C)) * a := by
          rw [hcomm]; simp only [mul_assoc]
      _ = a * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [hcomm]; simp
  have hpa : G.psi v a = (s : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [ha, IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hΓ : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v))
  have hUΓ : (G.psi v (u : G.C))ᴴ * G.gram v = G.gram v * G.psi v (sh G (u : G.C)) := by
    rw [show sh G (u : G.C) = MulOpposite.unop (G.star (u : G.C)) from rfl, G.psi_star]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hΓ, Matrix.one_mul]
  calc (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C))) := by
        rw [map_mul, map_mul, ← Matrix.mul_assoc, hUΓ]
        simp only [Matrix.mul_assoc]
    _ = (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [key, map_mul, hpa, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

/- English proof (translation)
Introduce `h`. Establish `hint : IsIntegral F (g : A)` using `Algebra.IsIntegral.isIntegral _`. Take `⟨q, hq⟩` from `Polynomial.X_dvd_iff.mpr h`. Establish `hmon : (minpoly F (g : A)).Monic` using `minpoly.monic hint`. Establish `hqmon : q.Monic`.

Rewrite `hmon` using `[hq]`. Conclude with `Polynomial.monic_X.of_mul_monic_left hmon`. Establish `haeval : Polynomial.aeval (g : A) q = 0`. Establish `h0` using `minpoly.aeval F (g : A)`. Rewrite `h0` using `[hq, map_mul, Polynomial.aeval_X]`.

Use `congrArg (fun y => ((g⁻¹ : Aˣ) : A) * y) h0` as an intermediate fact. Simplify `this` using `[← mul_assoc]`. Establish `hle` using `minpoly.min F (g : A) hqmon haeval`. Rewrite `hle` using `[hq, Polynomial.degree_mul, Polynomial.degree_X]`. Establish `hq0 : q ≠ 0` using `hqmon.ne_zero`.

Rewrite `hle` using `[Polynomial.degree_eq_natDegree hq0]`. Normalize the coercions in `at hle`. Use linear arithmetic over natural numbers and integers.
-/
private theorem coeff_zero_ne {F A : Type} [Field F] [Ring A] [Algebra F A] [Algebra.IsIntegral F A] [Nontrivial A]
    (g : Aˣ) : (minpoly F (g : A)).coeff 0 ≠ 0 := by
  intro h
  have hint : IsIntegral F (g : A) := Algebra.IsIntegral.isIntegral _
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h
  have hmon : (minpoly F (g : A)).Monic := minpoly.monic hint
  have hqmon : q.Monic := by
    rw [hq] at hmon
    exact Polynomial.monic_X.of_mul_monic_left hmon
  have haeval : Polynomial.aeval (g : A) q = 0 := by
    have h0 := minpoly.aeval F (g : A)
    rw [hq, map_mul, Polynomial.aeval_X] at h0
    have := congrArg (fun y => ((g⁻¹ : Aˣ) : A) * y) h0
    simpa [← mul_assoc] using this
  have hle := minpoly.min F (g : A) hqmon haeval
  rw [hq, Polynomial.degree_mul, Polynomial.degree_X] at hle
  have hq0 : q ≠ 0 := hqmon.ne_zero
  rw [Polynomial.degree_eq_natDegree hq0] at hle
  norm_cast at hle
  omega

/- English proof (translation)
Introduce `p _ G P v`. Use `⟨coeff_zero_ne (F := G.F) (A := G.C) P.γ, (P.c : ℚ), ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hint : IsIntegral G.F (P.γ : G.C)` using `Algebra.IsIntegral.isIntegral _`. Establish `hev : eval₂ v.embedding z (minpoly G.F (P.γ : G.C)) = 0` using `(Polynomial.mem_roots_map (minpoly.ne_zero hint)).mp hz`.

Take `⟨x, hx, hMx⟩` from `PolyArch.roots_eig_any p G v (P.γ : G.C) z hev`. Establish `hsim` using `sim_herm G v P.β P.γ (P.c : ℚ) P.sim`. Establish `hform` using `GlobalTheory.EigenvalueNormSignature.form_mulVec (G.psi v (P.γ : G.C)) (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x`. Rewrite `hform` using `[hsim, hMx]`. Establish `hQ : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x ≠ 0`.

Introduce `h0`. Take `⟨h1, h2⟩` from `P.posR v x hx`. Rewrite `h1`, `h2` using `[h0]`. Simplify using `at h1 h2`. Conclude with `h1 h2`.

Simplify using `only [Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hform`. Apply `mul_right_cancel₀ hQ` to reduce the goal to its premises. Rewrite `hform` using `[Complex.star_def]`. Move the coercions through the operations in `at hform ⊢`. Take the linear combination `hform`.
-/
theorem dPairPol_of :
    DPairPol := by
  intro p _ G P v
  refine ⟨coeff_zero_ne (F := G.F) (A := G.C) P.γ, (P.c : ℚ), ?_⟩
  intro z hz
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hev : eval₂ v.embedding z (minpoly G.F (P.γ : G.C)) = 0 :=
    (Polynomial.mem_roots_map (minpoly.ne_zero hint)).mp hz
  obtain ⟨x, hx, hMx⟩ := PolyArch.roots_eig_any p G v (P.γ : G.C) z hev
  have hsim := sim_herm G v P.β P.γ (P.c : ℚ) P.sim
  have hform := GlobalTheory.EigenvalueNormSignature.form_mulVec (G.psi v (P.γ : G.C))
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x
  rw [hsim, hMx] at hform
  have hQ : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := P.posR v x hx
    rw [h0] at h1 h2
    simp at h1 h2
    exact h1 h2
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hform
  apply mul_right_cancel₀ hQ
  rw [Complex.star_def] at hform
  push_cast at hform ⊢
  linear_combination hform

end UpperTheory.Gal.LocalSmoothExtension
