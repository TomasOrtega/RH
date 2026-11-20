import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ClassCT
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

/- English proof (translation)
Rewrite `hy` using `[Matrix.det_fin_two]`. Establish `h0 : ((y 1 0 : ℂ) * Complex.I + y 1 1) ≠ 0`. Introduce `h`. Establish `h1` using `congrArg Complex.re h`. Establish `h2` using `congrArg Complex.im h`.

Simplify using `at h1 h2`. Rewrite `hy` using `[h1, h2]`. Simplify using `at hy`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Establish `hn` using `Complex.normSq_pos.mpr h0`.

Rewrite using `[Complex.div_im, ← sub_div]`. Use `div_pos ?_ hn` and prove the remaining obligations. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem mobius_upper_half_plane_im_pos (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) :
    ((y 1 0 : ℂ) * Complex.I + y 1 1) ≠ 0 ∧
    0 < (((y 0 0 : ℂ) * Complex.I + y 0 1) / ((y 1 0 : ℂ) * Complex.I + y 1 1)).im := by
  rw [Matrix.det_fin_two] at hy
  have h0 : ((y 1 0 : ℂ) * Complex.I + y 1 1) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    rw [h1, h2] at hy
    simp at hy
  refine ⟨h0, ?_⟩
  have hn := Complex.normSq_pos.mpr h0
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ hn
  simp
  linarith

/- English proof (translation)
Take `⟨h0, h1⟩` from `mobius_upper_half_plane_im_pos y hy`. Use `⟨((|y.det| ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((y 1 0 : ℂ) * Complex.I + y 1 1) ^ (-(k : ℤ)), ⟨_, h1⟩, fun F t => ?_⟩` and prove the remaining obligations. Establish `hd : (!![1, t; 0, 1] * y).det = y.det` using `by rw [Matrix.det_mul]; simp`. Establish `e10 : (!![1, t; 0, 1] * y) 1 0 = y 1 0` using `by simp [Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e11 : (!![1, t; 0, 1] * y) 1 1 = y 1 1` using `by simp [Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `e00 : (!![1, t; 0, 1] * y) 0 0 = y 0 0 + t * y 1 0` using `by simp [Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e01 : (!![1, t; 0, 1] * y) 0 1 = y 0 1 + t * y 1 1` using `by simp [Matrix.mul_apply, Fin.sum_univ_two]`. Unfold `nsl`. Rewrite using `[hd, e10, e11, e00, e01, sign_pos hy, UpperHalfPlane.coe_I]`. Use `congr 2`.

Rewrite using `[← ofComplex_apply (t +ᵥ _)]`. Use `congr 1`. Rewrite using `[coe_vadd]`. Use `show _ = (t : ℂ) + ((y 0 0 : ℂ) * Complex.I + y 0 1) / ((y 1 0 : ℂ) * Complex.I + y 1 1)`. Simplify using `only [SignType.coe_one]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nsl_shift (k : ℕ) (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) :
    ∃ (c : ℂ) (z : ℍ), ∀ (F : ℍ → ℂ) (t : ℝ),
      nsl k F (!![1, t; 0, 1] * y) UpperHalfPlane.I = c * F (t +ᵥ z) := by
  obtain ⟨h0, h1⟩ := mobius_upper_half_plane_im_pos y hy
  refine ⟨((|y.det| ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((y 1 0 : ℂ) * Complex.I + y 1 1) ^ (-(k : ℤ)), ⟨_, h1⟩, fun F t => ?_⟩
  have hd : (!![1, t; 0, 1] * y).det = y.det := by rw [Matrix.det_mul]; simp
  have e10 : (!![1, t; 0, 1] * y) 1 0 = y 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (!![1, t; 0, 1] * y) 1 1 = y 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 : (!![1, t; 0, 1] * y) 0 0 = y 0 0 + t * y 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (!![1, t; 0, 1] * y) 0 1 = y 0 1 + t * y 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold nsl
  rw [hd, e10, e11, e00, e01, sign_pos hy, UpperHalfPlane.coe_I]
  congr 2
  rw [← ofComplex_apply (t +ᵥ _)]
  congr 1
  rw [coe_vadd]
  show _ = (t : ℂ) + ((y 0 0 : ℂ) * Complex.I + y 0 1) / ((y 1 0 : ℂ) * Complex.I + y 1 1)
  simp only [SignType.coe_one]
  push_cast
  field_simp
  ring

/- English proof (translation)
Take `⟨c, z, hc⟩` from `nsl_shift k y hy`. Take `⟨N, hN, hp, hi⟩` from `classCT k M hM f γ z`. Establish `key : ∀ t : ℝ, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = c * nsl k f (toR γ) (t +ᵥ z)`. Introduce `t`. Rewrite using `[← (nslMul k f).1 _ _ (toR γ).det_ne_zero (by rw [Matrix.det_mul]; simpa using hy), hc]`.

Simplify using `only [key]`. Use `⟨N, hN, fun t => ?_, ?_⟩` and prove the remaining obligations. Conclude with `congrArg (c * ·) (hp t)`. Rewrite using `[intervalIntegral.integral_const_mul, hi, mul_zero]`.
-/
private theorem pos_case (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) :
    ∃ N : ℕ, 0 < N ∧
      Function.Periodic (fun t : ℝ => nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = 0 := by
  obtain ⟨c, z, hc⟩ := nsl_shift k y hy
  obtain ⟨N, hN, hp, hi⟩ := classCT k M hM f γ z
  have key : ∀ t : ℝ, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = c * nsl k f (toR γ) (t +ᵥ z) := by
    intro t
    rw [← (nslMul k f).1 _ _ (toR γ).det_ne_zero (by rw [Matrix.det_mul]; simpa using hy), hc]
  simp only [key]
  refine ⟨N, hN, fun t => ?_, ?_⟩
  · exact congrArg (c * ·) (hp t)
  · rw [intervalIntegral.integral_const_mul, hi, mul_zero]

private def epsQ : GL (Fin 2) ℚ := aff (-1) 0

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [toR, epsQ, eps, aff]`.
-/
private theorem toR_epsQ : (toR epsQ).val = eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toR, epsQ, eps, aff]

/- English proof (translation)
Break down `hy.lt_or_gt with hy | hy` into its components or cases. Establish `hy' : 0 < (eps * y).det`. Rewrite using `[Matrix.det_mul]`. Simplify using `[eps, hy]`. Take `⟨N, hN, hp, hi⟩` from `pos_case k M hM f (γ * epsQ) (eps * y) hy'`.

Use `set G : ℝ → ℂ := fun t : ℝ => nsl k f ((toR (γ * epsQ)).val * (!![1, t; 0, 1] * (eps * y))) UpperHalfPlane.I with hG`. Establish `key : ∀ t : ℝ, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = G (-t)`. Introduce `t`. Establish `: eps * (!![1, -t; 0, 1] * eps) = !![1, t; 0, 1]`. Simplify using `[eps]`.

Simplify using `only [hG, map_mul, Units.val_mul, toR_epsQ]`. Rewrite using `[← this]`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [key]`. Use `⟨N, hN, fun t => ?_, ?_⟩` and prove the remaining obligations.

Use `show G (-(t + N)) = G (-t)`. Rewrite using `[neg_add, ← sub_eq_add_neg]`. Conclude with `hp.sub_eq _`. Rewrite using `[intervalIntegral.integral_comp_neg G]`. Use `hp.intervalIntegral_add_eq (-(N : ℝ)) 0` as an intermediate fact.

Simplify using `only [neg_add_cancel, zero_add] at this`. Rewrite using `[neg_zero, this]`. Conclude with `hi`. Conclude with `pos_case k M hM f γ y hy`.
-/
private theorem all_case (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : y.det ≠ 0) :
    ∃ N : ℕ, 0 < N ∧
      Function.Periodic (fun t : ℝ => nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = 0 := by
  rcases hy.lt_or_gt with hy | hy
  · have hy' : 0 < (eps * y).det := by
      rw [Matrix.det_mul]
      simp [eps, hy]
    obtain ⟨N, hN, hp, hi⟩ := pos_case k M hM f (γ * epsQ) (eps * y) hy'
    set G : ℝ → ℂ := fun t : ℝ => nsl k f ((toR (γ * epsQ)).val * (!![1, t; 0, 1] * (eps * y))) UpperHalfPlane.I with hG
    have key : ∀ t : ℝ, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = G (-t) := by
      intro t
      have : eps * (!![1, -t; 0, 1] * eps) = !![1, t; 0, 1] := by
        simp [eps]
      simp only [hG, map_mul, Units.val_mul, toR_epsQ]
      rw [← this]
      simp only [Matrix.mul_assoc]
    simp only [key]
    refine ⟨N, hN, fun t => ?_, ?_⟩
    · show G (-(t + N)) = G (-t)
      rw [neg_add, ← sub_eq_add_neg]
      exact hp.sub_eq _
    · rw [intervalIntegral.integral_comp_neg G]
      have := hp.intervalIntegral_add_eq (-(N : ℝ)) 0
      simp only [neg_add_cancel, zero_add] at this
      rw [neg_zero, this]
      exact hi
  · exact pos_case k M hM f γ y hy

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af.Nf in
/- English proof (translation)
Introduce `k M hM f φ hφ g`. Take `⟨γ, h, u, hu, rfl⟩` from `decomp M hM g`. Establish `key : ∀ t : ℝ, φ (upR (aff 1 t) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u))) = nsl k f ((toR γ⁻¹).val * (!![1, t; 0, 1] * (toR γ * h).val)) UpperHalfPlane.I`. Introduce `t`. Establish `e : upR (aff 1 t) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)) = ratGL ℚ 2 γ * (upR (toR γ⁻¹ * (aff 1 t * (toR γ * h))) * finGL ℚ 2 u)`.

Rewrite using `[ratGL_eq, ← mul_assoc (upR (toR γ) * finGL ℚ 2 (toF γ)) (upR (toR γ⁻¹ * _)), mul_assoc (upR (toR γ)) _ (upR (toR γ⁻¹ * _)), ← upR_comm, ← mul_assoc (upR (toR γ)), ← map_mul, map_inv, mul_inv_cancel_left, ← mul_assoc _ (upR h), mul_assoc (upR (toR γ)) _ (upR h), ← upR_comm]`. Simplify using `only [map_mul, mul_assoc]`. Rewrite using `[e, hφ γ _ u hu]`. Both sides reduce to the same expression. Simplify using `only [key]`.

Conclude with `all_case k M hM f γ⁻¹ _ (toR γ * h).det_ne_zero`.
-/
theorem UpperTheory.V.Af.Nf.liftCT :
    UpperTheory.V.Af.Nf.LiftCT := by
  intro k M hM f φ hφ g
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
  have key : ∀ t : ℝ, φ (upR (aff 1 t) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u))) =
      nsl k f ((toR γ⁻¹).val * (!![1, t; 0, 1] * (toR γ * h).val)) UpperHalfPlane.I := by
    intro t
    have e : upR (aff 1 t) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)) =
        ratGL ℚ 2 γ * (upR (toR γ⁻¹ * (aff 1 t * (toR γ * h))) * finGL ℚ 2 u) := by
      rw [ratGL_eq, ← mul_assoc (upR (toR γ) * finGL ℚ 2 (toF γ)) (upR (toR γ⁻¹ * _)), mul_assoc (upR (toR γ)) _ (upR (toR γ⁻¹ * _)),
        ← upR_comm, ← mul_assoc (upR (toR γ)), ← map_mul, map_inv, mul_inv_cancel_left,
        ← mul_assoc _ (upR h), mul_assoc (upR (toR γ)) _ (upR h), ← upR_comm]
      simp only [map_mul, mul_assoc]
    rw [e, hφ γ _ u hu]
    rfl
  simp only [key]
  exact all_case k M hM f γ⁻¹ _ (toR γ * h).det_ne_zero
