import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

noncomputable section
open Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval.GaussRep

/- English proof (translation)
Use `continuous_pi fun r => continuous_pi fun c => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases c <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, blk] <;> fun_prop`.
-/
lemma continuous_rows (h : M22) :
    Continuous fun z : Fin 2 → ℝ => (Matrix.of.symm (Matrix.of h * blk z) : M23) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, blk] <;> fun_prop

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_` and prove the remaining obligations. Establish `h1 : (Matrix.of h).mulVec z r = (Matrix.of.symm (Matrix.of h * blk z) : M23) r 2`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, blk]`. Rewrite using `[h1]`. Conclude with `(norm_le_pi_norm _ (2 : Fin 3)).trans (norm_le_pi_norm _ r)`.
-/
lemma norm_mulVec_le (h : M22) (z : Fin 2 → ℝ) :
    ‖(Matrix.of h).mulVec z‖ ≤ ‖(Matrix.of.symm (Matrix.of h * blk z) : M23)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : (Matrix.of h).mulVec z r = (Matrix.of.symm (Matrix.of h * blk z) : M23) r 2 := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, blk]
  rw [h1]
  exact (norm_le_pi_norm _ (2 : Fin 3)).trans (norm_le_pi_norm _ r)

/- English proof (translation)
Establish `hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `z hz`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hd hz`. Take `⟨K, hKpos, hK⟩` from `LinearMap.exists_antilipschitzWith _ hker`.

Establish `hz : ∀ z : Fin 2 → ℝ, ‖z‖ ≤ (K : ℝ) * ‖(Matrix.of.symm (Matrix.of h * blk z) : M23)‖`. Introduce `z`. Establish `h1` using `hK.le_mul_dist z 0`. Simplify using `only [dist_zero_right, map_zero, Matrix.mulVecLin_apply] at h1`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left (norm_mulVec_le h z) K.2)`.

Choose the witnesses or unpack the hypotheses as in `⟨C, hC⟩ : ∃ C : ℝ, ∀ X : M23, (1 + ‖X‖) ^ 3 * ‖Φ X‖ ≤ C := by`. Use `⟨2 ^ 3 * (Finset.Iic ((3, 0) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ, fun X => ?_⟩` and prove the remaining obligations. Use `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0) le_rfl le_rfl Φ X` as an intermediate fact. Simplify `this` using `[norm_iteratedFDeriv_zero]`. Establish `hmaj : Integrable (fun z : Fin 2 → ℝ => (1 + (K : ℝ)) ^ 3 * C * (1 + ‖z‖) ^ (-(3 : ℝ)))`.

Use `(integrable_one_add_norm ?_).const_mul _` and prove the remaining obligations. Simplify using `only [Module.finrank_fin_fun]`. Evaluate the numerical expressions. Use `hmaj.mono' (Φ.continuous.comp (continuous_rows h)).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `set X : M23 := Matrix.of.symm (Matrix.of h * blk z) with hX`.

Establish `hpos : (0 : ℝ) < 1 + ‖z‖` using `by positivity`. Establish `hK0 : (0 : ℝ) ≤ K` using `K.2`. Establish `hle : 1 + ‖z‖ ≤ (1 + (K : ℝ)) * (1 + ‖X‖)`. Use `hz z` as an intermediate fact. Establish `hX0 : 0 ≤ ‖X‖` using `norm_nonneg _`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hpow : (1 + ‖z‖) ^ 3 ≤ (1 + (K : ℝ)) ^ 3 * (1 + ‖X‖) ^ 3`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hpos.le hle 3`. Establish `hmul : ‖Φ X‖ * (1 + ‖z‖) ^ 3 ≤ (1 + (K : ℝ)) ^ 3 * C`.

Combine the equalities or inequalities in the displayed calculation. Establish `hr : (1 + ‖z‖) ^ (-(3 : ℝ)) = ((1 + ‖z‖) ^ 3)⁻¹`. Rewrite using `[Real.rpow_neg hpos.le]`. Use `norm_cast`. Rewrite using `[hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`.

Conclude with `hmul`.
-/
lemma integrable_rows (Φ : Sw) (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    Integrable (fun z : Fin 2 → ℝ => Φ (Matrix.of.symm (Matrix.of h * blk z))) := by
  have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    exact Matrix.eq_zero_of_mulVec_eq_zero hd hz
  obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith _ hker
  have hz : ∀ z : Fin 2 → ℝ,
      ‖z‖ ≤ (K : ℝ) * ‖(Matrix.of.symm (Matrix.of h * blk z) : M23)‖ := by
    intro z
    have h1 := hK.le_mul_dist z 0
    simp only [dist_zero_right, map_zero, Matrix.mulVecLin_apply] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_mulVec_le h z) K.2)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ X : M23, (1 + ‖X‖) ^ 3 * ‖Φ X‖ ≤ C := by
    refine ⟨2 ^ 3 * (Finset.Iic ((3, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ, fun X => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0))
      (k := 3) (n := 0) le_rfl le_rfl Φ X
    simpa [norm_iteratedFDeriv_zero] using this
  have hmaj : Integrable (fun z : Fin 2 → ℝ => (1 + (K : ℝ)) ^ 3 * C * (1 + ‖z‖) ^ (-(3 : ℝ))) := by
    refine (integrable_one_add_norm ?_).const_mul _
    simp only [Module.finrank_fin_fun]
    norm_num
  refine hmaj.mono' (Φ.continuous.comp (continuous_rows h)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  set X : M23 := Matrix.of.symm (Matrix.of h * blk z) with hX
  have hpos : (0 : ℝ) < 1 + ‖z‖ := by positivity
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hle : 1 + ‖z‖ ≤ (1 + (K : ℝ)) * (1 + ‖X‖) := by
    have := hz z
    have hX0 : 0 ≤ ‖X‖ := norm_nonneg _
    nlinarith
  have hpow : (1 + ‖z‖) ^ 3 ≤ (1 + (K : ℝ)) ^ 3 * (1 + ‖X‖) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hpos.le hle 3
  have hmul : ‖Φ X‖ * (1 + ‖z‖) ^ 3 ≤ (1 + (K : ℝ)) ^ 3 * C := by
    calc ‖Φ X‖ * (1 + ‖z‖) ^ 3 ≤ ‖Φ X‖ * ((1 + (K : ℝ)) ^ 3 * (1 + ‖X‖) ^ 3) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (1 + (K : ℝ)) ^ 3 * ((1 + ‖X‖) ^ 3 * ‖Φ X‖) := by ring
      _ ≤ (1 + (K : ℝ)) ^ 3 * C := mul_le_mul_of_nonneg_left (hC X) (by positivity)
  have hr : (1 + ‖z‖) ^ (-(3 : ℝ)) = ((1 + ‖z‖) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    norm_cast
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact hmul

/- English proof (translation)
Establish `hε' : (ε : ℂ) ≠ 0` using `by exact_mod_cast hε.ne'`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Use `set b : ℂ := ((-(Real.pi / ε ^ 2) : ℝ) : ℂ) with hb`. Establish `hbre : b.re < 0`. Rewrite using `[hb, Complex.ofReal_re]`.

Establish `: 0 < Real.pi / ε ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `integral_cexp_quadratic hbre (2 * Real.pi * Complex.I * u) 0`. Establish `hint : ∀ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * u : ℝ) : ℂ)) = (ε⁻¹ : ℂ) * Complex.exp (b * (ζ : ℂ) ^ 2 + 2 * Real.pi * Complex.I * u * ζ + 0)`. Introduce `ζ`.

Rewrite using `[GlobalTheory.CompanionTheory.Parseval.gau_eq]`. Use `push_cast`. Rewrite using `[mul_assoc, ← Complex.exp_add, hb]`. Use `push_cast`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hint]`. Rewrite using `[integral_const_mul, key]`. Establish `hsq : (Real.pi : ℂ) / -b = ((ε ^ 2 : ℝ) : ℂ)`. Rewrite using `[hb]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hroot : (((ε ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ε`. Rewrite using `[show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]`. Rewrite using `[hsq, hroot, ← mul_assoc, inv_mul_cancel₀ hε', one_mul]`.

Unfold `ge`. Use `push_cast`. Use `congr 1`. Rewrite using `[hb]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
lemma ge_eq_integral (ε u : ℝ) (hε : 0 < ε) :
    ((ge ε u : ℝ) : ℂ) = ∫ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((ζ * u : ℝ) : ℂ)) := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set b : ℂ := ((-(Real.pi / ε ^ 2) : ℝ) : ℂ) with hb
  have hbre : b.re < 0 := by
    rw [hb, Complex.ofReal_re]
    have : 0 < Real.pi / ε ^ 2 := by positivity
    linarith
  have key := integral_cexp_quadratic hbre (2 * Real.pi * Complex.I * u) 0
  have hint : ∀ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((ζ * u : ℝ) : ℂ)) =
      (ε⁻¹ : ℂ) * Complex.exp (b * (ζ : ℂ) ^ 2 + 2 * Real.pi * Complex.I * u * ζ + 0) := by
    intro ζ
    rw [GlobalTheory.CompanionTheory.Parseval.gau_eq]
    push_cast
    rw [mul_assoc, ← Complex.exp_add, hb]
    push_cast
    congr 2
    ring
  simp_rw [hint]
  rw [integral_const_mul, key]
  have hsq : (Real.pi : ℂ) / -b = ((ε ^ 2 : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  have hroot : (((ε ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ε := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]
  rw [hsq, hroot, ← mul_assoc, inv_mul_cancel₀ hε', one_mul]
  unfold ge
  push_cast
  congr 1
  rw [hb]
  push_cast
  field_simp
  ring_nf
  simp

/- English proof (translation)
Unfold `psiR`. Establish `: -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_psiR (x : ℝ) : ‖psiR x‖ = 1 := by
  unfold psiR
  have : -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Establish `: 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_cexp_two_pi (x : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Unfold `psiR`. Use `fun_prop`.
-/
lemma continuous_psiR : Continuous psiR := by
  unfold psiR; fun_prop

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Parseval.gau`. Use `fun_prop`.
-/
lemma continuous_gau (ε : ℝ) : Continuous (GlobalTheory.CompanionTheory.Parseval.gau ε) := by
  unfold GlobalTheory.CompanionTheory.Parseval.gau; fun_prop

/- English proof (translation)
Establish `e : psiR (-z₁) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z₀ - v) : ℝ) : ℂ)) = psiR (ζ * v) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * z₀ + z₁ : ℝ) : ℂ))`. Unfold `psiR`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `a * g * e`.
-/
lemma phase_identity (a g : ℂ) (ζ v z₀ z₁ : ℝ) :
    a * psiR (-z₁) * (g * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z₀ - v) : ℝ) : ℂ))) =
      g * psiR (ζ * v) * (a * Complex.exp (2 * Real.pi * Complex.I * ((ζ * z₀ + z₁ : ℝ) : ℂ))) := by
  have e : psiR (-z₁) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z₀ - v) : ℝ) : ℂ)) =
      psiR (ζ * v) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * z₀ + z₁ : ℝ) : ℂ)) := by
    unfold psiR
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination a * g * e

/- English proof (translation)
Introduce `Φ ε h v hε hd`. Establish `hF` using `integrable_rows Φ h hd`. Establish `hFc : Continuous fun z : Fin 2 → ℝ => Φ (Matrix.of.symm (Matrix.of h * blk z))` using `Φ.continuous.comp (continuous_rows h)`. Use `set F : (Fin 2 → ℝ) → ℂ := fun z => Φ (Matrix.of.symm (Matrix.of h * blk z)) with hFdef`. Set `f : (Fin 2 → ℝ) → ℝ → ℂ` to `fun z ζ => F z * psiR (-(z 1)) * ((GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z 0 - v) : ℝ) : ℂ)))`.

Establish `hψ` using `continuous_psiR`. Establish `hg` using `continuous_gau ε`. Establish `hcont : Continuous (Function.uncurry f)` using `by show Continuous fun p : (Fin 2 → ℝ) × ℝ => F p.1 * psiR (-(p.1 1)) * ((GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((p.2 * (p.1 0 - v) : ℝ) : ℂ)))`. Establish `h1 : Continuous fun p : (Fin 2 → ℝ) × ℝ => F p.1` using `hFc.comp continuous_fst`. Establish `h2 : Continuous fun p : (Fin 2 → ℝ) × ℝ => psiR (-(p.1 1))` using `hψ.comp (by fun_prop)`.

Establish `h3 : Continuous fun p : (Fin 2 → ℝ) × ℝ => (GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ)` using `Complex.continuous_ofReal.comp (hg.comp continuous_snd)`. Establish `h4 : Continuous fun p : (Fin 2 → ℝ) × ℝ => Complex.exp (2 * Real.pi * Complex.I * ((p.2 * (p.1 0 - v) : ℝ) : ℂ))` using `by fun_prop`. Conclude with `(h1.mul h2).mul (h3.mul h4)`. Establish `hint : Integrable (Function.uncurry f) ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ))`. Use `(hF.norm.mul_prod (GlobalTheory.CompanionTheory.Parseval.gau_integrable ε hε)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations.

Establish `hgn : ‖(GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ)‖ = GlobalTheory.CompanionTheory.Parseval.gau ε p.2`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (GlobalTheory.CompanionTheory.Parseval.gau_nonneg ε p.2 hε)]`. Simplify using `only [Function.uncurry, f, norm_mul, norm_psiR, norm_cexp_two_pi, hgn, mul_one]`. Conclude with `le_rfl`. Combine the equalities or inequalities in the displayed calculation.

Unfold `Ad3.LR.C.Ae`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [f]`. Rewrite using `[integral_const_mul, ← ge_eq_integral ε (z 0 - v) hε]`. Use `_ = ∫ ζ, ∫ z, f z ζ := integral_integral_swap hint`.

Use `_ = _ := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)` and prove the remaining obligations. Simplify using `only [f, GlobalTheory.CompanionTheory.Parseval.gz]`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations.

Conclude with `phase_identity _ _ ζ v (z 0) (z 1)`.
-/
theorem Ae_eq_integral_gau : ∀ (Φ : Ad3.LR.Sw) (ε : ℝ) (h : Ad3.LR.M22) (v : ℝ), 0 < ε →
    (Matrix.of h).det ≠ 0 → Ad3.LR.C.Ae Φ ε h v =
      ∫ ζ : ℝ, (GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) * Ad3.psiR (ζ * v) * GlobalTheory.CompanionTheory.Parseval.gz Φ h ζ := by
  intro Φ ε h v hε hd
  have hF := integrable_rows Φ h hd
  have hFc : Continuous fun z : Fin 2 → ℝ => Φ (Matrix.of.symm (Matrix.of h * blk z)) :=
    Φ.continuous.comp (continuous_rows h)
  set F : (Fin 2 → ℝ) → ℂ := fun z => Φ (Matrix.of.symm (Matrix.of h * blk z)) with hFdef
  let f : (Fin 2 → ℝ) → ℝ → ℂ := fun z ζ => F z * psiR (-(z 1)) *
    ((GlobalTheory.CompanionTheory.Parseval.gau ε ζ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ζ * (z 0 - v) : ℝ) : ℂ)))
  have hψ := continuous_psiR
  have hg := continuous_gau ε
  have hcont : Continuous (Function.uncurry f) := by
    show Continuous fun p : (Fin 2 → ℝ) × ℝ => F p.1 * psiR (-(p.1 1)) *
      ((GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((p.2 * (p.1 0 - v) : ℝ) : ℂ)))
    have h1 : Continuous fun p : (Fin 2 → ℝ) × ℝ => F p.1 := hFc.comp continuous_fst
    have h2 : Continuous fun p : (Fin 2 → ℝ) × ℝ => psiR (-(p.1 1)) :=
      hψ.comp (by fun_prop)
    have h3 : Continuous fun p : (Fin 2 → ℝ) × ℝ => (GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ) :=
      Complex.continuous_ofReal.comp (hg.comp continuous_snd)
    have h4 : Continuous fun p : (Fin 2 → ℝ) × ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * ((p.2 * (p.1 0 - v) : ℝ) : ℂ)) := by fun_prop
    exact (h1.mul h2).mul (h3.mul h4)
  have hint : Integrable (Function.uncurry f) ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := by
    refine (hF.norm.mul_prod (GlobalTheory.CompanionTheory.Parseval.gau_integrable ε hε)).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hgn : ‖(GlobalTheory.CompanionTheory.Parseval.gau ε p.2 : ℂ)‖ = GlobalTheory.CompanionTheory.Parseval.gau ε p.2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (GlobalTheory.CompanionTheory.Parseval.gau_nonneg ε p.2 hε)]
    simp only [Function.uncurry, f, norm_mul, norm_psiR, norm_cexp_two_pi, hgn, mul_one]
    exact le_rfl
  calc Ad3.LR.C.Ae Φ ε h v = ∫ z, ∫ ζ, f z ζ := by
        unfold Ad3.LR.C.Ae
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [f]
        rw [integral_const_mul, ← ge_eq_integral ε (z 0 - v) hε]
    _ = ∫ ζ, ∫ z, f z ζ := integral_integral_swap hint
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only [f, GlobalTheory.CompanionTheory.Parseval.gz]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact phase_identity _ _ ζ v (z 0) (z 1)

end GlobalTheory.CompanionTheory.Parseval.GaussRep
