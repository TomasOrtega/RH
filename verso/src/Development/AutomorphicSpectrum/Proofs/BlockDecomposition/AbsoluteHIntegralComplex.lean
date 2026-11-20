import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits

noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.HAbsC

/- English proof (translation)
Unfold `ph`. Rewrite using `[← mul_zpow, div_mul_div_comm, norm_mul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem ph_mul (n : ℤ) (a b : ℂ) : ph n (a * b) = ph n a * ph n b := by
  unfold ph
  rw [← mul_zpow, div_mul_div_comm, norm_mul]
  push_cast
  rfl

/- English proof (translation)
Unfold `ph`. Rewrite using `[norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz), _root_.one_zpow]`.
-/
theorem norm_ph (n : ℤ) {z : ℂ} (hz : z ≠ 0) : ‖ph n z‖ = 1 := by
  unfold ph
  rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz), _root_.one_zpow]

/- English proof (translation)
Establish `hn : ((‖c‖ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc)`. Use `set u : ℂ := c / ((‖c‖ : ℝ) : ℂ) with hu`. Establish `hu0 : u ≠ 0` using `div_ne_zero hc hn`. Establish `h1 : c ^ 2 / ((‖c ^ 2‖ : ℝ) : ℂ) = u ^ 2`. Rewrite using `[norm_pow, hu, div_pow]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `h2 : c⁻¹ / ((‖c⁻¹‖ : ℝ) : ℂ) = u⁻¹`. Rewrite using `[norm_inv, hu, inv_div]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Unfold `ph`. Rewrite using `[h1, h2, ← zpow_natCast u 2, ← _root_.zpow_mul, _root_.inv_zpow', ← zpow_add₀ hu0]`. Establish `: ((2 : ℕ) : ℤ) * (2 * (k : ℤ) - 2) + -(4 * (k : ℤ) - 4) = 0`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, zpow_zero]`.
-/
theorem ph_central (k : ℕ) {c : ℂ} (hc : c ≠ 0) :
    ph (2 * (k : ℤ) - 2) (c ^ 2) * ph (4 * (k : ℤ) - 4) c⁻¹ = 1 := by
  have hn : ((‖c‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc)
  set u : ℂ := c / ((‖c‖ : ℝ) : ℂ) with hu
  have hu0 : u ≠ 0 := div_ne_zero hc hn
  have h1 : c ^ 2 / ((‖c ^ 2‖ : ℝ) : ℂ) = u ^ 2 := by
    rw [norm_pow, hu, div_pow]
    push_cast
    rfl
  have h2 : c⁻¹ / ((‖c⁻¹‖ : ℝ) : ℂ) = u⁻¹ := by
    rw [norm_inv, hu, inv_div]
    push_cast
    field_simp
  unfold ph
  rw [h1, h2, ← zpow_natCast u 2, ← _root_.zpow_mul, _root_.inv_zpow', ← zpow_add₀ hu0]
  have : ((2 : ℕ) : ℤ) * (2 * (k : ℤ) - 2) + -(4 * (k : ℤ) - 4) = 0 := by
    push_cast
    ring
  rw [this, zpow_zero]

/- English proof (translation)
Establish `hdet : (c • M).det = c ^ 2 * M.det`. Simplify using `[Matrix.det_fin_two]`. Establish `hin : ∀ t y : ℂ, Matrix.vecMul ![t, t * y] (c • M) = Matrix.vecMul ![c * t, c * t * y] M`. Introduce `t y`. Use extensionality with `j`.

Simplify using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Use `set m : ℤ := 4 * (k : ℤ) - 4 with hm`. Use `set G : ℂ → ℂ := fun u => ∫ y : ℂ, f (Matrix.vecMul ![u, u * y] M) * psiC (-y) with hG`. Establish `hI : ∫ t : ℂ, ph m t * ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] (c • M)) * psiC (-y) = (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) * (ph m c⁻¹ * ∫ u : ℂ, ph m u * G u)`.

Establish `e : ∀ t : ℂ, ph m t * ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] (c • M)) * psiC (-y) = (fun u => ph m c⁻¹ * (ph m u * G u)) (c * t)`. Introduce `t`. Establish `h1 : t = c⁻¹ * (c * t)` using `by field_simp`. Simplify using `only [hG, hin]`. Use `conv_lhs => rw [h1, ph_mul, ← h1]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Rewrite using `[integral_comp_mul c hc (fun u => ph m c⁻¹ * (ph m u * G u)), integral_const_mul]`. Unfold `W2`. Rewrite using `[hI, hdet, ph_mul, norm_mul, norm_pow]`.

Establish `hcn : ‖c‖ ≠ 0` using `norm_ne_zero_iff.2 hc`. Establish `hp` using `ph_central k hc`. Rewrite `hp` using `[← hm]`. Establish `hcc : ((‖c‖ ^ 2 : ℝ) : ℂ) * (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]`.

Simplify using `only [hG]`. Move the coercions through the operations in `at hcc ⊢`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem whittakerGL2_smul_eq (k : ℕ) (f : (Fin 2 → ℂ) → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) {c : ℂ} (hc : c ≠ 0) :
    W2 k f (c • M) = W2 k f M := by
  have hdet : (c • M).det = c ^ 2 * M.det := by
    simp [Matrix.det_fin_two]
  have hin : ∀ t y : ℂ, Matrix.vecMul ![t, t * y] (c • M) = Matrix.vecMul ![c * t, c * t * y] M := by
    intro t y
    ext j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  set m : ℤ := 4 * (k : ℤ) - 4 with hm
  set G : ℂ → ℂ := fun u => ∫ y : ℂ, f (Matrix.vecMul ![u, u * y] M) * psiC (-y) with hG
  have hI : ∫ t : ℂ, ph m t * ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] (c • M)) * psiC (-y) =
      (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) * (ph m c⁻¹ * ∫ u : ℂ, ph m u * G u) := by
    have e : ∀ t : ℂ, ph m t * ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] (c • M)) * psiC (-y) =
        (fun u => ph m c⁻¹ * (ph m u * G u)) (c * t) := by
      intro t
      have h1 : t = c⁻¹ * (c * t) := by field_simp
      simp only [hG, hin]
      conv_lhs => rw [h1, ph_mul, ← h1]
      ring
    simp only [e]
    rw [integral_comp_mul c hc (fun u => ph m c⁻¹ * (ph m u * G u)), integral_const_mul]
  unfold W2
  rw [hI, hdet, ph_mul, norm_mul, norm_pow]
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hp := ph_central k hc
  rw [← hm] at hp
  have hcc : ((‖c‖ ^ 2 : ℝ) : ℂ) * (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
  simp only [hG]
  push_cast at hcc ⊢
  calc _ = (ph (2 * (k : ℤ) - 2) (c ^ 2) * ph m c⁻¹) * (((‖c‖ : ℂ) ^ 2 * ((‖c‖ : ℂ) ^ 2)⁻¹)) *
        (ph (2 * (k : ℤ) - 2) M.det * (‖M.det‖ : ℂ) *
          ∫ u : ℂ, ph m u * ∫ y : ℂ, f (Matrix.vecMul ![u, u * y] M) * psiC (-y)) := by ring
    _ = _ := by rw [hp, hcc, one_mul, one_mul]

/- English proof (translation)
Establish `h : w2 * d2 (-1 / v) = (-1 / v) • (d2 (-v) * w2)`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w2, d2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp`. Rewrite using `[h, Matrix.smul_mul, Matrix.mul_assoc]`.
-/
theorem weyl_diag_eq_smul_diag_weyl (v : ℂ) (hv : v ≠ 0) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    w2 * d2 (-1 / v) * H = (-1 / v) • (d2 (-v) * (w2 * H)) := by
  have h : w2 * d2 (-1 / v) = (-1 / v) • (d2 (-v) * w2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w2, d2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  rw [h, Matrix.smul_mul, Matrix.mul_assoc]

/- English proof (translation)
Unfold `Hw`. Rewrite using `[weyl_diag_eq_smul_diag_weyl v hv, whittakerGL2_smul_eq k f _ (div_ne_zero (by simp) hv)]`.
-/
theorem Hw_eq (k : ℕ) (n : ℤ) (s : ℂ) (f : (Fin 2 → ℂ) → ℂ) {v : ℂ} (hv : v ≠ 0) (κ : M22) :
    Hw k n s f v κ = W2 k f (d2 (-v) * (w2 * (Matrix.of κ)⁻¹)) * ph (-n) v *
      ((‖v‖ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 - s) := by
  unfold Hw
  rw [weyl_diag_eq_smul_diag_weyl v hv, whittakerGL2_smul_eq k f _ (div_ne_zero (by simp) hv)]

/- English proof (translation)
Establish `hp : 0 < ‖v‖` using `norm_pos_iff.2 hv`. Rewrite using `[Hw_eq k n s f hv, norm_mul, norm_mul, norm_ph _ hv, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hp.le]`. Use `congr 1`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_Hw (k : ℕ) (n : ℤ) (s : ℂ) (f : (Fin 2 → ℂ) → ℂ) {v : ℂ} (hv : v ≠ 0) (κ : M22) :
    ‖Hw k n s f v κ‖ = ‖W2 k f (d2 (-v) * (w2 * (Matrix.of κ)⁻¹))‖ * ‖v‖ ^ (-1 - 2 * s.re) := by
  have hp : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [Hw_eq k n s f hv, norm_mul, norm_mul, norm_ph _ hv, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  congr 1
  simp
  ring

/- English proof (translation)
Use `StronglyMeasurable.aestronglyMeasurable ?_` and prove the remaining obligations. Use `Measurable.stronglyMeasurable ?_` and prove the remaining obligations. Use `Measurable.mul (Measurable.mul ?_ (measurable_ph _)) ?_` and prove the remaining obligations. Conclude with `((stronglyMeasurable_whittakerGL2_diag k f g).comp_measurable measurable_neg).measurable`. Conclude with `(Complex.measurable_ofReal.comp (by fun_prop)).pow_const _`.
-/
theorem measurable_Hw' (k : ℕ) (n : ℤ) (s : ℂ) (f : SchwartzMap (Fin 2 → ℂ) ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    AEStronglyMeasurable (fun v : ℂ => W2 k f (d2 (-v) * g) * ph (-n) v *
      ((‖v‖ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 - s)) volume := by
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.mul (Measurable.mul ?_ (measurable_ph _)) ?_
  · exact ((stronglyMeasurable_whittakerGL2_diag k f g).comp_measurable measurable_neg).measurable
  · exact (Complex.measurable_ofReal.comp (by fun_prop)).pow_const _

/- English proof (translation)
Rewrite using `[Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Simplify using `[w2, Matrix.det_fin_two]`.
-/
theorem det_weyl_mul_inv (K : Matrix (Fin 2) (Fin 2) ℂ) (hK : K.det ≠ 0) :
    (w2 * K⁻¹).det = K.det⁻¹ := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  simp [w2, Matrix.det_fin_two]

/- English proof (translation)
Establish `hd` using `det_weyl_mul_inv _ hκ`. Establish `hn : ‖(Matrix.of κ).det‖ ≠ 0` using `norm_ne_zero_iff.2 hκ`. Establish `e0 : (w2 * (Matrix.of κ)⁻¹) 1 0 = -((Matrix.of κ).det⁻¹ * κ 1 1)`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]`. Simplify using `[w2, Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `e1 : (w2 * (Matrix.of κ)⁻¹) 1 1 = (Matrix.of κ).det⁻¹ * κ 0 1`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]`. Simplify using `[w2, Matrix.mul_apply, Fin.sum_univ_two]`. Unfold `Yb`. Rewrite using `[hd, e0, e1, norm_neg, norm_mul, norm_mul, norm_inv]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iwasawa_height_weyl_mul_inv (κ : M22) (hκ : (Matrix.of κ).det ≠ 0) :
    Yb (w2 * (Matrix.of κ)⁻¹) =
      ‖(Matrix.of κ).det‖ ^ 2 / (‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2) ^ 2 := by
  have hd := det_weyl_mul_inv _ hκ
  have hn : ‖(Matrix.of κ).det‖ ≠ 0 := norm_ne_zero_iff.2 hκ
  have e0 : (w2 * (Matrix.of κ)⁻¹) 1 0 = -((Matrix.of κ).det⁻¹ * κ 1 1) := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : (w2 * (Matrix.of κ)⁻¹) 1 1 = (Matrix.of κ).det⁻¹ * κ 0 1 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two]
  unfold Yb
  rw [hd, e0, e1, norm_neg, norm_mul, norm_mul, norm_inv]
  field_simp
  ring

/- English proof (translation)
Introduce `hZ k hk σ h0 h1`. Take `⟨C, N, hC⟩` from `hZ k hk (1 - σ) (by linarith) (by linarith)`. Use `⟨C, N, fun f n s hs κ hκ => ?_⟩` and prove the remaining obligations. Establish `hY` using `iwasawa_height_weyl_mul_inv κ hκ`. Establish `hdetg` using `det_weyl_mul_inv _ hκ`.

Establish `hnorm0 : ∀ {v : ℂ}, v ≠ 0 → ‖Hw k n s f v κ‖ = ‖W2 k f (d2 (-v) * (w2 * (Matrix.of κ)⁻¹))‖ * ‖v‖ ^ (-1 - 2 * σ)`. Introduce `v hv`. Rewrite using `[norm_Hw k n s f hv κ, hs]`. Establish `heq0 : ∀ {v : ℂ}, v ≠ 0 → Hw k n s f v κ = W2 k f (d2 (-v) * (w2 * (Matrix.of κ)⁻¹)) * ph (-n) v * ((‖v‖ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 - s)` using `fun hv => Hw_eq k n s f hv κ`. Generalize the expression as in `(w2 * (Matrix.of κ)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = g at hY hdetg hnorm0 heq0`.

Establish `hg0 : g.det ≠ 0`. Rewrite using `[hdetg]`. Conclude with `inv_ne_zero hκ`. Take `⟨i1, i2⟩` from `hC f g hg0`. Set `φ : ℂ → ℝ` to `fun x => ‖W2 k f (d2 x * g)‖ * ‖x‖ ^ (2 * (1 - σ) - 1)`.

Set `G : ℂ → ℝ` to `fun x => ‖W2 k f (d2 x * g)‖ * ‖x‖ ^ (-1 - 2 * σ)`. Establish `hne : ∀ᵐ x : ℂ, x ≠ 0`. Simplify using `[ae_iff]`. Establish `hφG : ∀ x : ℂ, x ≠ 0 → (‖x‖ ^ 2)⁻¹ * φ x = G x`. Introduce `x hx`.

Establish `hp : 0 < ‖x‖` using `norm_pos_iff.2 hx`. Establish `e : ‖x‖ ^ (-1 - 2 * σ) = (‖x‖ ^ 2)⁻¹ * ‖x‖ ^ (2 * (1 - σ) - 1)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_neg hp.le, ← Real.rpow_add hp]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [φ, G, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGint : Integrable G`. Establish `h2` using `(integrable_mulC_iff (fun x => ((φ x : ℝ) : ℂ))).1 i1.ofReal`.

Use `h2.re.congr ?_` and prove the remaining obligations. Use `filter_upwards [hne] with x hx`. Rewrite using `[← hφG x hx]`. Use `show Complex.re ((((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((φ x : ℝ) : ℂ)) = _`. Rewrite using `[← Complex.ofReal_mul, Complex.ofReal_re]`.

Establish `hGI : ∫ x, G x = ∫ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * (1 - σ) - 1) ∂mulC`. Establish `h2` using `integral_mulC (fun x => ((φ x : ℝ) : ℂ))`. Establish `e : ∀ x : ℂ, (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) = (((‖x‖ ^ 2)⁻¹ * φ x : ℝ) : ℂ)`. Introduce `x`. Use `push_cast`.

Both sides reduce to the same expression. Simplify using `only [e] at h2`. Rewrite `h2` using `[integral_complex_ofReal, integral_complex_ofReal]`. Establish `h3 : ∫ a : ℂˣ, φ a ∂mulC = ∫ x, (‖x‖ ^ 2)⁻¹ * φ x` using `by exact_mod_cast h2`. Use `Eq.trans ?_ h3.symm` and prove the remaining obligations.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hne] with x hx`. Conclude with `(hφG x hx).symm`. Establish `hnorm : ∀ᵐ v : ℂ, ‖Hw k n s f v κ‖ = G (-v)` using `by filter_upwards [hne] with v hv`. Rewrite using `[hnorm0 hv]`.

Simplify using `[G]`. Establish `hmeas : AEStronglyMeasurable (fun v : ℂ => Hw k n s f v κ) volume`. Use `(measurable_Hw' k n s f g).congr ?_` and prove the remaining obligations. Use `filter_upwards [hne] with v hv`. Conclude with `(heq0 hv).symm`.

Prove the components needed by the constructor for the conclusion. Use `(hGint.comp_neg).mono' hmeas ?_ filter_upwards [hnorm] with v hv` and prove the remaining obligations. Conclude with `hv.le`. Rewrite using `[integral_congr_ae hnorm, integral_neg_eq_self G volume, hGI]`. Use `i2.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[hY]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : Ad3.K.LC.C.AbsoluteZetaIntegralBound → Ad3.K.LC.C.HAbs := by
  intro hZ k hk σ h0 h1
  obtain ⟨C, N, hC⟩ := hZ k hk (1 - σ) (by linarith) (by linarith)
  refine ⟨C, N, fun f n s hs κ hκ => ?_⟩
  have hY := iwasawa_height_weyl_mul_inv κ hκ
  have hdetg := det_weyl_mul_inv _ hκ
  have hnorm0 : ∀ {v : ℂ}, v ≠ 0 → ‖Hw k n s f v κ‖ =
      ‖W2 k f (d2 (-v) * (w2 * (Matrix.of κ)⁻¹))‖ * ‖v‖ ^ (-1 - 2 * σ) := by
    intro v hv
    rw [norm_Hw k n s f hv κ, hs]
  have heq0 : ∀ {v : ℂ}, v ≠ 0 → Hw k n s f v κ =
      W2 k f (d2 (-v) * (w2 * (Matrix.of κ)⁻¹)) * ph (-n) v *
        ((‖v‖ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 - s) := fun hv => Hw_eq k n s f hv κ
  generalize (w2 * (Matrix.of κ)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = g at hY hdetg hnorm0 heq0
  have hg0 : g.det ≠ 0 := by
    rw [hdetg]
    exact inv_ne_zero hκ
  obtain ⟨i1, i2⟩ := hC f g hg0
  let φ : ℂ → ℝ := fun x => ‖W2 k f (d2 x * g)‖ * ‖x‖ ^ (2 * (1 - σ) - 1)
  let G : ℂ → ℝ := fun x => ‖W2 k f (d2 x * g)‖ * ‖x‖ ^ (-1 - 2 * σ)
  have hne : ∀ᵐ x : ℂ, x ≠ 0 := by
    simp [ae_iff]
  have hφG : ∀ x : ℂ, x ≠ 0 → (‖x‖ ^ 2)⁻¹ * φ x = G x := by
    intro x hx
    have hp : 0 < ‖x‖ := norm_pos_iff.2 hx
    have e : ‖x‖ ^ (-1 - 2 * σ) = (‖x‖ ^ 2)⁻¹ * ‖x‖ ^ (2 * (1 - σ) - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hp.le, ← Real.rpow_add hp]
      congr 1
      push_cast
      ring
    simp only [φ, G, e]
    ring
  have hGint : Integrable G := by
    have h2 := (integrable_mulC_iff (fun x => ((φ x : ℝ) : ℂ))).1 i1.ofReal
    refine h2.re.congr ?_
    filter_upwards [hne] with x hx
    rw [← hφG x hx]
    show Complex.re ((((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((φ x : ℝ) : ℂ)) = _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hGI : ∫ x, G x = ∫ a : ℂˣ, ‖W2 k f (d2 a * g)‖ * ‖(a : ℂ)‖ ^ (2 * (1 - σ) - 1) ∂mulC := by
    have h2 := integral_mulC (fun x => ((φ x : ℝ) : ℂ))
    have e : ∀ x : ℂ, (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) = (((‖x‖ ^ 2)⁻¹ * φ x : ℝ) : ℂ) := by
      intro x
      push_cast
      rfl
    simp only [e] at h2
    rw [integral_complex_ofReal, integral_complex_ofReal] at h2
    have h3 : ∫ a : ℂˣ, φ a ∂mulC = ∫ x, (‖x‖ ^ 2)⁻¹ * φ x := by exact_mod_cast h2
    refine Eq.trans ?_ h3.symm
    refine integral_congr_ae ?_
    filter_upwards [hne] with x hx
    exact (hφG x hx).symm
  have hnorm : ∀ᵐ v : ℂ, ‖Hw k n s f v κ‖ = G (-v) := by
    filter_upwards [hne] with v hv
    rw [hnorm0 hv]
    simp [G]
  have hmeas : AEStronglyMeasurable (fun v : ℂ => Hw k n s f v κ) volume := by
    refine (measurable_Hw' k n s f g).congr ?_
    filter_upwards [hne] with v hv
    exact (heq0 hv).symm
  constructor
  · refine (hGint.comp_neg).mono' hmeas ?_
    filter_upwards [hnorm] with v hv
    exact hv.le
  · rw [integral_congr_ae hnorm, integral_neg_eq_self G volume, hGI]
    refine i2.trans (le_of_eq ?_)
    rw [hY]
    congr 2
    ring

end GlobalTheory.CompanionTheory.HAbsC
