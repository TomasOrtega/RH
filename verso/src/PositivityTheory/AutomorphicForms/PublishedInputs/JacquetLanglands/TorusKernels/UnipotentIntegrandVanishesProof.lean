import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.SigmaFiniteInverseAbsDensity
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HaarIcc
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IntegralProdLog

noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

def ptp (p : ℝ × Y1) : P := pt p.1 p.2.1 p.2.2

def large₂ {I : Type} [Fintype I] (y : I → Y1) : ℝ := ∑ v, Real.log |(y v).1|

/- English proof (translation)
Unfold `large₂`. Conclude with `Finset.measurable_sum _ fun v _ => Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))`.
-/
theorem measurable_Lg {I : Type} [Fintype I] : Measurable (large₂ (I := I)) := by
  unfold large₂
  exact Finset.measurable_sum _ fun v _ =>
    Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem pt_congr {a a' c c' : ℝ} (h1 : a = a') (h2 : c = c') (hc : c ≠ 0) (hc' : c' ≠ 0) :
    pt a c hc = pt a' c' hc' := by
  subst h1
  subst h2
  rfl

/- English proof (translation)
Establish `h : ∀ v, Real.log |t * (y v).1| = Real.log t + Real.log |(y v).1|`. Introduce `v`. Rewrite using `[abs_mul, abs_of_pos ht, Real.log_mul ht.ne' (abs_ne_zero.mpr (y v).2)]`. Unfold `large₂`. Simplify using `only [scl, h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
theorem Lg_scl {I : Type} [Fintype I] (t : ℝ) (ht : 0 < t) (y : I → Y1) :
    large₂ (fun v => scl t ht.ne' (y v)) = Fintype.card I * Real.log t + large₂ y := by
  have h : ∀ v, Real.log |t * (y v).1| = Real.log t + Real.log |(y v).1| := by
    intro v
    rw [abs_mul, abs_of_pos ht, Real.log_mul ht.ne' (abs_ne_zero.mpr (y v).2)]
  unfold large₂
  simp only [scl, h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end UpperTheory.Esk.UnipotentIntegrandLemmas

open UpperTheory.Esk.UnipotentIntegrandLemmas in
/- English proof (translation)
Unfold `B1a UpperHalfPlaneMeasureCoordinates ConstantTermVanishingAlt`. Introduce `hB1 hB5`. Take `⟨hσ, -, -⟩` from `hB1`. Take `⟨hmp, -, hcont⟩` from `hB5`. Use `hσ` as an intermediate fact.

Introduce `I _ _ φ hφ β hβ hβ0 hβinv A B hA hAB u hu hint`. Establish `hval : Measurable (fun z : P => z.1)` using `measurable_subtype_coe`. Establish `hgm : Measurable (fun z : P => ((z.1.re / z.1.im, (⟨z.1.im, z.2⟩ : Y1)) : ℝ × Y1))` using `((Complex.measurable_re.comp hval).div (Complex.measurable_im.comp hval)).prodMk (Complex.measurable_im.comp hval).subtype_mk`. Set `eP : ℝ × Y1 ≃ᵐ P` to `{ toFun := fun p => pt p.1 p.2.1 p.2.2 invFun := fun z => (z.1.re / z.1.im, ⟨z.1.im, z.2⟩) left_inv := by`. Introduce and unpack `⟨x, y, hy⟩`.

Establish `h1 : ((y : ℂ) * ((x : ℂ) + Complex.I)).re = y * x` using `by simp`. Establish `h2 : ((y : ℂ) * ((x : ℂ) + Complex.I)).im = y` using `by simp`. Use `Prod.ext ?_ (Subtype.ext ?_)` and prove the remaining obligations. Use `show ((y : ℂ) * ((x : ℂ) + Complex.I)).re / ((y : ℂ) * ((x : ℂ) + Complex.I)).im = x`. Rewrite using `[h1, h2]`.

Clear the denominators using the available nonvanishing facts. Use `show ((y : ℂ) * ((x : ℂ) + Complex.I)).im = y`. Conclude with `h2`. Use `right_inv := by`. Introduce `z`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((z.1.im : ℂ) * (((z.1.re / z.1.im : ℝ) : ℂ) + Complex.I)) = z.1`. Establish `hz : z.1.im ≠ 0` using `z.2`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]`. Use `measurable_toFun := hcont.measurable`. Use `measurable_invFun := hgm }`. Establish `hmpP : MeasurePreserving eP ((volume : Measure ℝ).prod nu1) (volume : Measure P)` using `hmp`.

Establish `hmpX : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : I => eP) (Measure.pi fun _ : I => (volume : Measure ℝ).prod nu1) (Measure.pi fun _ : I => (volume : Measure P))` using `measurePreserving_pi _ _ fun _ => hmpP`. Establish `hmpA : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) (Measure.pi fun _ : I => (volume : Measure ℝ).prod nu1)` using `MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow ℝ Y1 I (fun _ => volume) (fun _ => nu1))`. Set `Φ : (I → ℝ) × (I → Y1) ≃ᵐ X I` to `(MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm.trans (MeasurableEquiv.piCongrRight fun _ : I => eP)`. Establish `hΦ : MeasurePreserving Φ ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) (volume : Measure (X I))` using `hmpX.comp hmpA`. Establish `hΦapp : ∀ (x : I → ℝ) (y : I → Y1), Φ (x, y) = fun v => pt (x v) (y v).1 (y v).2` using `fun x y => rfl`.

Take `⟨b, hbdef⟩ : ∃ b : (I → Y1) → ℝ, b = fun y => β (Φ (0, y))` from `⟨_, rfl⟩`. Establish `hb : Measurable b`. Rewrite using `[hbdef]`. Conclude with `hβ.comp (Φ.measurable.comp (measurable_const.prodMk measurable_id))`. Establish `hb0 : ∀ y, 0 ≤ b y`.

Rewrite using `[hbdef]`. Conclude with `fun y => hβ0 _`. Establish `hβΦ : ∀ (x : I → ℝ) (y : I → Y1), β (Φ (x, y)) = b y`. Introduce `x y`. Rewrite using `[hbdef]`.

Use `show β (Φ (x, y)) = β (Φ (0, y))`. Rewrite using `[hΦapp, hΦapp]`. Use `(hβinv x 0 (fun v => (y v).1) (fun v => (y v).2) 1 one_pos).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `v`.

Conclude with `pt_congr rfl (one_mul _) _ _`. Establish `huΦ : ∀ (x : I → ℝ) (y : I → Y1), u (Φ (x, y)) = (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0)`. Introduce `x y`. Rewrite using `[hΦapp]`. Conclude with `hu x (fun v => (y v).1) (fun v => (y v).2)`.

Establish `hint' : Integrable (fun p : (I → ℝ) × (I → Y1) => b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0)) ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1))`. Use `((hΦ.integrable_comp_emb Φ.measurableEmbedding).mpr hint).congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Take `⟨x, y⟩` from `p`. Use `show β (Φ (x, y)) • u (Φ (x, y)) = _`. Rewrite using `[hβΦ, huΦ]`.

Establish `hI : ∫ z, β z • u z = ∫ p : (I → ℝ) × (I → Y1), b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0) ∂((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1))`. Use `(hΦ.integral_comp' (fun z => β z • u z)).symm.trans ?_` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Take `⟨x, y⟩` from `p`. Use `show β (Φ (x, y)) • u (Φ (x, y)) = _`.

Rewrite using `[hβΦ, huΦ]`. Establish `hcond : ∀ (x : I → ℝ) (y : I → Y1), (A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B) ↔ large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)`. Introduce `x y`. Establish `hp : 0 < ∏ v, |(y v).1|` using `Finset.prod_pos fun v _ => abs_pos.mpr (y v).2`. Establish `hq : 0 < ∏ v, (1 + x v ^ 2)` using `Finset.prod_pos fun v _ => by positivity`.

Establish `hL : large₂ y = Real.log (∏ v, |(y v).1|)` using `by show ∑ v, Real.log |(y v).1| = _`. Rewrite using `[Real.log_prod (s := Finset.univ) (f := fun v => |(y v).1|) fun v _ => abs_ne_zero.mpr (y v).2]`. Establish `hM : Real.log (A / ∏ v, (1 + x v ^ 2)) = (Real.log A - ∑ v, Real.log (1 + x v ^ 2))`. Rewrite using `[Real.log_div hA.ne' hq.ne', Real.log_prod (s := Finset.univ) (f := fun v => 1 + x v ^ 2) fun v _ => by positivity]`. Rewrite using `[Set.mem_Icc, hL, ← hM, Real.log_le_log_iff (div_pos hA hq) hp, Real.log_le_log_iff hp (hA.trans hAB)]`.

Take `⟨m, hm⟩ : ∃ m : Measure ℝ, m = Measure.map (large₂ (I` from `I)) ((Measure.pi fun _ : I => nu1).withDensity fun y => ENNReal.ofReal (b y)) := ⟨_, rfl⟩`. Establish `hinner : ∀ x : I → ℝ, ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) = (∏ v, φ v (x v)) * (((m (Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B))).toReal : ℝ) : ℂ)`. Introduce `x`. Establish `hS : MeasurableSet ((large₂ (I` using `I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)) := measurable_Lg measurableSet_Icc`. Establish `e1 : (fun y : I → Y1 => b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0)) = fun y => ((((large₂ (I` using `I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)).indicator b y : ℝ) : ℂ) * ∏ v, φ v (x v) := by`.

Use function extensionality and compare the values at `y`. Distinguish the cases in `h : large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)`. Rewrite using `[if_pos ((hcond x y).mpr h), Set.indicator_of_mem (show y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) from h), Complex.real_smul]`. Rewrite using `[if_neg (fun h' => h ((hcond x y).mp h')), Set.indicator_of_notMem (show y ∉ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) from h), smul_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[e1, integral_mul_const, integral_complex_ofReal, integral_indicator hS, mul_comm]`. Use `congr 2`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hb0 y) hb.aestronglyMeasurable, hm, Measure.map_apply measurable_Lg measurableSet_Icc, withDensity_apply _ hS]`. Establish `hscl : ∀ (t : ℝ) (ht : 0 < t), MeasurePreserving (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) (Measure.pi fun _ : I => nu1) (Measure.pi fun _ : I => nu1)` using `fun t ht => measurePreserving_pi (fun _ : I => nu1) (fun _ : I => nu1) fun _ => measurePreserving_scl t ht.ne'`. Establish `hbscl : ∀ (t : ℝ) (ht : 0 < t) (y : I → Y1), b (fun v => scl t ht.ne' (y v)) = b y`.

Introduce `t ht y`. Rewrite using `[hbdef]`. Conclude with `(hβinv 0 0 (fun v => (y v).1) (fun v => (y v).2) t ht).symm`. Establish `hminv : ∀ c : ℝ, ∀ S : Set ℝ, MeasurableSet S → m ((fun x => c + x) ⁻¹' S) = m S`. Introduce `c S hS`.

Establish `hcard : (0 : ℝ) < Fintype.card I` using `by exact_mod_cast Fintype.card_pos`. Establish `hcard' : (Fintype.card I : ℝ) ≠ 0` using `hcard.ne'`. Take `⟨t, ht_def⟩ : ∃ t : ℝ, t = Real.exp (c / Fintype.card I)` from `⟨_, rfl⟩`. Establish `ht : 0 < t` using `by rw [ht_def]; exact Real.exp_pos _`. Establish `hlog : (Fintype.card I : ℝ) * Real.log t = c`.

Rewrite using `[ht_def, Real.log_exp]`. Clear the denominators using the available nonvanishing facts. Establish `hS' : MeasurableSet ((large₂ (I` using `I)) ⁻¹' S) := measurable_Lg hS`. Establish `hadd : Measurable (fun x : ℝ => c + x)` using `(continuous_add_left c).measurable`. Establish `hpre : (large₂ (I` using `I)) ⁻¹' ((fun x => c + x) ⁻¹' S) = (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) := by`.

Use extensionality with `y`. Simplify using `only [Set.mem_preimage]`. Rewrite using `[Lg_scl t ht y, hlog]`. Establish `hpm : MeasurableSet ((fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I` using `I)) ⁻¹' S)) := (hscl t ht).measurable hS'`. Establish `hmi : Measurable (((large₂ (I` using `I)) ⁻¹' S).indicator fun y => ENNReal.ofReal (b y)) := (ENNReal.measurable_ofReal.comp hb).indicator hS'`.

Rewrite using `[hm, Measure.map_apply measurable_Lg (hadd hS), Measure.map_apply measurable_Lg hS, hpre, withDensity_apply _ hpm, withDensity_apply _ hS', ← lintegral_indicator hpm, ← lintegral_indicator hS', ← (hscl t ht).lintegral_comp hmi]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : (fun v => scl t ht.ne' (y v)) ∈ (large₂ (I := I)) ⁻¹' S`. Rewrite using `[Set.indicator_of_mem (show y ∈ (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) from hy), Set.indicator_of_mem hy, hbscl t ht y]`.

Rewrite using `[Set.indicator_of_notMem (show y ∉ (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) from hy), Set.indicator_of_notMem hy]`. Establish `hlogAB : Real.log A < Real.log B` using `Real.log_lt_log hA hAB`. Establish `hsum0 : ∀ x : I → ℝ, 0 ≤ ∑ v, Real.log (1 + x v ^ 2)` using `fun x => Finset.sum_nonneg fun v _ => Real.log_nonneg (by linarith [sq_nonneg (x v)])`. Establish `hlt : ∀ x : I → ℝ, (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) < Real.log B` using `fun x => by linarith [hsum0 x]`. Establish `hP0 : ∀ x : I → ℝ, (∏ v, φ v (x v)) ≠ 0` using `fun x => Finset.prod_ne_zero_iff.mpr fun v _ => (hφ v).2.2.2.2 (x v)`.

Establish `: (ae (volume : Measure (I → ℝ))).NeBot` using `ae_neBot.mpr (NeZero.ne _)`. Take `⟨x0, hx0⟩` from `hint'.prod_right_ae.exists`. Establish `hS0 : MeasurableSet ((large₂ (I` using `I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)) := measurable_Lg measurableSet_Icc`. Establish `hTint : Integrable (((large₂ (I` using `I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)).indicator b) (Measure.pi fun _ : I => nu1) := by`. Use `(hx0.norm.div_const ‖∏ v, φ v (x0 v)‖).congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Use `show ‖b y • (if A / ∏ v, (1 + x0 v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x0 v) else 0)‖ / ‖∏ v, φ v (x0 v)‖ = _`. Distinguish the cases in `h : large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)`. Rewrite using `[if_pos ((hcond x0 y).mpr h), Set.indicator_of_mem (show y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) from h), norm_smul, Real.norm_of_nonneg (hb0 y), mul_div_assoc, div_self (norm_ne_zero_iff.mpr (hP0 x0)), mul_one]`. Rewrite using `[if_neg (fun h' => h ((hcond x0 y).mp h')), Set.indicator_of_notMem (show y ∉ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) from h), smul_zero, norm_zero, zero_div]`. Establish `hfin : m (Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)) ≠ ⊤`.

Rewrite using `[hm, Measure.map_apply measurable_Lg measurableSet_Icc, withDensity_apply _ hS0, ← lintegral_indicator hS0]`. Use `ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hTint.lintegral_lt_top)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [Set.indicator]`.

Apply the tactic sequence `split_ifs <;> simp`. Take `⟨R, hR⟩` from `haar_Icc m hminv (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B - (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2))) (by linarith [hlt x0]) (by rwa [show (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) + (Real.log B - (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2))) = Real.log B by ri …`. Establish `hR' : ∀ x : I → ℝ, ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) = (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ)`. Introduce `x`. Rewrite using `[hinner x, hR _ _ (hlt x).le, show Real.log B - (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) = (Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2) by ring]`.

Rewrite using `[hI, integral_prod _ hint']`. Use `(integral_congr_ae (Filter.Eventually.of_forall fun x => hR' x)).trans ?_` and prove the remaining obligations. Conclude with `integral_prod_log φ (fun v => ⟨(hφ v).2.1, (hφ v).2.2.1, (hφ v).2.2.2.1⟩) R (Real.log B - Real.log A)`.
-/
theorem UpperTheory.Esk.unipotent_integrand_vanishes_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.ConstantTermVanishingAlt := by
  unfold B1a UpperHalfPlaneMeasureCoordinates ConstantTermVanishingAlt
  intro hB1 hB5
  obtain ⟨hσ, -, -⟩ := hB1
  obtain ⟨hmp, -, hcont⟩ := hB5
  have := hσ
  intro I _ _ φ hφ β hβ hβ0 hβinv A B hA hAB u hu hint
  have hval : Measurable (fun z : P => z.1) := measurable_subtype_coe
  have hgm : Measurable (fun z : P => ((z.1.re / z.1.im, (⟨z.1.im, z.2⟩ : Y1)) : ℝ × Y1)) :=
    ((Complex.measurable_re.comp hval).div (Complex.measurable_im.comp hval)).prodMk
      (Complex.measurable_im.comp hval).subtype_mk
  let eP : ℝ × Y1 ≃ᵐ P :=
    { toFun := fun p => pt p.1 p.2.1 p.2.2
      invFun := fun z => (z.1.re / z.1.im, ⟨z.1.im, z.2⟩)
      left_inv := by
        rintro ⟨x, y, hy⟩
        have h1 : ((y : ℂ) * ((x : ℂ) + Complex.I)).re = y * x := by simp
        have h2 : ((y : ℂ) * ((x : ℂ) + Complex.I)).im = y := by simp
        refine Prod.ext ?_ (Subtype.ext ?_)
        · show ((y : ℂ) * ((x : ℂ) + Complex.I)).re / ((y : ℂ) * ((x : ℂ) + Complex.I)).im = x
          rw [h1, h2]
          field_simp
        · show ((y : ℂ) * ((x : ℂ) + Complex.I)).im = y
          exact h2
      right_inv := by
        intro z
        apply Subtype.ext
        show ((z.1.im : ℂ) * (((z.1.re / z.1.im : ℝ) : ℂ) + Complex.I)) = z.1
        have hz : z.1.im ≠ 0 := z.2
        apply Complex.ext
        · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
            Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]
          field_simp
        · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
            Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add, mul_one]
      measurable_toFun := hcont.measurable
      measurable_invFun := hgm }
  have hmpP : MeasurePreserving eP ((volume : Measure ℝ).prod nu1) (volume : Measure P) := hmp
  have hmpX : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : I => eP)
      (Measure.pi fun _ : I => (volume : Measure ℝ).prod nu1) (Measure.pi fun _ : I => (volume : Measure P)) :=
    measurePreserving_pi _ _ fun _ => hmpP
  have hmpA : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1))
      (Measure.pi fun _ : I => (volume : Measure ℝ).prod nu1) :=
    MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow ℝ Y1 I (fun _ => volume) (fun _ => nu1))
  let Φ : (I → ℝ) × (I → Y1) ≃ᵐ X I :=
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm.trans (MeasurableEquiv.piCongrRight fun _ : I => eP)
  have hΦ : MeasurePreserving Φ ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) (volume : Measure (X I)) := hmpX.comp hmpA
  have hΦapp : ∀ (x : I → ℝ) (y : I → Y1), Φ (x, y) = fun v => pt (x v) (y v).1 (y v).2 := fun x y => rfl
  obtain ⟨b, hbdef⟩ : ∃ b : (I → Y1) → ℝ, b = fun y => β (Φ (0, y)) := ⟨_, rfl⟩
  have hb : Measurable b := by
    rw [hbdef]
    exact hβ.comp (Φ.measurable.comp (measurable_const.prodMk measurable_id))
  have hb0 : ∀ y, 0 ≤ b y := by
    rw [hbdef]
    exact fun y => hβ0 _
  have hβΦ : ∀ (x : I → ℝ) (y : I → Y1), β (Φ (x, y)) = b y := by
    intro x y
    rw [hbdef]
    show β (Φ (x, y)) = β (Φ (0, y))
    rw [hΦapp, hΦapp]
    refine (hβinv x 0 (fun v => (y v).1) (fun v => (y v).2) 1 one_pos).trans ?_
    congr 1
    funext v
    exact pt_congr rfl (one_mul _) _ _
  have huΦ : ∀ (x : I → ℝ) (y : I → Y1), u (Φ (x, y)) = (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) := by
    intro x y
    rw [hΦapp]
    exact hu x (fun v => (y v).1) (fun v => (y v).2)
  have hint' : Integrable (fun p : (I → ℝ) × (I → Y1) => b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0)) ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) := by
    refine ((hΦ.integrable_comp_emb Φ.measurableEmbedding).mpr hint).congr
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p
    show β (Φ (x, y)) • u (Φ (x, y)) = _
    rw [hβΦ, huΦ]
  have hI : ∫ z, β z • u z = ∫ p : (I → ℝ) × (I → Y1), b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0) ∂((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) := by
    refine (hΦ.integral_comp' (fun z => β z • u z)).symm.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p
    show β (Φ (x, y)) • u (Φ (x, y)) = _
    rw [hβΦ, huΦ]
  have hcond : ∀ (x : I → ℝ) (y : I → Y1), (A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B) ↔ large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) := by
    intro x y
    have hp : 0 < ∏ v, |(y v).1| := Finset.prod_pos fun v _ => abs_pos.mpr (y v).2
    have hq : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun v _ => by positivity
    have hL : large₂ y = Real.log (∏ v, |(y v).1|) := by
      show ∑ v, Real.log |(y v).1| = _
      rw [Real.log_prod (s := Finset.univ) (f := fun v => |(y v).1|) fun v _ => abs_ne_zero.mpr (y v).2]
    have hM : Real.log (A / ∏ v, (1 + x v ^ 2)) = (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) := by
      rw [Real.log_div hA.ne' hq.ne',
        Real.log_prod (s := Finset.univ) (f := fun v => 1 + x v ^ 2) fun v _ => by positivity]
    rw [Set.mem_Icc, hL, ← hM, Real.log_le_log_iff (div_pos hA hq) hp,
      Real.log_le_log_iff hp (hA.trans hAB)]
  obtain ⟨m, hm⟩ : ∃ m : Measure ℝ, m = Measure.map (large₂ (I := I)) ((Measure.pi fun _ : I => nu1).withDensity fun y => ENNReal.ofReal (b y)) :=
    ⟨_, rfl⟩
  have hinner : ∀ x : I → ℝ, ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) =
      (∏ v, φ v (x v)) * (((m (Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B))).toReal : ℝ) : ℂ) := by
    intro x
    have hS : MeasurableSet ((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)) := measurable_Lg measurableSet_Icc
    have e1 : (fun y : I → Y1 => b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0)) = fun y =>
        ((((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)).indicator b y : ℝ) : ℂ) * ∏ v, φ v (x v) := by
      funext y
      by_cases h : large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)
      · rw [if_pos ((hcond x y).mpr h),
          Set.indicator_of_mem (show y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) from h), Complex.real_smul]
      · rw [if_neg (fun h' => h ((hcond x y).mp h')),
          Set.indicator_of_notMem (show y ∉ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B) from h), smul_zero]
        simp
    rw [e1, integral_mul_const, integral_complex_ofReal, integral_indicator hS, mul_comm]
    congr 2
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hb0 y) hb.aestronglyMeasurable, hm,
      Measure.map_apply measurable_Lg measurableSet_Icc, withDensity_apply _ hS]
  have hscl : ∀ (t : ℝ) (ht : 0 < t),
      MeasurePreserving (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) (Measure.pi fun _ : I => nu1) (Measure.pi fun _ : I => nu1) :=
    fun t ht => measurePreserving_pi (fun _ : I => nu1) (fun _ : I => nu1) fun _ => measurePreserving_scl t ht.ne'
  have hbscl : ∀ (t : ℝ) (ht : 0 < t) (y : I → Y1), b (fun v => scl t ht.ne' (y v)) = b y := by
    intro t ht y
    rw [hbdef]
    exact (hβinv 0 0 (fun v => (y v).1) (fun v => (y v).2) t ht).symm
  have hminv : ∀ c : ℝ, ∀ S : Set ℝ, MeasurableSet S → m ((fun x => c + x) ⁻¹' S) = m S := by
    intro c S hS
    have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hcard' : (Fintype.card I : ℝ) ≠ 0 := hcard.ne'
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = Real.exp (c / Fintype.card I) := ⟨_, rfl⟩
    have ht : 0 < t := by rw [ht_def]; exact Real.exp_pos _
    have hlog : (Fintype.card I : ℝ) * Real.log t = c := by
      rw [ht_def, Real.log_exp]
      field_simp
    have hS' : MeasurableSet ((large₂ (I := I)) ⁻¹' S) := measurable_Lg hS
    have hadd : Measurable (fun x : ℝ => c + x) := (continuous_add_left c).measurable
    have hpre : (large₂ (I := I)) ⁻¹' ((fun x => c + x) ⁻¹' S) =
        (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) := by
      ext y
      simp only [Set.mem_preimage]
      rw [Lg_scl t ht y, hlog]
    have hpm : MeasurableSet ((fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S)) :=
      (hscl t ht).measurable hS'
    have hmi : Measurable (((large₂ (I := I)) ⁻¹' S).indicator fun y => ENNReal.ofReal (b y)) :=
      (ENNReal.measurable_ofReal.comp hb).indicator hS'
    rw [hm, Measure.map_apply measurable_Lg (hadd hS), Measure.map_apply measurable_Lg hS, hpre,
      withDensity_apply _ hpm, withDensity_apply _ hS', ← lintegral_indicator hpm, ← lintegral_indicator hS',
      ← (hscl t ht).lintegral_comp hmi]
    congr 1
    funext y
    by_cases hy : (fun v => scl t ht.ne' (y v)) ∈ (large₂ (I := I)) ⁻¹' S
    · rw [Set.indicator_of_mem (show y ∈ (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) from hy),
        Set.indicator_of_mem hy, hbscl t ht y]
    · rw [Set.indicator_of_notMem (show y ∉ (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' ((large₂ (I := I)) ⁻¹' S) from hy),
        Set.indicator_of_notMem hy]
  have hlogAB : Real.log A < Real.log B := Real.log_lt_log hA hAB
  have hsum0 : ∀ x : I → ℝ, 0 ≤ ∑ v, Real.log (1 + x v ^ 2) := fun x =>
    Finset.sum_nonneg fun v _ => Real.log_nonneg (by linarith [sq_nonneg (x v)])
  have hlt : ∀ x : I → ℝ, (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) < Real.log B := fun x => by linarith [hsum0 x]
  have hP0 : ∀ x : I → ℝ, (∏ v, φ v (x v)) ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.mpr fun v _ => (hφ v).2.2.2.2 (x v)
  have : (ae (volume : Measure (I → ℝ))).NeBot := ae_neBot.mpr (NeZero.ne _)
  obtain ⟨x0, hx0⟩ := hint'.prod_right_ae.exists
  have hS0 : MeasurableSet ((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)) := measurable_Lg measurableSet_Icc
  have hTint : Integrable (((large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)).indicator b) (Measure.pi fun _ : I => nu1) := by
    refine (hx0.norm.div_const ‖∏ v, φ v (x0 v)‖).congr (Filter.Eventually.of_forall fun y => ?_)
    show ‖b y • (if A / ∏ v, (1 + x0 v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x0 v) else 0)‖ / ‖∏ v, φ v (x0 v)‖ = _
    by_cases h : large₂ y ∈ Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)
    · rw [if_pos ((hcond x0 y).mpr h),
        Set.indicator_of_mem (show y ∈ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) from h), norm_smul,
        Real.norm_of_nonneg (hb0 y), mul_div_assoc, div_self (norm_ne_zero_iff.mpr (hP0 x0)), mul_one]
    · rw [if_neg (fun h' => h ((hcond x0 y).mp h')),
        Set.indicator_of_notMem (show y ∉ (large₂ (I := I)) ⁻¹' Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B) from h), smul_zero,
        norm_zero, zero_div]
  have hfin : m (Set.Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)) ≠ ⊤ := by
    rw [hm, Measure.map_apply measurable_Lg measurableSet_Icc, withDensity_apply _ hS0,
      ← lintegral_indicator hS0]
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hTint.lintegral_lt_top)
    congr 1
    funext y
    simp only [Set.indicator]
    split_ifs <;> simp
  obtain ⟨R, hR⟩ := haar_Icc m hminv (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B - (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2))) (by linarith [hlt x0])
    (by rwa [show (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) + (Real.log B - (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2))) = Real.log B by ring])
  have hR' : ∀ x : I → ℝ, ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) =
      (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) := by
    intro x
    rw [hinner x, hR _ _ (hlt x).le,
      show Real.log B - (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) = (Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2) by ring]
  rw [hI, integral_prod _ hint']
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => hR' x)).trans ?_
  exact integral_prod_log φ (fun v => ⟨(hφ v).2.1, (hφ v).2.2.1, (hφ v).2.2.2.1⟩) R (Real.log B - Real.log A)
