import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs

noncomputable section

open MeasureTheory Filter Topology Metric

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

/- English proof (translation)
Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)` as an intermediate fact. Simplify using `using this`.
-/
theorem cardAddB {m : ℕ} (ε : Fin m → Bool) :
    (Finset.univ.filter fun a => ε a = true).card + (Finset.univ.filter fun a => ε a = false).card = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simpa using this

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.
-/
theorem nexpB (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/- English proof (translation)
Unfold `ip`. Use `fun_prop`.
-/
theorem contIpB {n : ℕ} (y : E n) : Continuous fun β : E n => ip β y := by
  unfold ip
  fun_prop

/- English proof (translation)
Introduce `m n ε c t hc ht P N hN`. Take `⟨hTr, hHq, hHinv, hDet, hQc⟩` from `hA m n ε`. Establish `ht0 : t ≠ 0`. Break down `ht with rfl | rfl` into its components or cases. Conclude with `hc.ne'`.

Conclude with `neg_ne_zero.mpr hc.ne'`. Establish `hIt : (Complex.I * (t : ℂ)) ≠ 0` using `mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)`. Establish `hsec : ∀ (Q : PX m n) (y : E n), secN ε c t Q (herm y) = FP ε c t Q y`. Introduce `Q y`. Simplify using `only [secN, FP, hTr]`.

Take `⟨P', hP'⟩ : ∃ P' : PX m n, P' = (MvPolynomial.C ((Complex.I * (t : ℂ)) ^ n) * detQ ε) ^ N * P` from `⟨_, rfl⟩`. Establish `hev : ∀ x : Fin m → Fin n → ℂ, evX P' x = ((Complex.I * (t : ℂ)) ^ n * (gramX ε x).det) ^ N * evX P x`. Introduce `x`. Rewrite using `[← hDet x, hP']`. Simplify using `only [evX, map_mul, map_pow, MvPolynomial.eval_C]`.

Establish `hDP' : Delta^[N] (FP ε c t P) = FP ε c t P'`. Rewrite using `[hP']`. Conclude with `(hD m n ε c t hc P N).2`. Establish `hFP'c : Continuous (FP ε c t P')` using `(hD m n ε c t hc P' N).1`. Take `⟨R, hR⟩` from `hG m n ε c t hc ht P`.

Establish `hpq` using `cardAddB ε`. Generalize the expression as in `hp : (Finset.univ.filter fun i => ε i = true).card = p at hR hpq`. Generalize the expression as in `hq : (Finset.univ.filter fun i => ε i = false).card = q at hR hpq`. Establish `hs : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1`. Break down `ht with rfl | rfl` into its components or cases.

Use `left`. Rewrite using `[div_self hc.ne']`. Simplify using the standard rewrite rules. Use `right`. Rewrite using `[neg_div, div_self hc.ne']`.

Simplify using the standard rewrite rules. Take `⟨J, a, G, hGc, ⟨C, hC⟩, hGeq⟩` from `hCG n _ hs p q N R`. Establish `hFPcls : FP ε c t P = cls ((t / c : ℝ) : ℂ) 0 p q R`. Use function extensionality and compare the values at `y`. Rewrite using `[← hsec]`.

Conclude with `hR y`. Establish `hFP'eq : ∀ y, FP ε c t P' y = ∑ j : Fin J, Polynomial.eval 0 (a j) * G j y`. Introduce `y`. Rewrite using `[← hDP', hFPcls, hGeq]`. Simplify using the standard rewrite rules.

Establish `hbd : ∀ y, ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2))`. Introduce `y`. Rewrite using `[hFP'eq y, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hC j y) (norm_nonneg _)`. Establish `hσ : (n : ℝ) ^ 2 / 2 < ((p + q + N : ℕ) : ℝ) / 2`. Establish `h1 : ((n : ℝ)) ^ 2 < ((m + N : ℕ) : ℝ)` using `by exact_mod_cast hN`. Rewrite using `[hpq]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hFP'int : Integrable (FP ε c t P') volume`. Use `Integrable.mono' (((hInt n).2 _ hσ).const_mul ((∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C)) hFP'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[neg_div]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hipc : ∀ β y : E n, ip β y = ip y β`. Introduce `β y`. Simplify using `only [ip]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _`. Establish `hcy : ∀ β : E n, Continuous fun y : E n => ip β y` using `fun β => (contIpB β).congr (fun y => hipc y β)`.

Establish `hhc : Continuous fun β : E n => herm β`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [herm]`. Use `fun_prop`. Establish `hdc : Continuous fun β : E n => (herm β).det` using `hhc.matrix_det`.

Establish `hDc : Continuous fun β : E n => ((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N` using `(continuous_const.mul hdc).pow N`. Establish `hF : Continuous fun β : E n => ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))`. Use `continuous_of_dominated (bound := fun y => ‖FP ε c t P' y‖) (fun β => ?_) (fun β => Filter.Eventually.of_forall fun y => ?_) hFP'int.norm (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `hFP'c.aestronglyMeasurable.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (hcy β))).neg)).aestronglyMeasurable`. Rewrite using `[norm_mul, nexpB, mul_one]`.

Conclude with `continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (contIpB y))).neg))`. Take `⟨g, hg⟩ : ∃ g : E n → ℂ, g = fun β => (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹ * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))))` from `⟨_, rfl⟩`. Establish `hgU : ContinuousOn g {y : E n | (herm y).det ≠ 0}`. Rewrite using `[hg]`. Use `ContinuousOn.mul ?_ (continuous_const.mul hF).continuousOn` and prove the remaining obligations.

Conclude with `hDc.continuousOn.inv₀ (fun β hβ => pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβ))`. Establish `hgm : Measurable g`. Rewrite using `[hg]`. Conclude with `hDc.measurable.inv.mul (continuous_const.mul hF).measurable`. Establish `hcan : ∀ u v w D : ℂ, D ≠ 0 → u * (v * w) = u * D⁻¹ * (D * v * w)`.

Introduce `u v w D hD`. Rewrite using `[show u * D⁻¹ * (D * v * w) = u * (D⁻¹ * D) * (v * w) by ring, inv_mul_cancel₀ hD, mul_one]`. Establish `hA' : ∀ φ : E n → ℂ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {y : E n | (herm y).det ≠ 0} → ∫ x, φ (qX ε x) * (evX P x * gs c x) = ∫ β, φ β * g β`. Introduce `φ hφc hφs hφU`. Establish `hψc : Continuous (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹)`.

Apply `continuous_of_tsupport` to reduce the goal to its premises. Introduce `β hβ`. Establish `hβU : (herm β).det ≠ 0` using `hφU (tsupport_mul_subset_left hβ)`. Conclude with `hφc.continuousAt.mul (hDc.continuousAt.inv₀ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβU)))`. Establish `hψs : HasCompactSupport (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹)` using `hφs.mul_right`.

Establish `key2 : (∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x)) = ∫ β, (φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : …` using `hM n (Fin m → Fin n → ℂ) volume (fun x => evX P' x * gs c x) (qX ε) (hI m n c hc P') hQc.measurable t ht0 hFP'int _ hψc hψs`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[hev x]`.

Distinguish the cases in `h0 : φ (qX ε x) = 0`. Simplify using `[h0]`. Establish `hne : (herm (qX ε x)).det ≠ 0` using `hφU (subset_tsupport _ (Function.mem_support.mpr h0))`. Rewrite `hne` using `[hHq x]`. Rewrite using `[hHq x]`.

Conclude with `hcan _ _ _ _ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hne))`. Use `_ = _ := key2`. Use `_ = ∫ β, φ β * g β := by`. Use `congr 1`. Use function extensionality and compare the values at `β`.

Rewrite using `[hg]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨g, hgU, ?_, ?_⟩` and prove the remaining obligations. Introduce `S hS hSU`. Establish `hpre : gramX ε ⁻¹' (herm '' S) = qX ε ⁻¹' S`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩`. Establish `hyq : y = qX ε x`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hyq]`. Conclude with `hy`. Introduce `hx`. Conclude with `⟨qX ε x, hx, hHq x⟩`.

Rewrite using `[hpre]`. Establish `hUo : IsOpen {y : E n | (herm y).det ≠ 0}` using `isOpen_ne_fun hdc continuous_const`. Take `⟨δ, hδ, hδU⟩` from `hS.exists_cthickening_subset_open hUo hSU`. Establish `hK : IsCompact (Metric.cthickening δ S)` using `hS.cthickening`. Establish `hδk : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1)` using `fun k => div_pos hδ (Nat.cast_add_one_pos k)`.

Establish `hδt : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 1)) atTop (𝓝 0)`. Simplify `(tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ)` using `[div_eq_mul_inv]`. Establish `hle : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ` using `fun k => div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg k))`. Take `⟨φk, hφk⟩ : ∃ φk : ℕ → E n → ℂ, φk = fun k β => (((thickenedIndicator (hδk k) S β : NNReal) : ℝ) : ℂ)` from `⟨_, rfl⟩`. Establish `hφkc : ∀ k, Continuous (φk k)`.

Introduce `k`. Rewrite using `[hφk]`. Conclude with `Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (thickenedIndicator (hδk k) S).continuous)`. Establish `hφk0 : ∀ k β, β ∉ Metric.cthickening δ S → φk k β = 0`. Introduce `k β hβ`.

Rewrite using `[hφk]`. Simplify using `only`. Rewrite using `[thickenedIndicator_zero (hδk k) S (fun h => hβ (Metric.cthickening_mono (hle k) S (Metric.thickening_subset_cthickening _ _ h)))]`. Simplify using the standard rewrite rules. Establish `hφk1 : ∀ k β, ‖φk k β‖ ≤ 1`.

Introduce `k β`. Rewrite using `[hφk]`. Simplify using `only`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]`. Conclude with `thickenedIndicator_le_one (hδk k) S β` after adjusting the coercions.

Establish `hφks : ∀ k, HasCompactSupport (φk k)` using `fun k => HasCompactSupport.intro hK (hφk0 k)`. Establish `hφkU : ∀ k, tsupport (φk k) ⊆ {y : E n | (herm y).det ≠ 0}` using `fun k => (closure_minimal (Function.support_subset_iff'.2 (hφk0 k)) hK.isClosed).trans hδU`. Establish `hlim : ∀ β : E n, Tendsto (fun k : ℕ => φk k β) atTop (𝓝 (S.indicator (fun _ => (1 : ℂ)) β))`. Introduce `β`. Establish `h1` using `tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hδk hδt S) β`.

Rewrite `h1` using `[hS.isClosed.closure_eq]`. Establish `h2` using `((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1`. Rewrite using `[hφk]`. Distinguish the cases in `hβ : β ∈ S`. Simplify `h2` using `[hβ, Function.comp_def]`.

Simplify `h2` using `[hβ, Function.comp_def]`. Establish `hLt : Tendsto (fun k => ∫ x, φk k (qX ε x) * (evX P x * gs c x)) atTop (𝓝 (∫ x, S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x)))`. Use `tendsto_integral_of_dominated_convergence (fun x => ‖evX P x * gs c x‖) (fun k => ?_) (hI m n c hc P).norm (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `((hφkc k).comp hQc).aestronglyMeasurable.mul (hI m n c hc P).aestronglyMeasurable`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)`. Conclude with `(hlim (qX ε x)).mul_const _`. Establish `hgK : IntegrableOn g (Metric.cthickening δ S) volume` using `(hgU.mono hδU).integrableOn_compact hK`. Establish `hRt : Tendsto (fun k => ∫ β, φk k β * g β) atTop (𝓝 (∫ β, S.indicator (fun _ => (1 : ℂ)) β * g β))`. Use `tendsto_integral_of_dominated_convergence ((Metric.cthickening δ S).indicator fun β => ‖g β‖) (fun k => ?_) (IntegrableOn.integrable_indicator hgK.norm hK.measurableSet) (fun k => Filter.Eventually.of_forall fun β => ?_) (Filter.Eventually.of_forall fun β => (hlim β).mul_const _)` and prove the remaining obligations.

Conclude with `(hφkc k).aestronglyMeasurable.mul hgm.aestronglyMeasurable`. Distinguish the cases in `hβ : β ∈ Metric.cthickening δ S`. Rewrite using `[Set.indicator_of_mem hβ, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)`. Simplify using `[hβ, hφk0 k β hβ]`.

Establish `heq` using `tendsto_nhds_unique hLt (Filter.Tendsto.congr (fun k => (hA' (φk k) (hφkc k) (hφks k) (hφkU k)).symm) hRt)`. Rewrite using `[← integral_indicator (hQc.measurable hS.isClosed.measurableSet), ← integral_indicator hS.isClosed.measurableSet]`. Establish `e1 : ∀ x, (qX ε ⁻¹' S).indicator (fun x => evX P x * gs c x) x = S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x)`. Introduce `x`. Apply the tactic sequence `by_cases h : qX ε x ∈ S <;> simp [h]`.

Establish `e2 : ∀ β, S.indicator g β = S.indicator (fun _ => (1 : ℂ)) β * g β`. Introduce `β`. Apply the tactic sequence `by_cases h : β ∈ S <;> simp [h]`. Simplify using `only [e1, e2]`. Conclude with `heq`.

Introduce `β _`. Establish `hint : (∫ y : E n, Delta^[N] (fun y : E n => secN ε c t P (herm y)) y * chr t β y) = ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))`. Establish `hfun : (fun y : E n => secN ε c t P (herm y)) = FP ε c t P` using `funext (hsec P)`. Rewrite using `[hfun, hDP']`. Both sides reduce to the same expression.

Rewrite using `[hint, hg]`. Establish `h1 : ((-1 : ℂ) ^ n / (-(Complex.I * (t : ℂ))) ^ n) = ((Complex.I * (t : ℂ)) ^ n)⁻¹`. Rewrite using `[neg_pow (Complex.I * (t : ℂ)), div_mul_eq_div_div, div_self (pow_ne_zero _ (by norm_num)), one_div]`. Rewrite using `[h1]`. Establish `hab : (((2 * Real.pi / |t|) ^ n ^ 2 : ℝ) : ℂ) * (((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) = 1`.

Rewrite using `[← Complex.ofReal_mul, ← mul_pow, div_mul_div_comm, mul_comm (2 * Real.pi) |t|, div_self (mul_ne_zero (abs_ne_zero.mpr ht0) (by positivity)), one_pow, Complex.ofReal_one]`. Take the linear combination `(((herm β).det ^ N)⁻¹ * (((Complex.I * (t : ℂ)) ^ n)⁻¹) ^ N * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) * hab`.
-/
theorem dens_of (hA : AlgA) (hI : IntG) (hD : DerivF) (hM : MollId) (hG : Gauss) (hCG : ClsGain)
    (hInt : Integr) : Dens := by
  intro m n ε c t hc ht P N hN
  obtain ⟨hTr, hHq, hHinv, hDet, hQc⟩ := hA m n ε
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.mpr hc.ne'
  have hIt : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)
  have hsec : ∀ (Q : PX m n) (y : E n), secN ε c t Q (herm y) = FP ε c t Q y := by
    intro Q y
    simp only [secN, FP, hTr]
  obtain ⟨P', hP'⟩ : ∃ P' : PX m n, P' = (MvPolynomial.C ((Complex.I * (t : ℂ)) ^ n) * detQ ε) ^ N * P := ⟨_, rfl⟩
  have hev : ∀ x : Fin m → Fin n → ℂ, evX P' x = ((Complex.I * (t : ℂ)) ^ n * (gramX ε x).det) ^ N * evX P x := by
    intro x
    rw [← hDet x, hP']
    simp only [evX, map_mul, map_pow, MvPolynomial.eval_C]
  have hDP' : Delta^[N] (FP ε c t P) = FP ε c t P' := by
    rw [hP']
    exact (hD m n ε c t hc P N).2
  have hFP'c : Continuous (FP ε c t P') := (hD m n ε c t hc P' N).1
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have hpq := cardAddB ε
  generalize hp : (Finset.univ.filter fun i => ε i = true).card = p at hR hpq
  generalize hq : (Finset.univ.filter fun i => ε i = false).card = q at hR hpq
  have hs : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left
      rw [div_self hc.ne']
      simp
    · right
      rw [neg_div, div_self hc.ne']
      simp
  obtain ⟨J, a, G, hGc, ⟨C, hC⟩, hGeq⟩ := hCG n _ hs p q N R
  have hFPcls : FP ε c t P = cls ((t / c : ℝ) : ℂ) 0 p q R := by
    funext y
    rw [← hsec]
    exact hR y
  have hFP'eq : ∀ y, FP ε c t P' y = ∑ j : Fin J, Polynomial.eval 0 (a j) * G j y := by
    intro y
    rw [← hDP', hFPcls, hGeq]
    simp
  have hbd : ∀ y, ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := by
    intro y
    rw [hFP'eq y, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC j y) (norm_nonneg _)
  have hσ : (n : ℝ) ^ 2 / 2 < ((p + q + N : ℕ) : ℝ) / 2 := by
    have h1 : ((n : ℝ)) ^ 2 < ((m + N : ℕ) : ℝ) := by exact_mod_cast hN
    rw [hpq]
    linarith
  have hFP'int : Integrable (FP ε c t P') volume := by
    refine Integrable.mono' (((hInt n).2 _ hσ).const_mul ((∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C)) hFP'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := hbd y
      _ = (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := by
        rw [neg_div]
        ring
  have hipc : ∀ β y : E n, ip β y = ip y β := by
    intro β y
    simp only [ip]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hcy : ∀ β : E n, Continuous fun y : E n => ip β y := fun β => (contIpB β).congr (fun y => hipc y β)
  have hhc : Continuous fun β : E n => herm β := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hdc : Continuous fun β : E n => (herm β).det := hhc.matrix_det
  have hDc : Continuous fun β : E n => ((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N := (continuous_const.mul hdc).pow N
  have hF : Continuous fun β : E n => ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
    refine continuous_of_dominated (bound := fun y => ‖FP ε c t P' y‖) (fun β => ?_) (fun β => Filter.Eventually.of_forall fun y => ?_) hFP'int.norm (Filter.Eventually.of_forall fun y => ?_)
    · exact hFP'c.aestronglyMeasurable.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (hcy β))).neg)).aestronglyMeasurable
    · rw [norm_mul, nexpB, mul_one]
    · exact continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (contIpB y))).neg))
  obtain ⟨g, hg⟩ : ∃ g : E n → ℂ, g = fun β => (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹ * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) := ⟨_, rfl⟩
  have hgU : ContinuousOn g {y : E n | (herm y).det ≠ 0} := by
    rw [hg]
    refine ContinuousOn.mul ?_ (continuous_const.mul hF).continuousOn
    exact hDc.continuousOn.inv₀ (fun β hβ => pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβ))
  have hgm : Measurable g := by
    rw [hg]
    exact hDc.measurable.inv.mul (continuous_const.mul hF).measurable
  have hcan : ∀ u v w D : ℂ, D ≠ 0 → u * (v * w) = u * D⁻¹ * (D * v * w) := by
    intro u v w D hD
    rw [show u * D⁻¹ * (D * v * w) = u * (D⁻¹ * D) * (v * w) by ring, inv_mul_cancel₀ hD, mul_one]
  have hA' : ∀ φ : E n → ℂ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {y : E n | (herm y).det ≠ 0} →
      ∫ x, φ (qX ε x) * (evX P x * gs c x) = ∫ β, φ β * g β := by
    intro φ hφc hφs hφU
    have hψc : Continuous (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := by
      apply continuous_of_tsupport
      intro β hβ
      have hβU : (herm β).det ≠ 0 := hφU (tsupport_mul_subset_left hβ)
      exact hφc.continuousAt.mul (hDc.continuousAt.inv₀ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβU)))
    have hψs : HasCompactSupport (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := hφs.mul_right
    have key2 : (∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x)) = ∫ β, (φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) :=
      hM n (Fin m → Fin n → ℂ) volume (fun x => evX P' x * gs c x) (qX ε) (hI m n c hc P') hQc.measurable t ht0 hFP'int _ hψc hψs
    calc (∫ x, φ (qX ε x) * (evX P x * gs c x)) = ∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x) := by
          congr 1
          funext x
          rw [hev x]
          by_cases h0 : φ (qX ε x) = 0
          · simp [h0]
          · have hne : (herm (qX ε x)).det ≠ 0 := hφU (subset_tsupport _ (Function.mem_support.mpr h0))
            rw [hHq x] at hne
            rw [hHq x]
            exact hcan _ _ _ _ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hne))
      _ = _ := key2
      _ = ∫ β, φ β * g β := by
          congr 1
          funext β
          rw [hg]
          ring
  refine ⟨g, hgU, ?_, ?_⟩
  · intro S hS hSU
    have hpre : gramX ε ⁻¹' (herm '' S) = qX ε ⁻¹' S := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyq : y = qX ε x := by
          calc y = hinv (herm y) := (hHinv y).symm
            _ = hinv (herm (qX ε x)) := by rw [hyx, hHq]
            _ = qX ε x := hHinv _
        rw [← hyq]
        exact hy
      · intro hx
        exact ⟨qX ε x, hx, hHq x⟩
    rw [hpre]
    have hUo : IsOpen {y : E n | (herm y).det ≠ 0} := isOpen_ne_fun hdc continuous_const
    obtain ⟨δ, hδ, hδU⟩ := hS.exists_cthickening_subset_open hUo hSU
    have hK : IsCompact (Metric.cthickening δ S) := hS.cthickening
    have hδk : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1) := fun k => div_pos hδ (Nat.cast_add_one_pos k)
    have hδt : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ)
    have hle : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ := fun k => div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg k))
    obtain ⟨φk, hφk⟩ : ∃ φk : ℕ → E n → ℂ, φk = fun k β => (((thickenedIndicator (hδk k) S β : NNReal) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hφkc : ∀ k, Continuous (φk k) := by
      intro k
      rw [hφk]
      exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (thickenedIndicator (hδk k) S).continuous)
    have hφk0 : ∀ k β, β ∉ Metric.cthickening δ S → φk k β = 0 := by
      intro k β hβ
      rw [hφk]
      simp only
      rw [thickenedIndicator_zero (hδk k) S (fun h => hβ (Metric.cthickening_mono (hle k) S (Metric.thickening_subset_cthickening _ _ h)))]
      simp
    have hφk1 : ∀ k β, ‖φk k β‖ ≤ 1 := by
      intro k β
      rw [hφk]
      simp only
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast thickenedIndicator_le_one (hδk k) S β
    have hφks : ∀ k, HasCompactSupport (φk k) := fun k => HasCompactSupport.intro hK (hφk0 k)
    have hφkU : ∀ k, tsupport (φk k) ⊆ {y : E n | (herm y).det ≠ 0} := fun k =>
      (closure_minimal (Function.support_subset_iff'.2 (hφk0 k)) hK.isClosed).trans hδU
    have hlim : ∀ β : E n, Tendsto (fun k : ℕ => φk k β) atTop (𝓝 (S.indicator (fun _ => (1 : ℂ)) β)) := by
      intro β
      have h1 := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hδk hδt S) β
      rw [hS.isClosed.closure_eq] at h1
      have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1
      rw [hφk]
      by_cases hβ : β ∈ S
      · simpa [hβ, Function.comp_def] using h2
      · simpa [hβ, Function.comp_def] using h2
    have hLt : Tendsto (fun k => ∫ x, φk k (qX ε x) * (evX P x * gs c x)) atTop (𝓝 (∫ x, S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x))) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖evX P x * gs c x‖) (fun k => ?_) (hI m n c hc P).norm (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
      · exact ((hφkc k).comp hQc).aestronglyMeasurable.mul (hI m n c hc P).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
      · exact (hlim (qX ε x)).mul_const _
    have hgK : IntegrableOn g (Metric.cthickening δ S) volume := (hgU.mono hδU).integrableOn_compact hK
    have hRt : Tendsto (fun k => ∫ β, φk k β * g β) atTop (𝓝 (∫ β, S.indicator (fun _ => (1 : ℂ)) β * g β)) := by
      refine tendsto_integral_of_dominated_convergence ((Metric.cthickening δ S).indicator fun β => ‖g β‖) (fun k => ?_) (IntegrableOn.integrable_indicator hgK.norm hK.measurableSet) (fun k => Filter.Eventually.of_forall fun β => ?_) (Filter.Eventually.of_forall fun β => (hlim β).mul_const _)
      · exact (hφkc k).aestronglyMeasurable.mul hgm.aestronglyMeasurable
      · by_cases hβ : β ∈ Metric.cthickening δ S
        · rw [Set.indicator_of_mem hβ, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
        · simp [hβ, hφk0 k β hβ]
    have heq := tendsto_nhds_unique hLt (Filter.Tendsto.congr (fun k => (hA' (φk k) (hφkc k) (hφks k) (hφkU k)).symm) hRt)
    rw [← integral_indicator (hQc.measurable hS.isClosed.measurableSet), ← integral_indicator hS.isClosed.measurableSet]
    have e1 : ∀ x, (qX ε ⁻¹' S).indicator (fun x => evX P x * gs c x) x = S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x) := by
      intro x
      by_cases h : qX ε x ∈ S <;> simp [h]
    have e2 : ∀ β, S.indicator g β = S.indicator (fun _ => (1 : ℂ)) β * g β := by
      intro β
      by_cases h : β ∈ S <;> simp [h]
    simp only [e1, e2]
    exact heq
  · intro β _
    have hint : (∫ y : E n, Delta^[N] (fun y : E n => secN ε c t P (herm y)) y * chr t β y) = ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
      have hfun : (fun y : E n => secN ε c t P (herm y)) = FP ε c t P := funext (hsec P)
      rw [hfun, hDP']
      rfl
    rw [hint, hg]
    have h1 : ((-1 : ℂ) ^ n / (-(Complex.I * (t : ℂ))) ^ n) = ((Complex.I * (t : ℂ)) ^ n)⁻¹ := by
      rw [neg_pow (Complex.I * (t : ℂ)), div_mul_eq_div_div, div_self (pow_ne_zero _ (by norm_num)), one_div]
    rw [h1]
    have hab : (((2 * Real.pi / |t|) ^ n ^ 2 : ℝ) : ℂ) * (((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← mul_pow, div_mul_div_comm, mul_comm (2 * Real.pi) |t|, div_self (mul_ne_zero (abs_ne_zero.mpr ht0) (by positivity)), one_pow, Complex.ofReal_one]
    linear_combination (((herm β).det ^ N)⁻¹ * (((Complex.I * (t : ℂ)) ^ n)⁻¹) ^ N * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) * hab

end PositivityTheory.Rg.Sw.WR.D
