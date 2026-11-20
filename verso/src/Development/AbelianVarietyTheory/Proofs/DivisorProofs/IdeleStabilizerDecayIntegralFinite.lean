import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleDecayMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerIsOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiIdealBound.MinkReal

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleArchBound

open scoped ENNReal

section Abstract

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Establish `hc : Continuous fun x => |(L x).det|` using `(ContinuousLinearMap.continuous_det.comp L.continuous).abs`. Take `⟨C, hC⟩` from `((isCompact_closedBall (0 : V) 1).image hc).bddAbove`. Use `⟨max C 0, le_max_right _ _, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : 0 < 1 + ‖x‖` using `by positivity`. Use `set y : V := (1 + ‖x‖)⁻¹ • x with hy`.

Establish `hy1 : y ∈ Metric.closedBall (0 : V) 1`. Rewrite using `[mem_closedBall_zero_iff, hy, norm_smul, norm_inv, Real.norm_of_nonneg h1.le, inv_mul_le_iff₀ h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx : x = (1 + ‖x‖) • y` using `by rw [hy, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]`. Establish `hd : (L x).det = (1 + ‖x‖) ^ Module.finrank ℝ V * (L y).det` using `by conv_lhs => rw [hx, map_smul]`.

Conclude with `LinearMap.det_smul _ _`. Rewrite using `[hd, abs_mul, abs_of_pos (pow_pos h1 _), mul_comm]`. Use `gcongr`. Conclude with `(hC ⟨y, hy1, rfl⟩).trans (le_max_left _ _)`.
-/
theorem exists_det_le (L : V →L[ℝ] V →L[ℝ] V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |(L x).det| ≤ C * (1 + ‖x‖) ^ Module.finrank ℝ V := by
  have hc : Continuous fun x => |(L x).det| := (ContinuousLinearMap.continuous_det.comp L.continuous).abs
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : V) 1).image hc).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have h1 : 0 < 1 + ‖x‖ := by positivity
  set y : V := (1 + ‖x‖)⁻¹ • x with hy
  have hy1 : y ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, hy, norm_smul, norm_inv, Real.norm_of_nonneg h1.le, inv_mul_le_iff₀ h1]
    linarith
  have hx : x = (1 + ‖x‖) • y := by rw [hy, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]
  have hd : (L x).det = (1 + ‖x‖) ^ Module.finrank ℝ V * (L y).det := by
    conv_lhs => rw [hx, map_smul]
    exact LinearMap.det_smul _ _
  rw [hd, abs_mul, abs_of_pos (pow_pos h1 _), mul_comm]
  gcongr
  exact (hC ⟨y, hy1, rfl⟩).trans (le_max_left _ _)

variable [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `exists_det_le L`. Use `set n := Module.finrank ℝ V`. Establish `hI` using `(integrable_one_add_norm (μ := ν) (r := (n + 1 : ℕ)) (by push_cast; linarith)).const_mul (C ^ k)`. Use `lt_of_le_of_lt (lintegral_mono fun x => ?_) hI.lintegral_lt_top` and prove the remaining obligations. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Establish `h1 : 0 < 1 + ‖x‖` using `by positivity`. Rewrite using `[Real.rpow_neg h1.le, Real.rpow_natCast]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_det_lt_top (L : V →L[ℝ] V →L[ℝ] V) (ν : Measure V) [ν.IsAddHaarMeasure] (k : ℕ) :
    ∫⁻ x, ENNReal.ofReal (((1 + ‖x‖) ^ (Module.finrank ℝ V * (k + 1) + 1))⁻¹ * |(L x).det| ^ k) ∂ν < ⊤ := by
  obtain ⟨C, hC0, hC⟩ := exists_det_le L
  set n := Module.finrank ℝ V
  have hI := (integrable_one_add_norm (μ := ν) (r := (n + 1 : ℕ)) (by push_cast; linarith)).const_mul (C ^ k)
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hI.lintegral_lt_top
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 0 < 1 + ‖x‖ := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_natCast]
  calc ((1 + ‖x‖) ^ (n * (k + 1) + 1))⁻¹ * |(L x).det| ^ k
      ≤ ((1 + ‖x‖) ^ (n * (k + 1) + 1))⁻¹ * (C * (1 + ‖x‖) ^ n) ^ k := by gcongr; exact hC x
    _ = C ^ k * ((1 + ‖x‖) ^ (n + 1))⁻¹ := by
      field_simp
      ring

/- English proof (translation)
Use `set N := Module.finrank ℝ V * (k + 1) + 1`. Set `ν : Measure V` to `Measure.addHaar`. Establish `hc : Continuous fun x => |(L x).det|` using `(ContinuousLinearMap.continuous_det.comp L.continuous).abs`. Establish `hdet : ∀ g h, (L (p (g * h))).det = (L (p g)).det * (L (p h)).det` using `fun g h => by`. Rewrite using `[hL]`.

Conclude with `LinearMap.det_comp _ _`. Establish `hdet1 : (L (p 1)).det = 1` using `by rw [hone]; exact LinearMap.det_id`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hU⟩ : ∃ δ > 0, ∀ y ∈ Metric.ball (p 1) δ, 1 / 2 < |(L y).det| ∧ ‖L y - ContinuousLinearMap.id ℝ V‖ < 1 / 2 := by`. Establish `ho` using `(isOpen_lt (continuous_const (y := (1 / 2 : ℝ))) hc).inter (isOpen_lt (L.continuous.sub (continuous_const (y := ContinuousLinearMap.id ℝ V))).norm (continuous_const (y := (1 / 2 : ℝ))))`. Take `⟨δ, hδ, h⟩` from `Metric.isOpen_iff.1 ho (p 1) ⟨by simp only [Set.mem_ofPred_eq, hdet1]; norm_num, by simp [hone]⟩`.

Conclude with `⟨δ, hδ, fun y hy => h hy⟩`. Use `set U := Metric.ball (p 1) δ`. Establish `hUn : ∀ y ∈ U, ‖y‖ ≤ ‖p 1‖ + δ` using `fun y hy => by`. Use `norm_sub_norm_le y (p 1)` as an intermediate fact. Use `mem_ball_iff_norm.1 hy` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set T : Set G := {g | g ∈ S ∧ p g⁻¹ ∈ U}`. Establish `hT : μ T < ⊤`. Use `lt_of_le_of_lt (measure_mono fun g hg => ?_) (hfin (2 * ‖p 1‖ + δ))` and prove the remaining obligations. Use `⟨hg.1, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : p g = p 1 - (L (p g⁻¹) - ContinuousLinearMap.id ℝ V) (p g)`. Simplify using `[← hp]`. Establish `h2` using `(L (p g⁻¹) - ContinuousLinearMap.id ℝ V).le_opNorm (p g)`. Establish `h3` using `mul_le_mul_of_nonneg_right (hU _ hg.2).2.le (norm_nonneg (p g))`. Establish `h4` using `norm_sub_le (p 1) ((L (p g⁻¹) - ContinuousLinearMap.id ℝ V) (p g))`.

Rewrite `h4` using `[← h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hUn _ hg.2` as an intermediate fact. Combine the linear relations using `[norm_nonneg (p 1)]`. Establish `hpt : ∀ g x, g ∈ S → L (p g⁻¹) x ∈ U → ∃ h ∈ S, p h ∈ U ∧ x = p (g * h)`.

Introduce `g x _ hx`. Take `⟨h, hh, he⟩` from `hsurj _ (abs_pos.1 (lt_trans (by norm_num) (hU _ hx).1))`. Use `⟨h, hh, he ▸ hx, ?_⟩` and prove the remaining obligations. Rewrite using `[hp, he, ← ContinuousLinearMap.comp_apply, ← hL, mul_inv_cancel, hone, ContinuousLinearMap.id_apply]`. Use `set f : V → ℝ≥0∞ := fun x => ENNReal.ofReal (((1 + ‖x‖) ^ N)⁻¹ * |(L x).det| ^ k)`.

Establish `hfm : Measurable f` using `((((measurable_const.add measurable_norm).pow_const N).inv).mul (hc.measurable.pow_const k)).ennreal_ofReal`. Establish `hf : ∫⁻ x, f x ∂ν < ⊤` using `lintegral_det_lt_top L ν k`. Use `set A : Set (G × V) := {q | q.1 ∈ S ∧ L (p q.1⁻¹) q.2 ∈ U}`. Establish `hA : MeasurableSet A`. Establish `h2 : Continuous fun q : V × V => L q.1 q.2` using `L.continuous₂`.

Conclude with `(measurable_fst hS).inter ((h2.measurable.comp (((hpm.comp measurable_inv).comp measurable_fst).prodMk measurable_snd)) Metric.isOpen_ball.measurableSet)`. Establish `hΦ : Measurable (A.indicator fun q => f q.2)` using `(hfm.comp measurable_snd).indicator hA`. Establish `hswap` using `lintegral_lintegral_swap (μ := μ) (ν := ν) (f := fun g x => A.indicator (fun q => f q.2) (g, x)) hΦ.aemeasurable`. Establish `hup : ∀ x, ∫⁻ g, A.indicator (fun q => f q.2) (g, x) ∂μ ≤ μ T * f x`. Introduce `x`.

Distinguish the cases in `hx : ∃ g, (g, x) ∈ A`. Take `⟨g₀, hg₀⟩` from `hx`. Take `⟨h, hh, -, rfl⟩` from `hpt g₀ x hg₀.1 hg₀.2`. Establish `hk : g₀ * h ∈ S` using `S.mul_mem hg₀.1 hh`. Generalize the expression as in `g₀ * h = a at hk ⊢`.

Establish `: (fun g => A.indicator (fun q => f q.2) (g, p a)) = ((fun g => a⁻¹ * g) ⁻¹' T).indicator fun _ => f (p a)`. Use function extensionality and compare the values at `g`. Establish `: (g, p a) ∈ A ↔ g ∈ (fun g => a⁻¹ * g) ⁻¹' T`. Simplify using `only [A, T, Set.mem_ofPred_eq, Set.mem_preimage, mul_inv_rev, inv_inv, ← hp, S.mul_mem_cancel_left (S.inv_mem hk)]`. Simplify using `only [Set.indicator, this]`.

Rewrite using `[this]`. Use `(lintegral_indicator_const_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[measure_preimage_mul, mul_comm]`. Use `push Not at hx`. Simplify using `[Set.indicator_of_notMem (hx _)]`.

Use `set C : ℝ := 1 + ‖L‖ * (‖p 1‖ + δ)`. Establish `hC : 1 ≤ C` using `le_add_of_nonneg_right (by positivity)`. Use `set c : ℝ := (C ^ N)⁻¹ * (1 / 2) ^ k`. Establish `hc0 : 0 < c` using `by positivity`. Establish `hlow : ∀ g, (ENNReal.ofReal c * ν U) * (S : Set G).indicator (fun g => ENNReal.ofReal (((1 + ‖p g‖) ^ N)⁻¹ * |(L (p g)).det| ^ (k + 1))) g ≤ ∫⁻ x, A.indicator (fun q => f q.2) (g, x) ∂ν`.

Introduce `g`. Distinguish the cases in `hg : g ∈ S`. Use `swap`. Simplify using `[Set.indicator_of_notMem (s := (S : Set G)) hg]`. Rewrite using `[Set.indicator_of_mem (s := (S : Set G)) hg]`.

Establish `hd : (L (p g)).det * (L (p g⁻¹)).det = 1` using `by rw [← hdet, mul_inv_cancel, hdet1]`. Establish `hd0 : (L (p g⁻¹)).det ≠ 0` using `right_ne_zero_of_mul_eq_one hd`. Establish `hν : ν (L (p g⁻¹) ⁻¹' U) = ENNReal.ofReal |(L (p g)).det| * ν U`. Rewrite using `[Measure.addHaar_preimage_continuousLinearMap ν hd0, eq_inv_of_mul_eq_one_left hd]`. Establish `hB : MeasurableSet (L (p g⁻¹) ⁻¹' U)` using `(Metric.isOpen_ball.preimage (L _).continuous).measurableSet`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hν, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_right_comm, ← ENNReal.ofReal_mul hc0.le, pow_succ]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫⁻ x, (L (p g⁻¹) ⁻¹' U).indicator (fun _ => ENNReal.ofReal (c * (((1 + ‖p g‖) ^ N)⁻¹ * |(L (p g)).det| ^ k))) x ∂ν := (lintegral_indicator_const hB _).symm`.

Use `_ ≤ _ := by`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : L (p g⁻¹) x ∈ U`. Use `swap`. Rewrite using `[Set.indicator_of_notMem (s := L (p g⁻¹) ⁻¹' U) hx]`.

Conclude with `bot_le`. Rewrite using `[Set.indicator_of_mem (s := L (p g⁻¹) ⁻¹' U) hx, Set.indicator_of_mem (s := A) ⟨hg, hx⟩]`. Take `⟨h, -, hh, rfl⟩` from `hpt g x hg hx`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h1 : 1 + ‖p (g * h)‖ ≤ C * (1 + ‖p g‖)`.

Establish `h2 : ‖p (g * h)‖ ≤ ‖L‖ * ‖p g‖ * (‖p 1‖ + δ)`. Rewrite using `[hp]`. Conclude with `(L.le_opNorm₂ _ _).trans (by gcongr; exact hUn _ hh)`. Establish `: 0 ≤ ‖L‖ * (‖p 1‖ + δ)` using `by positivity`. Simplify using `only [C]`.

Use polynomial arithmetic with `[norm_nonneg (p g)]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [c, mul_pow, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ((1 + ‖p (g * h)‖) ^ N)⁻¹ * (|(L (p g)).det| * |(L (p h)).det|) ^ k := by gcongr`.

Conclude with `(hU _ hh).1.le`. Use `_ = _ := by rw [hdet, abs_mul]`. Establish `hνU : ν U ≠ 0` using `(Metric.measure_ball_pos ν _ hδ).ne'`. Establish `hνU' : ν U ≠ ⊤` using `measure_ball_lt_top.ne`. Establish `hk0 : ENNReal.ofReal c * ν U ≠ 0` using `mul_ne_zero (ENNReal.ofReal_pos.2 hc0).ne' hνU`.

Establish `hkt : ENNReal.ofReal c * ν U ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνU'`. Establish `hmain` using `(lintegral_mono (μ := μ) hlow).trans (hswap.le.trans (lintegral_mono hup))`. Rewrite `hmain` using `[lintegral_const_mul' _ _ hkt, lintegral_const_mul' _ _ hT.ne, lintegral_indicator hS]`. Use `hmain.trans_lt (ENNReal.mul_lt_top hT hf)` as an intermediate fact. Conclude with `(ENNReal.lt_top_of_mul_ne_top_right this.ne hk0)`.
-/
theorem lintegral_subgroup_lt_top {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (S : Subgroup G) (hS : MeasurableSet (S : Set G))
    (L : V →L[ℝ] V →L[ℝ] V) (p : G → V) (hpm : Measurable p)
    (hone : L (p 1) = ContinuousLinearMap.id ℝ V)
    (hL : ∀ g h, L (p (g * h)) = (L (p g)).comp (L (p h))) (hp : ∀ g h, p (g * h) = L (p g) (p h))
    (hsurj : ∀ x, (L x).det ≠ 0 → ∃ h ∈ S, p h = x)
    (hfin : ∀ R : ℝ, μ {g | g ∈ S ∧ ‖p g‖ ≤ R ∧ ‖p g⁻¹‖ ≤ R} < ⊤) (k : ℕ) :
    ∫⁻ g in S, ENNReal.ofReal (((1 + ‖p g‖) ^ (Module.finrank ℝ V * (k + 1) + 1))⁻¹ * |(L (p g)).det| ^ (k + 1)) ∂μ
      < ⊤ := by
  classical
  set N := Module.finrank ℝ V * (k + 1) + 1
  let ν : Measure V := Measure.addHaar
  have hc : Continuous fun x => |(L x).det| := (ContinuousLinearMap.continuous_det.comp L.continuous).abs
  have hdet : ∀ g h, (L (p (g * h))).det = (L (p g)).det * (L (p h)).det := fun g h => by
    rw [hL]; exact LinearMap.det_comp _ _
  have hdet1 : (L (p 1)).det = 1 := by rw [hone]; exact LinearMap.det_id
  obtain ⟨δ, hδ, hU⟩ : ∃ δ > 0, ∀ y ∈ Metric.ball (p 1) δ,
      1 / 2 < |(L y).det| ∧ ‖L y - ContinuousLinearMap.id ℝ V‖ < 1 / 2 := by
    have ho := (isOpen_lt (continuous_const (y := (1 / 2 : ℝ))) hc).inter
      (isOpen_lt (L.continuous.sub (continuous_const (y := ContinuousLinearMap.id ℝ V))).norm
        (continuous_const (y := (1 / 2 : ℝ))))
    obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 ho (p 1) ⟨by simp only [Set.mem_ofPred_eq, hdet1]; norm_num,
      by simp [hone]⟩
    exact ⟨δ, hδ, fun y hy => h hy⟩
  set U := Metric.ball (p 1) δ
  have hUn : ∀ y ∈ U, ‖y‖ ≤ ‖p 1‖ + δ := fun y hy => by
    have := norm_sub_norm_le y (p 1)
    have := mem_ball_iff_norm.1 hy
    linarith
  set T : Set G := {g | g ∈ S ∧ p g⁻¹ ∈ U}
  have hT : μ T < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun g hg => ?_) (hfin (2 * ‖p 1‖ + δ))
    refine ⟨hg.1, ?_, ?_⟩
    · have h1 : p g = p 1 - (L (p g⁻¹) - ContinuousLinearMap.id ℝ V) (p g) := by
        simp [← hp]
      have h2 := (L (p g⁻¹) - ContinuousLinearMap.id ℝ V).le_opNorm (p g)
      have h3 := mul_le_mul_of_nonneg_right (hU _ hg.2).2.le (norm_nonneg (p g))
      have h4 := norm_sub_le (p 1) ((L (p g⁻¹) - ContinuousLinearMap.id ℝ V) (p g))
      rw [← h1] at h4
      linarith
    · have := hUn _ hg.2
      linarith [norm_nonneg (p 1)]
  have hpt : ∀ g x, g ∈ S → L (p g⁻¹) x ∈ U → ∃ h ∈ S, p h ∈ U ∧ x = p (g * h) := by
    intro g x _ hx
    obtain ⟨h, hh, he⟩ := hsurj _ (abs_pos.1 (lt_trans (by norm_num) (hU _ hx).1))
    refine ⟨h, hh, he ▸ hx, ?_⟩
    rw [hp, he, ← ContinuousLinearMap.comp_apply, ← hL, mul_inv_cancel, hone, ContinuousLinearMap.id_apply]
  set f : V → ℝ≥0∞ := fun x => ENNReal.ofReal (((1 + ‖x‖) ^ N)⁻¹ * |(L x).det| ^ k)
  have hfm : Measurable f :=
    ((((measurable_const.add measurable_norm).pow_const N).inv).mul (hc.measurable.pow_const k)).ennreal_ofReal
  have hf : ∫⁻ x, f x ∂ν < ⊤ := lintegral_det_lt_top L ν k
  set A : Set (G × V) := {q | q.1 ∈ S ∧ L (p q.1⁻¹) q.2 ∈ U}
  have hA : MeasurableSet A := by
    have h2 : Continuous fun q : V × V => L q.1 q.2 := L.continuous₂
    exact (measurable_fst hS).inter ((h2.measurable.comp
      (((hpm.comp measurable_inv).comp measurable_fst).prodMk measurable_snd)) Metric.isOpen_ball.measurableSet)
  have hΦ : Measurable (A.indicator fun q => f q.2) := (hfm.comp measurable_snd).indicator hA
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := ν) (f := fun g x => A.indicator (fun q => f q.2) (g, x))
    hΦ.aemeasurable
  have hup : ∀ x, ∫⁻ g, A.indicator (fun q => f q.2) (g, x) ∂μ ≤ μ T * f x := by
    intro x
    by_cases hx : ∃ g, (g, x) ∈ A
    · obtain ⟨g₀, hg₀⟩ := hx
      obtain ⟨h, hh, -, rfl⟩ := hpt g₀ x hg₀.1 hg₀.2
      have hk : g₀ * h ∈ S := S.mul_mem hg₀.1 hh
      generalize g₀ * h = a at hk ⊢
      have : (fun g => A.indicator (fun q => f q.2) (g, p a)) =
          ((fun g => a⁻¹ * g) ⁻¹' T).indicator fun _ => f (p a) := by
        funext g
        have : (g, p a) ∈ A ↔ g ∈ (fun g => a⁻¹ * g) ⁻¹' T := by
          simp only [A, T, Set.mem_ofPred_eq, Set.mem_preimage, mul_inv_rev, inv_inv, ← hp,
            S.mul_mem_cancel_left (S.inv_mem hk)]
        simp only [Set.indicator, this]
      rw [this]
      refine (lintegral_indicator_const_le _ _).trans ?_
      rw [measure_preimage_mul, mul_comm]
    · push Not at hx
      simp [Set.indicator_of_notMem (hx _)]
  set C : ℝ := 1 + ‖L‖ * (‖p 1‖ + δ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  set c : ℝ := (C ^ N)⁻¹ * (1 / 2) ^ k
  have hc0 : 0 < c := by positivity
  have hlow : ∀ g, (ENNReal.ofReal c * ν U) * (S : Set G).indicator (fun g => ENNReal.ofReal
      (((1 + ‖p g‖) ^ N)⁻¹ * |(L (p g)).det| ^ (k + 1))) g ≤ ∫⁻ x, A.indicator (fun q => f q.2) (g, x) ∂ν := by
    intro g
    by_cases hg : g ∈ S
    swap
    · simp [Set.indicator_of_notMem (s := (S : Set G)) hg]
    rw [Set.indicator_of_mem (s := (S : Set G)) hg]
    have hd : (L (p g)).det * (L (p g⁻¹)).det = 1 := by rw [← hdet, mul_inv_cancel, hdet1]
    have hd0 : (L (p g⁻¹)).det ≠ 0 := right_ne_zero_of_mul_eq_one hd
    have hν : ν (L (p g⁻¹) ⁻¹' U) = ENNReal.ofReal |(L (p g)).det| * ν U := by
      rw [Measure.addHaar_preimage_continuousLinearMap ν hd0, eq_inv_of_mul_eq_one_left hd]
    have hB : MeasurableSet (L (p g⁻¹) ⁻¹' U) :=
      (Metric.isOpen_ball.preimage (L _).continuous).measurableSet
    calc _ = ENNReal.ofReal (c * (((1 + ‖p g‖) ^ N)⁻¹ * |(L (p g)).det| ^ k)) * ν (L (p g⁻¹) ⁻¹' U) := by
          rw [hν, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_right_comm,
            ← ENNReal.ofReal_mul hc0.le, pow_succ]
          congr 2
          ring
      _ = ∫⁻ x, (L (p g⁻¹) ⁻¹' U).indicator
          (fun _ => ENNReal.ofReal (c * (((1 + ‖p g‖) ^ N)⁻¹ * |(L (p g)).det| ^ k))) x ∂ν :=
          (lintegral_indicator_const hB _).symm
      _ ≤ _ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : L (p g⁻¹) x ∈ U
          swap
          · rw [Set.indicator_of_notMem (s := L (p g⁻¹) ⁻¹' U) hx]; exact bot_le
          rw [Set.indicator_of_mem (s := L (p g⁻¹) ⁻¹' U) hx, Set.indicator_of_mem (s := A) ⟨hg, hx⟩]
          obtain ⟨h, -, hh, rfl⟩ := hpt g x hg hx
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 1 + ‖p (g * h)‖ ≤ C * (1 + ‖p g‖) := by
            have h2 : ‖p (g * h)‖ ≤ ‖L‖ * ‖p g‖ * (‖p 1‖ + δ) := by
              rw [hp]
              exact (L.le_opNorm₂ _ _).trans (by gcongr; exact hUn _ hh)
            have : 0 ≤ ‖L‖ * (‖p 1‖ + δ) := by positivity
            simp only [C]
            nlinarith [norm_nonneg (p g)]
          calc c * (((1 + ‖p g‖) ^ N)⁻¹ * |(L (p g)).det| ^ k)
              = ((C * (1 + ‖p g‖)) ^ N)⁻¹ * (|(L (p g)).det| * (1 / 2)) ^ k := by
                simp only [c, mul_pow, mul_inv]; ring
            _ ≤ ((1 + ‖p (g * h)‖) ^ N)⁻¹ * (|(L (p g)).det| * |(L (p h)).det|) ^ k := by
                gcongr
                exact (hU _ hh).1.le
            _ = _ := by rw [hdet, abs_mul]
  have hνU : ν U ≠ 0 := (Metric.measure_ball_pos ν _ hδ).ne'
  have hνU' : ν U ≠ ⊤ := measure_ball_lt_top.ne
  have hk0 : ENNReal.ofReal c * ν U ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 hc0).ne' hνU
  have hkt : ENNReal.ofReal c * ν U ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνU'
  have hmain := (lintegral_mono (μ := μ) hlow).trans (hswap.le.trans (lintegral_mono hup))
  rw [lintegral_const_mul' _ _ hkt, lintegral_const_mul' _ _ hT.ne, lintegral_indicator hS] at hmain
  have := hmain.trans_lt (ENNReal.mul_lt_top hT hf)
  exact (ENNReal.lt_top_of_mul_ne_top_right this.ne hk0)

end Abstract

/- English proof (translation)
The claim follows from `Algebra.lmul_isUnit_iff.1 ((LinearMap.isUnit_iff_isUnit_det _).2 h)`.
-/
theorem isUnit_of_norm {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    {x : A} (h : IsUnit (Algebra.norm R x)) : IsUnit x :=
  Algebra.lmul_isUnit_iff.1 ((LinearMap.isUnit_iff_isUnit_det _).2 h)

section Ideles

open scoped Classical
open mixedEmbedding GlobalTheory.IdeleDecay GlobalTheory.IdeleTate

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bas : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) :=
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

def evR : AF F →+* mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))

def mat (x : AE F E) : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) (mixedSpace F) :=
  (Algebra.leftMulMatrix (bas F E) x).map (evR F)

def vec (x : AE F E) : Fin (Module.finrank F E) → mixedSpace F := fun i => evR F ((bas F E).repr x i)

variable {F E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_eq (x : AE F E) (i : Fin (Module.finrank F E)) : coord F E x i = (bas F E).repr x i := rfl

/- English proof (translation)
Use `conv_rhs => rw [← (bas F E).sum_repr x]`. Use `Matrix.ext fun j k => ?_` and prove the remaining obligations. Simplify using `only [mat, vec, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]`.
-/
theorem sum_vec_mat (x : AE F E) : ∑ i, vec F E x i • mat F E (bas F E i) = mat F E x := by
  conv_rhs => rw [← (bas F E).sum_repr x]
  refine Matrix.ext fun j k => ?_
  simp only [mat, vec, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]

/- English proof (translation)
Simplify using `only [mat, map_mul, Matrix.map_mul]`.
-/
theorem mat_mul (x y : AE F E) : mat F E (x * y) = mat F E x * mat F E y := by
  simp only [mat, map_mul, Matrix.map_mul]

/- English proof (translation)
Simplify using `only [mat, map_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem mat_one : mat F E 1 = 1 := by
  simp only [mat, map_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[vec, ← Algebra.leftMulMatrix_mulVec_repr, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem vec_mul (x y : AE F E) : vec F E (x * y) = mat F E x *ᵥ vec F E y := by
  funext i
  rw [vec, ← Algebra.leftMulMatrix_mulVec_repr, RingHom.map_mulVec]
  rfl

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_matrix_det (bas F E), RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_mat (x : AE F E) : (mat F E x).det = evR F (Algebra.norm (AF F) x) := by
  rw [Algebra.norm_eq_matrix_det (bas F E), RingHom.map_det]
  rfl

/- English proof (translation)
Rewrite using `[det_mat, PIW.MinkowskiIdealBound.MinkR.abs_algNorm]`. Use `Eq.trans ?_ (PIW.MinkowskiIdealBound.MinkR.norm_ringEquiv (Algebra.norm (AF F) l.1).1).symm` and prove the remaining obligations. Rewrite using `[InfiniteAdeleRing.norm_def, absInf, NNReal.coe_prod]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.Doubling.absEw_unitInf]`.

Both sides reduce to the same expression.
-/
theorem absInf_eq (l : (AE F E)ˣ) : (absInf F E l : ℝ) = |Algebra.norm ℝ (mat F E l.1).det| := by
  rw [det_mat, PIW.MinkowskiIdealBound.MinkR.abs_algNorm]
  refine Eq.trans ?_ (PIW.MinkowskiIdealBound.MinkR.norm_ringEquiv (Algebra.norm (AF F) l.1).1).symm
  rw [InfiniteAdeleRing.norm_def, absInf, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.Doubling.absEw_unitInf]
  rfl

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg (size_nonneg x)).2 fun i => Finset.single_le_sum (f := fun i => ‖evI F (coord F E x i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)`.
-/
theorem norm_vec_le (x : AE F E) : ‖vec F E x‖ ≤ size F E x :=
  (pi_norm_le_iff_of_nonneg (size_nonneg x)).2 fun i =>
    Finset.single_le_sum (f := fun i => ‖evI F (coord F E x i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/- English proof (translation)
The claim follows from `continuous_pi fun i => (continuous_evI F).comp ((continuous_apply i).comp (continuous_coord F E))`.
-/
theorem continuous_vec : Continuous (vec F E) :=
  continuous_pi fun i => (continuous_evI F).comp ((continuous_apply i).comp (continuous_coord F E))

variable (F E) in

/- English proof (translation)
Set `f : (Fin (Module.finrank F E) → mixedSpace F) →ₗ[ℝ] (Fin (Module.finrank F E) → mixedSpace F) →ₗ[ℝ] (Fin (Module.finrank F E) → mixedSpace F)` to `LinearMap.mk₂ ℝ (fun v w => (∑ i, v i • mat F E (bas F E i)) *ᵥ w) (fun a b c => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Matrix.add_mulVec]) (fun c a b => by simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, Matrix.smul_mulVec]) (fun a b c => Matrix.m …`. Use `⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ f), fun v w => rfl, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]`. Both sides reduce to the same expression.
-/
theorem exists_bilin : ∃ L : (Fin (Module.finrank F E) → mixedSpace F) →L[ℝ]
    (Fin (Module.finrank F E) → mixedSpace F) →L[ℝ] (Fin (Module.finrank F E) → mixedSpace F),
    (∀ v w, L v w = (∑ i, v i • mat F E (bas F E i)) *ᵥ w) ∧
      ∀ v, (L v).det = Algebra.norm ℝ (∑ i, v i • mat F E (bas F E i)).det := by
  let f : (Fin (Module.finrank F E) → mixedSpace F) →ₗ[ℝ] (Fin (Module.finrank F E) → mixedSpace F) →ₗ[ℝ]
      (Fin (Module.finrank F E) → mixedSpace F) :=
    LinearMap.mk₂ ℝ (fun v w => (∑ i, v i • mat F E (bas F E i)) *ᵥ w)
      (fun a b c => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Matrix.add_mulVec])
      (fun c a b => by simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, Matrix.smul_mulVec])
      (fun a b c => Matrix.mulVec_add _ _ _) (fun c a b => Matrix.mulVec_smul _ _ _)
  refine ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ f), fun v w => rfl,
    fun v => ?_⟩
  rw [← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]
  rfl

/- English proof (translation)
Establish `key : ∀ y : AE F E, sndA F ((bas F E).repr (y * z) k) = ∑ i, sndA F ((bas F E).repr y i) * sndA F ((bas F E).repr (bas F E i * z) k)` using `fun y => by conv_lhs => rw [← (bas F E).sum_repr y, Finset.sum_mul]`. Simplify using `only [smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]`. Establish `h1` using `key 1`. Rewrite `h1` using `[one_mul]`. Conclude with `(key x).trans ((Finset.sum_congr rfl fun i _ => congrArg (· * _) (hx i)).trans h1.symm)`.
-/
theorem repr_mul_snd {x : AE F E} (hx : ∀ i, ((bas F E).repr x i).2 = ((bas F E).repr 1 i).2) (z : AE F E)
    (k : Fin (Module.finrank F E)) : ((bas F E).repr (x * z) k).2 = ((bas F E).repr z k).2 := by
  have key : ∀ y : AE F E, sndA F ((bas F E).repr (y * z) k) =
      ∑ i, sndA F ((bas F E).repr y i) * sndA F ((bas F E).repr (bas F E i * z) k) := fun y => by
    conv_lhs => rw [← (bas F E).sum_repr y, Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, map_mul]
  have h1 := key 1
  rw [one_mul] at h1
  exact (key x).trans ((Finset.sum_congr rfl fun i _ => congrArg (· * _) (hx i)).trans h1.symm)

/- English proof (translation)
Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `x : AE F E` to `(bas F E).equivFun.symm fun i => (e.symm (v i), ((bas F E).repr 1 i).2)`. Establish `hx : ∀ i, (bas F E).repr x i = (e.symm (v i), ((bas F E).repr 1 i).2)` using `fun i => congrFun ((bas F E).equivFun.apply_symm_apply _) i`. Establish `hvec : vec F E x = v` using `funext fun i => by`. Rewrite using `[vec, hx]`.

Conclude with `e.apply_symm_apply _`. Establish `hsnd` using `repr_mul_snd (x := x) fun i => by rw [hx]`. Use `haveI := Module.Free.of_basis (bas F E)`. Use `haveI := Module.Finite.of_basis (bas F E)`. Establish `hu : IsUnit x`.

Use `isUnit_of_norm (R := AF F) (Prod.isUnit_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite `hv` using `[← hvec, sum_vec_mat, det_mat]`. Conclude with `(MulEquiv.isUnit_map e).1 (isUnit_of_norm (R := ℝ) hv.isUnit)`. Establish `: sndA F (Algebra.norm (AF F) x) = 1`. Rewrite using `[Algebra.norm_eq_matrix_det (bas F E), AlgHom.map_det, ← Matrix.det_one (n := Fin (Module.finrank F E))]`.

Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Use `(hsnd _ i).trans ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]`.

Distinguish the cases in `h : i = j`. Rewrite using `[if_pos h, if_pos h.symm]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Both sides reduce to the same expression.

Conclude with `IsUnit.of_mul_eq_one 1 ((mul_one _).trans this)`. Use `⟨hu.unit, fun z => forall_congr' fun i => forall_congr' fun w => ?_, hvec⟩` and prove the remaining obligations. Establish `: evFin F w (coord F E (x * z) i) = evFin F w (coord F E z i)` using `congrArg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (hsnd z i)`. Rewrite using `[IsUnit.unit_spec, this]`.
-/
theorem exists_mem_stab (v : Fin (Module.finrank F E) → mixedSpace F)
    (hv : Algebra.norm ℝ (∑ i, v i • mat F E (bas F E i)).det ≠ 0) :
    ∃ h ∈ stab F E, vec F E h.1 = v := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let x : AE F E := (bas F E).equivFun.symm fun i => (e.symm (v i), ((bas F E).repr 1 i).2)
  have hx : ∀ i, (bas F E).repr x i = (e.symm (v i), ((bas F E).repr 1 i).2) := fun i =>
    congrFun ((bas F E).equivFun.apply_symm_apply _) i
  have hvec : vec F E x = v := funext fun i => by
    rw [vec, hx]; exact e.apply_symm_apply _
  have hsnd := repr_mul_snd (x := x) fun i => by rw [hx]
  haveI := Module.Free.of_basis (bas F E)
  haveI := Module.Finite.of_basis (bas F E)
  have hu : IsUnit x := by
    refine isUnit_of_norm (R := AF F) (Prod.isUnit_iff.2 ⟨?_, ?_⟩)
    · rw [← hvec, sum_vec_mat, det_mat] at hv
      exact (MulEquiv.isUnit_map e).1 (isUnit_of_norm (R := ℝ) hv.isUnit)
    · have : sndA F (Algebra.norm (AF F) x) = 1 := by
        rw [Algebra.norm_eq_matrix_det (bas F E), AlgHom.map_det, ← Matrix.det_one (n := Fin (Module.finrank F E))]
        congr 1
        refine Matrix.ext fun i j => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
        refine (hsnd _ i).trans ?_
        rw [Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
        by_cases h : i = j
        · rw [if_pos h, if_pos h.symm]; rfl
        · rw [if_neg h, if_neg (Ne.symm h)]; rfl
      exact IsUnit.of_mul_eq_one 1 ((mul_one _).trans this)
  refine ⟨hu.unit, fun z => forall_congr' fun i => forall_congr' fun w => ?_, hvec⟩
  have : evFin F w (coord F E (x * z) i) = evFin F w (coord F E z i) :=
    congrArg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (hsnd z i)
  rw [IsUnit.unit_spec, this]

variable (F) in

/- English proof (translation)
Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Establish `hc : Continuous e.symm`. Use `continuous_pi fun v => ?_` and prove the remaining obligations. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]`.

Conclude with `((continuous_apply _).comp continuous_fst).congr fun y => (congrFun (congrArg Prod.fst (e.apply_symm_apply y)) ⟨v, hv⟩).symm`. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]`. Conclude with `((continuous_apply _).comp continuous_snd).congr fun y => (congrFun (congrArg Prod.snd (e.apply_symm_apply y)) ⟨v, hv⟩).symm`. Use `(isCompact_closedBall (0 : mixedSpace F) R).image hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨e a, mem_closedBall_zero_iff.2 ha, e.symm_apply_apply a⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `‖e (e.symm y)‖ ≤ R`.

Rewrite using `[e.apply_symm_apply]`. Conclude with `mem_closedBall_zero_iff.1 hy`.
-/
theorem isCompact_inf (R : ℝ) : IsCompact {a : Ainf F | ‖InfiniteAdeleRing.ringEquiv_mixedSpace F a‖ ≤ R} := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hc : Continuous e.symm := by
    refine continuous_pi fun v => ?_
    rcases v.isReal_or_isComplex with hv | hv
    · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
      exact ((continuous_apply _).comp continuous_fst).congr fun y =>
        (congrFun (congrArg Prod.fst (e.apply_symm_apply y)) ⟨v, hv⟩).symm
    · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
      exact ((continuous_apply _).comp continuous_snd).congr fun y =>
        (congrFun (congrArg Prod.snd (e.apply_symm_apply y)) ⟨v, hv⟩).symm
  convert (isCompact_closedBall (0 : mixedSpace F) R).image hc using 1
  ext a
  constructor
  · intro ha
    exact ⟨e a, mem_closedBall_zero_iff.2 ha, e.symm_apply_apply a⟩
  · rintro ⟨y, hy, rfl⟩
    change ‖e (e.symm y)‖ ≤ R
    rw [e.apply_symm_apply]
    exact mem_closedBall_zero_iff.1 hy

variable (F E) in

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Set `O : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)` to `{a | ∀ v, a v ∈ v.adicCompletionIntegers F}`. Establish `hO : IsCompact O` using `GlobalTheory.AdeleCocompact.isCompact_integral F`.

Set `ψ : (Fin (Module.finrank F E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F` to `fun z => ∑ j, ((bas F E).repr 1 j).2 * z j`. Establish `hψ : Continuous ψ` using `continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)`. Establish `hK` using `(isCompact_inf F R).prod ((isCompact_univ_pi fun _ => hO).image hψ)`. Set `χ : (Fin (Module.finrank F E) → AF F) → AE F E` to `fun z => ∑ i, z i • bas F E i`. Establish `hχ : Continuous χ` using `continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const`.

Use `⟨χ '' Set.pi Set.univ fun _ => _, (isCompact_univ_pi fun _ => hK).image hχ, fun g hg hR => ⟨fun i => (bas F E).repr g.1 i, fun i _ => ⟨(norm_le_pi_norm (vec F E g.1) i).trans hR, fun j => ((bas F E).repr (g.1 * bas F E j) i).2, fun j _ => ?_, ?_⟩, (bas F E).sum_repr _⟩⟩` and prove the remaining obligations. Use `(hg (bas F E j)).1 (fun k v => ?_) i` and prove the remaining obligations. Rewrite using `[coord_eq, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Rewrite using `[map_one]`.

Conclude with `one_mem _`. Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Establish `: sndA F ((bas F E).repr (g.1 * 1) i) = ∑ j, sndA F ((bas F E).repr 1 j) * sndA F ((bas F E).repr (g.1 * bas F E j) i)` using `by conv_lhs => rw [← (bas F E).sum_repr 1, Finset.mul_sum]`. Simplify using `only [mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]`.

Rewrite `this` using `[mul_one]`. Conclude with `this.symm`.
-/
theorem exists_compact (R : ℝ) : ∃ K : Set (AE F E), IsCompact K ∧
    ∀ g ∈ stab F E, ‖vec F E g.1‖ ≤ R → g.1 ∈ K := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  let O : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  have hO : IsCompact O := GlobalTheory.AdeleCocompact.isCompact_integral F
  let ψ : (Fin (Module.finrank F E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
    fun z => ∑ j, ((bas F E).repr 1 j).2 * z j
  have hψ : Continuous ψ := continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hK := (isCompact_inf F R).prod ((isCompact_univ_pi fun _ => hO).image hψ)
  let χ : (Fin (Module.finrank F E) → AF F) → AE F E := fun z => ∑ i, z i • bas F E i
  have hχ : Continuous χ := continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  refine ⟨χ '' Set.pi Set.univ fun _ => _, (isCompact_univ_pi fun _ => hK).image hχ, fun g hg hR =>
    ⟨fun i => (bas F E).repr g.1 i, fun i _ => ⟨(norm_le_pi_norm (vec F E g.1) i).trans hR,
      fun j => ((bas F E).repr (g.1 * bas F E j) i).2, fun j _ => ?_, ?_⟩, (bas F E).sum_repr _⟩⟩
  · refine (hg (bas F E j)).1 (fun k v => ?_) i
    rw [coord_eq, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  · have : sndA F ((bas F E).repr (g.1 * 1) i) =
        ∑ j, sndA F ((bas F E).repr 1 j) * sndA F ((bas F E).repr (g.1 * bas F E j) i) := by
      conv_lhs => rw [← (bas F E).sum_repr 1, Finset.mul_sum]
      simp only [mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, map_mul]
    rw [mul_one] at this
    exact this.symm

end Ideles

end GlobalTheory.IdeleArchBound

open GlobalTheory.IdeleArchBound in

/- English proof (translation)
Introduce `F E _ _ _ _ _ s hs`. Take `⟨k, rfl⟩ : ∃ k, s = k + 1` from `⟨s - 1, by omega⟩`. Use `⟨Module.finrank ℝ (Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) * (k + 1) + 1, fun μ hμ => ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology`.

Use `haveI : T2Space (AE F E) := e.isEmbedding.t2Space`. Use `haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`. Use `haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology`.

Use `haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)`. Use `haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩`. Use `letI : MeasurableSpace (Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) := borel _`. Use `haveI : BorelSpace (Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) := ⟨rfl⟩`.

Take `⟨L, hL, hdet⟩` from `exists_bilin F E`. Establish `hL' : ∀ x w, L (vec F E x) w = mat F E x *ᵥ w` using `fun x w => by rw [hL, sum_vec_mat]`. Establish `key` using `lintegral_subgroup_lt_top μ (GlobalTheory.IdeleTate.stab F E) (GlobalTheory.IdeleTate.isOpen_stab F E).measurableSet L (fun l => vec F E l.1) (continuous_vec.comp Units.continuous_val).measurable (ContinuousLinearMap.ext fun w => by`. Rewrite using `[hL', Units.val_one, mat_one, Matrix.one_mulVec, ContinuousLinearMap.id_apply])`. Use the proof step `(fun g h => ContinuousLinearMap.ext fun w => by`.

Rewrite using `[ContinuousLinearMap.comp_apply, hL', hL', hL', Units.val_mul, mat_mul, Matrix.mulVec_mulVec])`. Use the proof step `(fun g h => by rw [hL', Units.val_mul, vec_mul])`. Use the proof step `(fun x hx => exists_mem_stab x (by rwa [hdet] at hx))`. Use the proof step `(fun R => by`. Take `⟨K, hK, hK'⟩` from `exists_compact F E R`.

Establish `hc` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hK.prod (hK.image MulOpposite.continuous_op))`. Use `lt_of_le_of_lt (measure_mono fun g hg => ?_) hc.measure_lt_top` and prove the remaining obligations. Conclude with `⟨hK' g hg.1 hg.2.1, _, hK' g⁻¹ (inv_mem hg.1) hg.2.2, rfl⟩) k`. Use `lt_of_le_of_lt (lintegral_mono fun l => ENNReal.ofReal_le_ofReal ?_) key` and prove the remaining obligations. Rewrite using `[hdet, sum_vec_mat, ← absInf_eq]`.

Use `gcongr`. Conclude with `norm_vec_le _`.
-/
theorem GlobalTheory.IdeleArchBound.lintegral_stab_lt_top :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s : ℕ), 1 ≤ s →
    ∃ N : ℕ, ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure →
      ∫⁻ l in (GlobalTheory.IdeleTate.stab F E : Set (AE F E)ˣ),
        ENNReal.ofReal (((1 + GlobalTheory.IdeleDecay.size F E l.1) ^ N)⁻¹ * (GlobalTheory.IdeleTate.absInf F E l : ℝ) ^ s) ∂μ < ⊤ := by
  intro F E _ _ _ _ _ s hs
  classical
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  refine ⟨Module.finrank ℝ (Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) * (k + 1) + 1, fun μ hμ => ?_⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ :=
    @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  letI : MeasurableSpace (Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  obtain ⟨L, hL, hdet⟩ := exists_bilin F E
  have hL' : ∀ x w, L (vec F E x) w = mat F E x *ᵥ w := fun x w => by rw [hL, sum_vec_mat]
  have key := lintegral_subgroup_lt_top μ (GlobalTheory.IdeleTate.stab F E) (GlobalTheory.IdeleTate.isOpen_stab F E).measurableSet L
    (fun l => vec F E l.1) (continuous_vec.comp Units.continuous_val).measurable
    (ContinuousLinearMap.ext fun w => by
      rw [hL', Units.val_one, mat_one, Matrix.one_mulVec, ContinuousLinearMap.id_apply])
    (fun g h => ContinuousLinearMap.ext fun w => by
      rw [ContinuousLinearMap.comp_apply, hL', hL', hL', Units.val_mul, mat_mul, Matrix.mulVec_mulVec])
    (fun g h => by rw [hL', Units.val_mul, vec_mul])
    (fun x hx => exists_mem_stab x (by rwa [hdet] at hx))
    (fun R => by
      obtain ⟨K, hK, hK'⟩ := exists_compact F E R
      have hc := Units.isClosedEmbedding_embedProduct.isCompact_preimage
        (hK.prod (hK.image MulOpposite.continuous_op))
      refine lt_of_le_of_lt (measure_mono fun g hg => ?_) hc.measure_lt_top
      exact ⟨hK' g hg.1 hg.2.1, _, hK' g⁻¹ (inv_mem hg.1) hg.2.2, rfl⟩) k
  refine lt_of_le_of_lt (lintegral_mono fun l => ENNReal.ofReal_le_ofReal ?_) key
  rw [hdet, sum_vec_mat, ← absInf_eq]
  gcongr
  exact norm_vec_le _

end
