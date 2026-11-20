import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtCompact
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtNonInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace ExtensionProof

variable {D : ℕ} {U : Type} [TopologicalSpace U]

/- English proof (translation)
Establish `h : piece A k = (A.chart k).target ∩ ⋂ l : Fin A.n, ⋂ (_ : l < k), ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart l).source)ᶜ`. Use extensionality with `y`. Simplify using `only [piece, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff, mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, h⟩`.

Conclude with `⟨hy, fun l hl hl' => h l hl hl'.2⟩`. Introduce and unpack `⟨hy, h⟩`. Conclude with `⟨hy, fun l hl hl' => h l hl ⟨hy, hl'⟩⟩`. Rewrite using `[h]`. Conclude with `(A.chart k).open_target.measurableSet.inter (MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => ((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target (A.chart l).open_source).measurableSet.compl)`.
-/
theorem measurableSet_piece (A : FinHolAtlas D U) (k : Fin A.n) : MeasurableSet (piece A k) := by
  have h : piece A k = (A.chart k).target ∩ ⋂ l : Fin A.n, ⋂ (_ : l < k),
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart l).source)ᶜ := by
    ext y
    simp only [piece, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff, mem_preimage]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun l hl hl' => h l hl hl'.2⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun l hl hl' => h l hl ⟨hy, hl'⟩⟩
  rw [h]
  exact (A.chart k).open_target.measurableSet.inter (MeasurableSet.iInter fun l =>
    MeasurableSet.iInter fun _ => ((A.chart k).continuousOn_symm.isOpen_inter_preimage
      (A.chart k).open_target (A.chart l).open_source).measurableSet.compl)

/- English proof (translation)
The claim follows from `(hf.mono fun _ hy => hy.1).aemeasurable (measurableSet_piece A k)`.
-/
theorem aem_of_continuousOn {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (A : FinHolAtlas D U) (k : Fin A.n) {f : (Fin D → ℂ) → β}
    (hf : ContinuousOn f (A.chart k).target) : AEMeasurable f (volume.restrict (piece A k)) :=
  (hf.mono fun _ hy => hy.1).aemeasurable (measurableSet_piece A k)

/- English proof (translation)
The claim follows from `(h k).continuousOn.mono fun _ hy => ⟨hy, (A.chart k).map_target hy⟩`.
-/
theorem continuousOn_of_holoOn (A : FinHolAtlas D U) (k : Fin A.n) {f : U → ℂ}
    (h : A.HoloOn (A.chart k).source f) :
    ContinuousOn (f ∘ (A.chart k).symm) (A.chart k).target :=
  (h k).continuousOn.mono fun _ hy => ⟨hy, (A.chart k).map_target hy⟩

/- English proof (translation)
The claim follows from `Finset.sum_le_sum fun k _ => lintegral_mono fun _ => h k _`.
-/
theorem chartIntegral_mono (A : FinHolAtlas D U) {f g : Fin A.n → U → ℝ≥0∞}
    (h : ∀ k x, f k x ≤ g k x) : chartIntegral A f ≤ chartIntegral A g :=
  Finset.sum_le_sum fun k _ => lintegral_mono fun _ => h k _

/- English proof (translation)
Unfold `chartIntegral`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => lintegral_const_mul' c _ hc`.
-/
theorem chartIntegral_const_mul (A : FinHolAtlas D U) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (f : Fin A.n → U → ℝ≥0∞) :
    chartIntegral A (fun k x => c * f k x) = c * chartIntegral A f := by
  unfold chartIntegral
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => lintegral_const_mul' c _ hc

/- English proof (translation)
Unfold `chartIntegral`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => lintegral_add_left' (hf k) _`.
-/
theorem chartIntegral_add (A : FinHolAtlas D U) (f g : Fin A.n → U → ℝ≥0∞)
    (hf : ∀ k, AEMeasurable (fun y => f k ((A.chart k).symm y)) (volume.restrict (piece A k))) :
    chartIntegral A (fun k x => f k x + g k x) = chartIntegral A f + chartIntegral A g := by
  unfold chartIntegral
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => lintegral_add_left' (hf k) _

/- English proof (translation)
Unfold `chartIntegral at hB ⊢`. Establish `h1 : ∀ k, ∫⁻ y in piece A k, g k ((A.chart k).symm y) ≤ liminf (fun m => ∫⁻ y in piece A k, f m k ((A.chart k).symm y)) atTop` using `fun k => (lintegral_mono fun y => hg k _).trans (lintegral_liminf_le' fun m => hf m k)`. Use `(Finset.sum_le_sum fun k _ => h1 k).trans ?_` and prove the remaining obligations. Simplify using `only [liminf_eq_iSup_iInf_of_nat]`. Rewrite using `[ENNReal.finsetSum_iSup_of_monotone]`.

Conclude with `iSup_le fun N => (Finset.sum_le_sum fun k _ => iInf₂_le N le_rfl).trans (hB N)`. Introduce `k a b hab`. Conclude with `le_iInf₂ fun i hi => iInf₂_le i (hab.trans hi)`.
-/
theorem chartIntegral_le_of_liminf (A : FinHolAtlas D U) (f : ℕ → Fin A.n → U → ℝ≥0∞)
    (g : Fin A.n → U → ℝ≥0∞) (B : ℝ≥0∞)
    (hf : ∀ m k, AEMeasurable (fun y => f m k ((A.chart k).symm y)) (volume.restrict (piece A k)))
    (hB : ∀ m, chartIntegral A (f m) ≤ B) (hg : ∀ k x, g k x ≤ liminf (fun m => f m k x) atTop) :
    chartIntegral A g ≤ B := by
  unfold chartIntegral at hB ⊢
  have h1 : ∀ k, ∫⁻ y in piece A k, g k ((A.chart k).symm y) ≤
      liminf (fun m => ∫⁻ y in piece A k, f m k ((A.chart k).symm y)) atTop := fun k =>
    (lintegral_mono fun y => hg k _).trans (lintegral_liminf_le' fun m => hf m k)
  refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.finsetSum_iSup_of_monotone]
  · exact iSup_le fun N => (Finset.sum_le_sum fun k _ => iInf₂_le N le_rfl).trans (hB N)
  · intro k a b hab
    exact le_iInf₂ fun i hi => iInf₂_le i (hab.trans hi)

variable {X : EmbDatum D}

/- English proof (translation)
The claim follows from `continuousOn_of_holoOn X.A k ((X.e_mem i).1 k)`.
-/
theorem contOn_e (X : EmbDatum D) (i : Fin X.N) (k : Fin X.A.n) :
    ContinuousOn (X.e i k ∘ (X.A.chart k).symm) (X.A.chart k).target :=
  continuousOn_of_holoOn X.A k ((X.e_mem i).1 k)

/- English proof (translation)
The claim follows from `continuousOn_of_holoOn X.A k ((X.e₂_mem i).1 k)`.
-/
theorem contOn_e₂ (X : EmbDatum D) (i : Fin X.N₂) (k : Fin X.A.n) :
    ContinuousOn (X.e₂ i k ∘ (X.A.chart k).symm) (X.A.chart k).target :=
  continuousOn_of_holoOn X.A k ((X.e₂_mem i).1 k)

/- English proof (translation)
Simplify using `[ZeroDatum.s, lin, Finset.sum_apply]`.
-/
theorem s_apply (Z : ZeroDatum X) (i : Fin D) (k : Fin X.A.n) (y : X.U) :
    Z.s i k y = ∑ l, Z.c i l * X.e l k y := by
  simp [ZeroDatum.s, lin, Finset.sum_apply]

/- English proof (translation)
Unfold `fsWeight`. Conclude with `(Finset.aemeasurable_fun_sum Finset.univ fun i _ => (aem_of_continuousOn A k (he i)).norm.pow_const 2).log`.
-/
theorem aem_fsWeight {N : ℕ} (A : FinHolAtlas D U) (k : Fin A.n) (e : Fin N → Fin A.n → U → ℂ)
    (he : ∀ i, ContinuousOn (e i k ∘ (A.chart k).symm) (A.chart k).target) :
    AEMeasurable (fun y => fsWeight e k ((A.chart k).symm y)) (volume.restrict (piece A k)) := by
  unfold fsWeight
  exact (Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
    (aem_of_continuousOn A k (he i)).norm.pow_const 2).log

/- English proof (translation)
Simplify using `only [EmbDatum.wt]`. Conclude with `(aem_fsWeight X.A k X.e₂ fun i => contOn_e₂ X i k).add ((aem_fsWeight X.A k X.e fun i => contOn_e X i k).const_mul _)`.
-/
theorem aem_wt (X : EmbDatum D) (m : ℕ) (k : Fin X.A.n) :
    AEMeasurable (fun y => X.wt m k ((X.A.chart k).symm y)) (volume.restrict (piece X.A k)) := by
  simp only [EmbDatum.wt]
  exact (aem_fsWeight X.A k X.e₂ fun i => contOn_e₂ X i k).add
    ((aem_fsWeight X.A k X.e fun i => contOn_e X i k).const_mul _)

/- English proof (translation)
Unfold `extEv`. Repeatedly rewrite using `[s_apply]`. Use `((Finset.aemeasurable_fun_sum Finset.univ fun i _ => ?_).mul (aem_fsWeight X.A k X.e fun i => contOn_e X i k).neg.exp).div_const _` and prove the remaining obligations. Conclude with `(Finset.aemeasurable_fun_sum Finset.univ fun l _ => (aem_of_continuousOn X.A k (contOn_e X l k)).const_mul _).norm.pow_const 2`.
-/
theorem aem_extEv (Z : ZeroDatum X) (k : Fin X.A.n) :
    AEMeasurable (fun y => extEv Z k ((X.A.chart k).symm y)) (volume.restrict (piece X.A k)) := by
  unfold extEv
  simp_rw [s_apply]
  refine ((Finset.aemeasurable_fun_sum Finset.univ fun i _ => ?_).mul
    (aem_fsWeight X.A k X.e fun i => contOn_e X i k).neg.exp).div_const _
  exact (Finset.aemeasurable_fun_sum Finset.univ fun l _ =>
    (aem_of_continuousOn X.A k (contOn_e X l k)).const_mul _).norm.pow_const 2

/- English proof (translation)
Unfold `extFactor extDen extX curvEta`. Use `measurability`.
-/
theorem measurable_extFactor (D : ℕ) (ε δ : ℝ) : Measurable (extFactor D ε δ) := by
  unfold extFactor extDen extX curvEta
  measurability

/- English proof (translation)
The claim follows from `(((((aem_of_continuousOn X.A k hu).norm.pow_const 2).const_mul _).mul (aem_wt X m k).neg.exp).mul (hw.comp_aemeasurable (aem_extEv Z k))).ennreal_ofReal`.
-/
theorem aem_dens (Z : ZeroDatum X) (m : ℕ) (k : Fin X.A.n) (u : X.U → ℂ)
    (hu : ContinuousOn (u ∘ (X.A.chart k).symm) (X.A.chart k).target) (w : ℝ → ℝ)
    (hw : Measurable w) :
    AEMeasurable (fun y => ENNReal.ofReal (2 ^ D * ‖u ((X.A.chart k).symm y)‖ ^ 2 *
      Real.exp (-X.wt m k ((X.A.chart k).symm y)) * w (extEv Z k ((X.A.chart k).symm y))))
      (volume.restrict (piece X.A k)) :=
  (((((aem_of_continuousOn X.A k hu).norm.pow_const 2).const_mul _).mul
    (aem_wt X m k).neg.exp).mul (hw.comp_aemeasurable (aem_extEv Z k))).ennreal_ofReal

/- English proof (translation)
The claim follows from `((((aem_of_continuousOn X.A k hu).norm.pow_const 2).const_mul _).mul (aem_wt X m k).neg.exp).ennreal_ofReal`.
-/
theorem aem_dens' (X : EmbDatum D) (m : ℕ) (k : Fin X.A.n) (u : X.U → ℂ)
    (hu : ContinuousOn (u ∘ (X.A.chart k).symm) (X.A.chart k).target) :
    AEMeasurable (fun y => ENNReal.ofReal (2 ^ D * ‖u ((X.A.chart k).symm y)‖ ^ 2 *
      Real.exp (-X.wt m k ((X.A.chart k).symm y)))) (volume.restrict (piece X.A k)) :=
  ((((aem_of_continuousOn X.A k hu).norm.pow_const 2).const_mul _).mul
    (aem_wt X m k).neg.exp).ennreal_ofReal

/- English proof (translation)
Unfold `rSq`. Check the signs of the components of the expression.
-/
theorem rSq_nonneg {N : ℕ} (c : Fin D → Fin N → ℂ) : 0 ≤ rSq c := by
  unfold rSq; positivity

/- English proof (translation)
Unfold `extEv`. Conclude with `div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => by positivity) (Real.exp_pos _).le) (rSq_nonneg Z.c)`.
-/
theorem extEv_nonneg (Z : ZeroDatum X) (k : Fin X.A.n) (y : X.U) : 0 ≤ extEv Z k y := by
  unfold extEv
  exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => by positivity) (Real.exp_pos _).le)
    (rSq_nonneg Z.c)

/- English proof (translation)
Use `set E := ∑ l, ‖X.e l k y‖ ^ 2 with hE`. Establish `hs : ∀ i, ‖Z.s i k y‖ ^ 2 ≤ (∑ l, ‖Z.c i l‖ ^ 2) * E`. Introduce `i`. Rewrite using `[s_apply]`. Establish `h1 : ‖∑ l, Z.c i l * X.e l k y‖ ≤ ∑ l, ‖Z.c i l‖ * ‖X.e l k y‖` using `(norm_sum_le _ _).trans (le_of_eq (by simp))`.

Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖Z.c i l‖) (fun l => ‖X.e l k y‖)`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ∑ i, ‖Z.s i k y‖ ^ 2 ≤ rSq Z.c * E`. Unfold `rSq`. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_le_sum fun i _ => hs i`. Establish `hE0 : 0 ≤ E` using `by positivity`. Establish `hR0` using `rSq_nonneg Z.c`. Unfold `extEv fsWeight`. Rewrite using `[← hE]`.

Break down `hE0.lt_or_eq with hEpos | hE0'` into its components or cases. Rewrite using `[Real.exp_neg, Real.exp_log hEpos]`. Break down `hR0.lt_or_eq with hRpos | hR0'` into its components or cases. Rewrite using `[div_le_one hRpos]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hR0']`. Simplify using the standard rewrite rules. Establish `: ∑ i, ‖Z.s i k y‖ ^ 2 = 0` using `le_antisymm (by simpa [← hE0'] using hsum) (by positivity)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem extEv_le_one (Z : ZeroDatum X) (k : Fin X.A.n) (y : X.U) : extEv Z k y ≤ 1 := by
  set E := ∑ l, ‖X.e l k y‖ ^ 2 with hE
  have hs : ∀ i, ‖Z.s i k y‖ ^ 2 ≤ (∑ l, ‖Z.c i l‖ ^ 2) * E := by
    intro i
    rw [s_apply]
    have h1 : ‖∑ l, Z.c i l * X.e l k y‖ ≤ ∑ l, ‖Z.c i l‖ * ‖X.e l k y‖ :=
      (norm_sum_le _ _).trans (le_of_eq (by simp))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖Z.c i l‖)
      (fun l => ‖X.e l k y‖)
    calc ‖∑ l, Z.c i l * X.e l k y‖ ^ 2 ≤ (∑ l, ‖Z.c i l‖ * ‖X.e l k y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hsum : ∑ i, ‖Z.s i k y‖ ^ 2 ≤ rSq Z.c * E := by
    unfold rSq
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hs i
  have hE0 : 0 ≤ E := by positivity
  have hR0 := rSq_nonneg Z.c
  unfold extEv fsWeight
  rw [← hE]
  rcases hE0.lt_or_eq with hEpos | hE0'
  · rw [Real.exp_neg, Real.exp_log hEpos]
    rcases hR0.lt_or_eq with hRpos | hR0'
    · rw [div_le_one hRpos]
      calc (∑ i, ‖Z.s i k y‖ ^ 2) * E⁻¹ ≤ (rSq Z.c * E) * E⁻¹ :=
            mul_le_mul_of_nonneg_right hsum (inv_nonneg.2 hE0)
        _ = rSq Z.c := by field_simp
    · rw [← hR0']; simp
  · have : ∑ i, ‖Z.s i k y‖ ^ 2 = 0 :=
      le_antisymm (by simpa [← hE0'] using hsum) (by positivity)
    rw [this]; simp

/- English proof (translation)
Establish `ha : 0 < t + ε ^ 2` using `by positivity`. Establish `hb : 0 < 1 + ε ^ 2` using `by positivity`. Establish `hx : 1 ≤ extX ε t`. Unfold `extX`. Establish `: Real.log (t + ε ^ 2) ≤ Real.log (1 + ε ^ 2)` using `Real.log_le_log ha (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDr : (1 : ℝ) ≤ D` using `by exact_mod_cast hD`. Establish `key` using `exp_div_ge_of_one_le hx hDr`. Establish `hden : 0 < extDen ε t`. Unfold `extDen`.

Use `le_curvEta hx` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg (extX ε t + 1)]`. Establish `hexpx : Real.exp (extX ε t) = Real.exp 1 * (1 + ε ^ 2) / (t + ε ^ 2)`. Unfold `extX`. Rewrite using `[Real.exp_sub, Real.exp_add, Real.exp_log hb, Real.exp_log ha]`.

Establish `hexpDx : Real.exp (D * extX ε t) = Real.exp 1 ^ D * (1 + ε ^ 2) ^ D / (t + ε ^ 2) ^ D`. Rewrite using `[Real.exp_nat_mul, hexpx, div_pow, mul_pow]`. Establish `hexpD : Real.exp ((D : ℝ) - 1) * Real.exp 1 = Real.exp 1 ^ D`. Rewrite using `[← Real.exp_add, ← Real.exp_nat_mul]`. Put the polynomial expressions in normal form.

Establish `hmono : ((t + ε ^ 2) ^ D)⁻¹ ≤ ((t + δ ^ 2) ^ D)⁻¹` using `inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le (by linarith) D)`. Establish `hdef : extDen ε t = (extX ε t + 1) ^ 2 + curvEta (extX ε t)` using `rfl`. Rewrite `key` using `[← hdef, hexpDx]`. Use `set P := (t + ε ^ 2) ^ D with hP`. Use `set Q := (1 + ε ^ 2) ^ D with hQ`.

Use `set E1 := Real.exp 1 with hE1`. Establish `hPpos : 0 < P` using `by positivity`. Establish `hQpos : 0 < Q` using `by positivity`. Establish `hE1pos : 0 < E1` using `Real.exp_pos 1`. Establish `hE1D : 0 < E1 ^ D` using `by positivity`.

Establish `k1 : Real.exp ((D : ℝ) - 1) * (P * extDen ε t) ≤ 2 * (E1 ^ D * Q)`. Use `key` as an intermediate fact. Rewrite `this` using `[div_div, le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `k3 : P * extDen ε t ≤ 2 * E1 * Q`.

Rewrite `k1` using `[← hexpD]`. Establish `h' : Real.exp ((D : ℝ) - 1) * (P * extDen ε t) ≤ Real.exp ((D : ℝ) - 1) * (2 * E1 * Q)` using `by linarith [k1]`. Conclude with `le_of_mul_le_mul_left h' (Real.exp_pos _)`. Establish `k4 : 1 ≤ 2 * E1 * Q * (P⁻¹ / extDen ε t)`. Rewrite using `[show 2 * E1 * Q * (P⁻¹ / extDen ε t) = (2 * E1 * Q) / (P * extDen ε t) by field_simp]`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `extFactor`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_factor {ε δ t : ℝ} (hε : 0 < ε) (hδε : δ ^ 2 ≤ ε ^ 2) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hpos : 0 < t + δ ^ 2) (hD : 1 ≤ D) :
    1 ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ D * extFactor D ε δ t := by
  have ha : 0 < t + ε ^ 2 := by positivity
  have hb : 0 < 1 + ε ^ 2 := by positivity
  have hx : 1 ≤ extX ε t := by
    unfold extX
    have : Real.log (t + ε ^ 2) ≤ Real.log (1 + ε ^ 2) := Real.log_le_log ha (by linarith)
    linarith
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have key := exp_div_ge_of_one_le hx hDr
  have hden : 0 < extDen ε t := by
    unfold extDen
    have := le_curvEta hx
    nlinarith [sq_nonneg (extX ε t + 1)]
  have hexpx : Real.exp (extX ε t) = Real.exp 1 * (1 + ε ^ 2) / (t + ε ^ 2) := by
    unfold extX
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hb, Real.exp_log ha]
  have hexpDx : Real.exp (D * extX ε t) = Real.exp 1 ^ D * (1 + ε ^ 2) ^ D / (t + ε ^ 2) ^ D := by
    rw [Real.exp_nat_mul, hexpx, div_pow, mul_pow]
  have hexpD : Real.exp ((D : ℝ) - 1) * Real.exp 1 = Real.exp 1 ^ D := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    ring_nf
  have hmono : ((t + ε ^ 2) ^ D)⁻¹ ≤ ((t + δ ^ 2) ^ D)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le (by linarith) D)
  have hdef : extDen ε t = (extX ε t + 1) ^ 2 + curvEta (extX ε t) := rfl
  rw [← hdef, hexpDx] at key
  set P := (t + ε ^ 2) ^ D with hP
  set Q := (1 + ε ^ 2) ^ D with hQ
  set E1 := Real.exp 1 with hE1
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hE1pos : 0 < E1 := Real.exp_pos 1
  have hE1D : 0 < E1 ^ D := by positivity

  have k1 : Real.exp ((D : ℝ) - 1) * (P * extDen ε t) ≤ 2 * (E1 ^ D * Q) := by
    have := key
    rw [div_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  have k3 : P * extDen ε t ≤ 2 * E1 * Q := by
    rw [← hexpD] at k1
    have h' : Real.exp ((D : ℝ) - 1) * (P * extDen ε t) ≤
        Real.exp ((D : ℝ) - 1) * (2 * E1 * Q) := by linarith [k1]
    exact le_of_mul_le_mul_left h' (Real.exp_pos _)
  have k4 : 1 ≤ 2 * E1 * Q * (P⁻¹ / extDen ε t) := by
    rw [show 2 * E1 * Q * (P⁻¹ / extDen ε t) = (2 * E1 * Q) / (P * extDen ε t) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  unfold extFactor
  calc (1 : ℝ) ≤ 2 * E1 * Q * (P⁻¹ / extDen ε t) := k4
    _ ≤ 2 * E1 * Q * (((t + δ ^ 2) ^ D)⁻¹ / extDen ε t) := by gcongr

end ExtensionProof

open ExtensionProof in

/- English proof (translation)
Introduce `D X Z j hD hj g`. Establish `hcD : 0 < cD D` using `by unfold cD; positivity`. Establish `hr : 0 ≤ rSq Z.c` using `rSq_nonneg Z.c`. Establish `hsN : 0 ≤ sNormSq X.A Z.S (X.wt j) g`. Unfold `sNormSq`.

Conclude with `finsum_nonneg fun x => finsum_nonneg fun _ => by positivity`. Take `⟨K, hKdef⟩ : ∃ K : ℝ, K = cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g` from `⟨_, rfl⟩`. Establish `hK0 : 0 ≤ K` using `by rw [hKdef]; positivity`. Establish `hgoal : 140 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g = 140 * K`. Rewrite using `[hKdef]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hgoal]`. Break down `hK0.lt_or_eq with hKpos | hKzero` into its components or cases. Use `swap`. Establish `hg0 : ∀ x ∈ Z.S, g x = 0`.

Introduce `x hx`. Establish `hprod : rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g = 0`. Establish `: cD D * (rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g) = 0`. Rewrite using `[← mul_assoc, ← hKdef, hKzero]`. Conclude with `(mul_eq_zero.1 this).resolve_left hcD.ne'`.

Break down `mul_eq_zero.1 hprod with hr0 | hs0` into its components or cases. It suffices to derive a contradiction. Establish `hr0' : rSq Z.c = 0` using `(pow_eq_zero_iff (by omega)).1 hr0`. Establish `hc0 : ∀ i l, Z.c i l = 0`. Introduce `i l`.

Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun l _ => by positivity)).1 hr0' i (Finset.mem_univ _)`. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg (fun l _ => by positivity)).1 h1 l (Finset.mem_univ _)`. Simplify using `using h2`. Apply `Z.nondeg x hx` to reduce the goal to its premises. Establish `hs0 : (fun i => lin X.e (Z.c i)) = fun _ => 0`.

Use function extensionality and compare the values at `i`. Simplify using `[lin, hc0]`. Rewrite using `[hs0]`. Simplify using `[sJac, sJacMap, LinearMap.det_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `hfin : Z.S.Finite` using `Z.finite`. Unfold `sNormSq at hs0`. Rewrite `hs0` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Establish `h` using `(Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by positivity)).1 hs0 x (hfin.mem_toFinset.2 hx)`. Establish `h2 : ‖g x‖ ^ 2 = 0` using `(mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne'`.

Simplify using `using h2`. Use `⟨0, Submodule.zero_mem _, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[res, hg0 x hx]`. Simplify using `[topNormSq, chartIntegral]`. Take `⟨θ, hθ⟩ : ∃ θ : ℝ, θ = K / 100` from `⟨_, rfl⟩`.

Establish `hθpos : 0 < θ` using `by rw [hθ]; positivity`. Take `⟨ε₀, hε₀, hεΔ⟩` from `hΔ D X Z j hD hj g θ hθpos`. Establish `hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ ∧ (1 + ε ^ 2) ^ D < 1 + 1 / 200`. Establish `h1 : Tendsto (fun ε : ℝ => (1 + ε ^ 2) ^ D) (𝓝 0) (𝓝 1)`. Establish `hc : Continuous (fun ε : ℝ => (1 + ε ^ 2) ^ D)` using `by fun_prop`.

Simplify using `using hc.tendsto 0`. Conclude with `(Filter.Eventually.and (Iio_mem_nhds hε₀) (h1.eventually (gt_mem_nhds (by norm_num)))).filter_mono nhdsWithin_le_nhds`. Take `⟨ε, ⟨hεlt, hεb⟩, hεpos⟩` from `(hev.and self_mem_nhdsWithin).exists`. Establish `hεpos' : 0 < ε` using `hεpos`. Establish `hεlt' : ε < ε₀` using `hεlt`.

Take `⟨F₀, hF₀c, hF₀tr, -, hF₀res, hF₀n, hF₀δ⟩` from `hεΔ ε hεpos' hεlt'.le`. Take `⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun n : ℕ => ε / ((n : ℝ) + 1)` from `⟨_, rfl⟩`. Establish `hδpos : ∀ n, 0 < δ n` using `fun n => by rw [hδdef]; positivity`. Establish `hδle : ∀ n, δ n ≤ ε` using `fun n => by`. Rewrite using `[hδdef]`.

Conclude with `div_le_self hεpos'.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])`. Establish `hδlim : Tendsto δ atTop (𝓝 0)`. Use `tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Rewrite using `[hδdef]`.

Use `this.congr fun n => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `choose Fn hFnmem hFnbd using fun n => hF₀δ (δ n) (hδpos n) (hδle n)`. Take `⟨B, hB⟩ : ∃ B : ℝ, B = 36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ` from `⟨_, rfl⟩`. Rewrite `hFnbd` using `[← hB]`.

Establish `hBeq : B = (36 * Real.log 2 + 1 / 100) * K` using `by rw [hB, hθ, hKdef]; ring`. Establish `hl0 : 0 < Real.log 2` using `Real.log_pos one_lt_two`. Establish `hBnn : 0 ≤ B` using `by rw [hBeq]; positivity`. Take `⟨c₁, hc₁⟩ : ∃ c : ℝ, c = 2 * Real.exp 1 * (1 + ε ^ 2) ^ D` from `⟨_, rfl⟩`. Establish `hc₁nn : 0 ≤ c₁` using `by rw [hc₁]; positivity`.

Establish `hcontFn : ∀ n k, ContinuousOn (Fn n k ∘ (X.A.chart k).symm) (X.A.chart k).target` using `fun n k => continuousOn_of_holoOn X.A k ((hFnmem n).1 k)`. Establish `hFnb : ∀ n, topNormSq X.A (X.wt (D + j)) (F₀ - Fn n) ≤ ENNReal.ofReal (c₁ * B)`. Introduce `n`. Combine the equalities or inequalities in the displayed calculation. Unfold `topNormSq`.

Use `chartIntegral_mono _ fun k y => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul hc₁nn]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `h1` using `one_le_factor (D := D) hεpos' (pow_le_pow_left₀ (hδpos n).le (hδle n) 2) (extEv_nonneg Z k y) (extEv_le_one Z k y) (add_pos_of_nonneg_of_pos (extEv_nonneg Z k y) (pow_pos (hδpos n) 2)) hD`. Rewrite `h1` using `[← hc₁]`.

Establish `h0 : 0 ≤ 2 ^ D * ‖F₀ k y - Fn n k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y)`. Check the signs of the components of the expression. Simplify using `only [Pi.sub_apply]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 h0]`. Use `_ = ENNReal.ofReal c₁ * chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖F₀ k y - Fn n k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) * extFactor D ε (δ n) (extEv Z k y))) := chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top _`.

Use `_ ≤ ENNReal.ofReal c₁ * ENNReal.ofReal B := by gcongr; exact hFnbd n`. Use `_ = ENNReal.ofReal (c₁ * B) := (ENNReal.ofReal_mul hc₁nn).symm`. Establish `hF₀m : ∀ (c : ℝ≥0∞) (k : Fin X.A.n), AEMeasurable (fun y => c * ENNReal.ofReal (2 ^ D * ‖F₀ k ((X.A.chart k).symm y)‖ ^ 2 * Real.exp (-X.wt (D + j) k ((X.A.chart k).symm y)))) (volume.restrict (piece X.A k))` using `fun c k => (aem_dens' X (D + j) k (F₀ k) (hF₀c k)).const_mul c`. Establish `hFnN : ∀ n, topNormSq X.A (X.wt (D + j)) (Fn n) ≤ ENNReal.ofReal (2 * θ + 2 * (c₁ * B))`. Introduce `n`.

Combine the equalities or inequalities in the displayed calculation. Unfold `topNormSq`. Use `chartIntegral_mono _ fun k y => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `htri : ‖Fn n k y‖ ≤ ‖F₀ k y‖ + ‖(F₀ - Fn n) k y‖`. Simplify using `using norm_sub_le (F₀ k y) (F₀ k y - Fn n k y)`. Establish `hp : 0 ≤ 2 ^ D * Real.exp (-X.wt (D + j) k y)` using `by positivity`. Establish `hsq : ‖Fn n k y‖ ^ 2 ≤ 2 * ‖F₀ k y‖ ^ 2 + 2 * ‖(F₀ - Fn n) k y‖ ^ 2`. Use polynomial arithmetic with `[norm_nonneg (Fn n k y), norm_nonneg (F₀ k y), norm_nonneg ((F₀ - Fn n) k y), sq_nonneg (‖F₀ k y‖ - ‖(F₀ - Fn n) k y‖)]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hsq hp]`. Use `_ = ENNReal.ofReal 2 * topNormSq X.A (X.wt (D + j)) F₀ + ENNReal.ofReal 2 * topNormSq X.A (X.wt (D + j)) (F₀ - Fn n) := by`. Rewrite using `[chartIntegral_add _ _ _ (hF₀m _), chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top, chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top]`. Both sides reduce to the same expression. Use `_ ≤ ENNReal.ofReal 2 * ENNReal.ofReal θ + ENNReal.ofReal 2 * ENNReal.ofReal (c₁ * B) := by`.

Conclude with `add_le_add (mul_le_mul_right hF₀n _) (mul_le_mul_right (hFnb n) _)`. Use `_ = ENNReal.ofReal (2 * θ + 2 * (c₁ * B)) := by`. Rewrite using `[← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Take `⟨φ', hφ', G, hGmem, hGlim⟩` from `hC D X (D + j) Fn (2 * θ + 2 * (c₁ * B)) hFnmem hFnN`. Establish `hsub : ∀ k y, Tendsto (fun m => F₀ k y - Fn (φ' m) k y) atTop (𝓝 (F₀ k y - G k y))` using `fun k y => tendsto_const_nhds.sub (hGlim k y)`.

Establish `hcontG : ∀ k, ContinuousOn (G k ∘ (X.A.chart k).symm) (X.A.chart k).target` using `fun k => continuousOn_of_holoOn X.A k (hGmem.1 k)`. Establish `hGb : topNormSq X.A (X.wt (D + j)) (F₀ - G) ≤ ENNReal.ofReal (c₁ * B)`. Unfold `topNormSq`. Use `chartIntegral_le_of_liminf X.A (fun m k y => ENNReal.ofReal (2 ^ D * ‖(F₀ - Fn (φ' m)) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y))) _ _ (fun m k => ?_) (fun m => hFnb (φ' m)) (fun k y => ?_)` and prove the remaining obligations. Conclude with `aem_dens' X (D + j) k (fun x => F₀ k x - Fn (φ' m) k x) ((hF₀c k).sub (hcontFn _ k))`.

Establish `ht : Tendsto (fun m => ENNReal.ofReal (2 ^ D * ‖(F₀ - Fn (φ' m)) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y))) atTop (𝓝 (ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y))))` using `ENNReal.tendsto_ofReal ((((hsub k y).norm.pow 2).const_mul _).mul_const _)`. Conclude with `ht.liminf_eq.ge`. Establish `hGw : chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) * extFactor D ε 0 (extEv Z k y))) ≤ ENNReal.ofReal B`. Use `chartIntegral_le_of_liminf X.A (fun m k y => ENNReal.ofReal (2 ^ D * ‖F₀ k y - Fn (φ' m) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) * extFactor D ε (δ (φ' m)) (extEv Z k y))) _ _ (fun m k => ?_) (fun m => hFnbd (φ' m)) (fun k y => ?_)` and prove the remaining obligations. Conclude with `aem_dens Z (D + j) k (fun x => F₀ k x - Fn (φ' m) k x) ((hF₀c k).sub (hcontFn _ k)) _ (measurable_extFactor D ε _)`.

Break down `(extEv_nonneg Z k y).lt_or_eq with htpos | ht0` into its components or cases. Establish `hfac : Tendsto (fun m => extFactor D ε (δ (φ' m)) (extEv Z k y)) atTop (𝓝 (extFactor D ε 0 (extEv Z k y)))`. Unfold `extFactor`. Use `Tendsto.div_const (Tendsto.inv₀ ?_ ?_) _` and prove the remaining obligations. Conclude with `(tendsto_const_nhds.add ((hδlim.comp hφ'.tendsto_atTop).pow 2)).pow D`.

Use `pow_ne_zero _ ?_` and prove the remaining obligations. Rewrite using `[zero_pow two_ne_zero, add_zero]`. Conclude with `htpos.ne'`. Establish `ht : Tendsto (fun m => ENNReal.ofReal (2 ^ D * ‖F₀ k y - Fn (φ' m) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) * extFactor D ε (δ (φ' m)) (extEv Z k y))) atTop (𝓝 (ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) * extFactor D ε 0 (extEv Z k y))))` using `ENNReal.tendsto_ofReal (((((hsub k y).norm.pow 2).const_mul _).mul_const _).mul hfac)`. Conclude with `ht.liminf_eq.ge`.

Establish `h0 : extFactor D ε 0 (extEv Z k y) = 0`. Rewrite using `[← ht0]`. Simplify using `[extFactor, zero_pow (show D ≠ 0 by omega)]`. Rewrite using `[h0, mul_zero, ENNReal.ofReal_zero]`. Conclude with `bot_le`.

Establish `hres0` using `hN D X Z (D + j) ε hD hεpos' (F₀ - G) (fun k => (hF₀c k).sub (hcontG k)) (fun k l x hx => by`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[hF₀tr k l x hx, hGmem.2.1 k l x hx]`. Use the proof step `ring)`. Use the proof step `(lt_of_le_of_lt hGw ENNReal.ofReal_lt_top)`.

Use `⟨G, hGmem, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hres0 x hx`. Establish `h' : G (chartIdx X.A x) x = F₀ (chartIdx X.A x) x`. Simplify using `only [Pi.sub_apply, sub_eq_zero] at h`. Conclude with `h.symm`.

Rewrite using `[← hF₀res x hx]`. Simplify using `only [res, h']`. Establish `hnum : 201 * θ + 201 / 200 * (c₁ * B) ≤ 140 * K`. Establish `he` using `Real.exp_one_lt_d9`. Establish `hl` using `Real.log_two_lt_d9`.

Establish `he0` using `Real.exp_pos 1`. Establish `hq : (1 + ε ^ 2) ^ D ≤ 201 / 200` using `by linarith [hεb]`. Establish `hc₁le : c₁ ≤ 2 * Real.exp 1 * (201 / 200)`. Rewrite using `[hc₁]`. Use `gcongr`.

Establish `hel : Real.exp 1 * Real.log 2 < 1.8842`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_right he hl0]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right hc₁le hBnn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = K * (2.01 + 1.010025 * (72 * (Real.exp 1 * Real.log 2) + 0.02 * Real.exp 1)) := by`. Rewrite using `[hBeq, hθ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ K * 140 := by`. Apply `mul_le_mul_of_nonneg_left _ hK0` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = 140 * K := by ring`. Combine the equalities or inequalities in the displayed calculation. Unfold `topNormSq`. Use `chartIntegral_mono _ fun k y => ?_` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `htri : ‖G k y‖ ≤ ‖F₀ k y‖ + ‖(F₀ - G) k y‖`. Simplify using `using norm_sub_le (F₀ k y) (F₀ k y - G k y)`. Establish `hp : 0 ≤ 2 ^ D * Real.exp (-X.wt (D + j) k y)` using `by positivity`.

Establish `hsq : ‖G k y‖ ^ 2 ≤ 201 * ‖F₀ k y‖ ^ 2 + 201 / 200 * ‖(F₀ - G) k y‖ ^ 2`. Use polynomial arithmetic with `[norm_nonneg (G k y), norm_nonneg (F₀ k y), norm_nonneg ((F₀ - G) k y), sq_nonneg (200 * ‖F₀ k y‖ - ‖(F₀ - G) k y‖)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hsq hp]`. Use `_ = ENNReal.ofReal 201 * topNormSq X.A (X.wt (D + j)) F₀ + ENNReal.ofReal (201 / 200) * topNormSq X.A (X.wt (D + j)) (F₀ - G) := by`. Rewrite using `[chartIntegral_add _ _ _ (hF₀m _), chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top, chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top]`.

Both sides reduce to the same expression. Use `_ ≤ ENNReal.ofReal 201 * ENNReal.ofReal θ + ENNReal.ofReal (201 / 200) * ENNReal.ofReal (c₁ * B) := by`. Conclude with `add_le_add (mul_le_mul_right hF₀n _) (mul_le_mul_right hGb _)`. Use `_ = ENNReal.ofReal (201 * θ + 201 / 200 * (c₁ * B)) := by`. Rewrite using `[← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]`.

Use `_ ≤ ENNReal.ofReal (140 * K) := ENNReal.ofReal_le_ofReal hnum`.
-/
theorem ExtensionLemma.proof (hΔ : ExtDelta.Statement) (hC : TopSecCompact.Statement)
    (hN : ExtNonInt.Statement) : ExtensionLemma.Statement := by
  intro D X Z j hD hj g
  have hcD : 0 < cD D := by unfold cD; positivity
  have hr : 0 ≤ rSq Z.c := rSq_nonneg Z.c
  have hsN : 0 ≤ sNormSq X.A Z.S (X.wt j) g := by
    unfold sNormSq
    exact finsum_nonneg fun x => finsum_nonneg fun _ => by positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hgoal : 140 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g = 140 * K := by
    rw [hKdef]; ring
  rw [hgoal]
  rcases hK0.lt_or_eq with hKpos | hKzero
  swap
  ·
    have hg0 : ∀ x ∈ Z.S, g x = 0 := by
      intro x hx
      have hprod : rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g = 0 := by
        have : cD D * (rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g) = 0 := by
          rw [← mul_assoc, ← hKdef, hKzero]
        exact (mul_eq_zero.1 this).resolve_left hcD.ne'
      rcases mul_eq_zero.1 hprod with hr0 | hs0
      · exfalso
        have hr0' : rSq Z.c = 0 := (pow_eq_zero_iff (by omega)).1 hr0
        have hc0 : ∀ i l, Z.c i l = 0 := by
          intro i l
          have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun l _ =>
            by positivity)).1 hr0' i (Finset.mem_univ _)
          have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => by positivity)).1 h1 l
            (Finset.mem_univ _)
          simpa using h2
        apply Z.nondeg x hx
        have hs0 : (fun i => lin X.e (Z.c i)) = fun _ => 0 := by
          funext i; simp [lin, hc0]
        rw [hs0]
        simp [sJac, sJacMap, LinearMap.det_zero]
        omega
      · have hfin : Z.S.Finite := Z.finite
        unfold sNormSq at hs0
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hs0
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by positivity)).1 hs0 x
          (hfin.mem_toFinset.2 hx)
        have h2 : ‖g x‖ ^ 2 = 0 := (mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne'
        simpa using h2
    refine ⟨0, Submodule.zero_mem _, fun x hx => ?_, ?_⟩
    · simp [res, hg0 x hx]
    · simp [topNormSq, chartIntegral]

  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = K / 100 := ⟨_, rfl⟩
  have hθpos : 0 < θ := by rw [hθ]; positivity
  obtain ⟨ε₀, hε₀, hεΔ⟩ := hΔ D X Z j hD hj g θ hθpos
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ ∧ (1 + ε ^ 2) ^ D < 1 + 1 / 200 := by
    have h1 : Tendsto (fun ε : ℝ => (1 + ε ^ 2) ^ D) (𝓝 0) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => (1 + ε ^ 2) ^ D) := by fun_prop
      simpa using hc.tendsto 0
    exact (Filter.Eventually.and (Iio_mem_nhds hε₀)
      (h1.eventually (gt_mem_nhds (by norm_num)))).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hεlt, hεb⟩, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos' : 0 < ε := hεpos
  have hεlt' : ε < ε₀ := hεlt
  obtain ⟨F₀, hF₀c, hF₀tr, -, hF₀res, hF₀n, hF₀δ⟩ := hεΔ ε hεpos' hεlt'.le
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun n : ℕ => ε / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hδpos : ∀ n, 0 < δ n := fun n => by rw [hδdef]; positivity
  have hδle : ∀ n, δ n ≤ ε := fun n => by
    rw [hδdef]
    exact div_le_self hεpos'.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
    rw [mul_zero] at this
    rw [hδdef]
    refine this.congr fun n => ?_
    ring
  choose Fn hFnmem hFnbd using fun n => hF₀δ (δ n) (hδpos n) (hδle n)
  obtain ⟨B, hB⟩ : ∃ B : ℝ,
      B = 36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ := ⟨_, rfl⟩
  rw [← hB] at hFnbd
  have hBeq : B = (36 * Real.log 2 + 1 / 100) * K := by rw [hB, hθ, hKdef]; ring
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hBnn : 0 ≤ B := by rw [hBeq]; positivity
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = 2 * Real.exp 1 * (1 + ε ^ 2) ^ D := ⟨_, rfl⟩
  have hc₁nn : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hcontFn : ∀ n k, ContinuousOn (Fn n k ∘ (X.A.chart k).symm) (X.A.chart k).target :=
    fun n k => continuousOn_of_holoOn X.A k ((hFnmem n).1 k)

  have hFnb : ∀ n, topNormSq X.A (X.wt (D + j)) (F₀ - Fn n) ≤ ENNReal.ofReal (c₁ * B) := by
    intro n
    calc topNormSq X.A (X.wt (D + j)) (F₀ - Fn n)
        ≤ chartIntegral X.A (fun k y => ENNReal.ofReal c₁ * ENNReal.ofReal (2 ^ D *
            ‖F₀ k y - Fn n k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) *
            extFactor D ε (δ n) (extEv Z k y))) := by
          unfold topNormSq
          refine chartIntegral_mono _ fun k y => ?_
          rw [← ENNReal.ofReal_mul hc₁nn]
          apply ENNReal.ofReal_le_ofReal
          have h1 := one_le_factor (D := D) hεpos' (pow_le_pow_left₀ (hδpos n).le (hδle n) 2)
            (extEv_nonneg Z k y) (extEv_le_one Z k y)
            (add_pos_of_nonneg_of_pos (extEv_nonneg Z k y) (pow_pos (hδpos n) 2)) hD
          rw [← hc₁] at h1
          have h0 : 0 ≤ 2 ^ D * ‖F₀ k y - Fn n k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) := by
            positivity
          simp only [Pi.sub_apply]
          nlinarith [mul_le_mul_of_nonneg_left h1 h0]
      _ = ENNReal.ofReal c₁ * chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D *
            ‖F₀ k y - Fn n k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) *
            extFactor D ε (δ n) (extEv Z k y))) :=
          chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal c₁ * ENNReal.ofReal B := by gcongr; exact hFnbd n
      _ = ENNReal.ofReal (c₁ * B) := (ENNReal.ofReal_mul hc₁nn).symm

  have hF₀m : ∀ (c : ℝ≥0∞) (k : Fin X.A.n), AEMeasurable (fun y => c * ENNReal.ofReal (2 ^ D *
      ‖F₀ k ((X.A.chart k).symm y)‖ ^ 2 * Real.exp (-X.wt (D + j) k ((X.A.chart k).symm y))))
      (volume.restrict (piece X.A k)) :=
    fun c k => (aem_dens' X (D + j) k (F₀ k) (hF₀c k)).const_mul c
  have hFnN : ∀ n, topNormSq X.A (X.wt (D + j)) (Fn n) ≤
      ENNReal.ofReal (2 * θ + 2 * (c₁ * B)) := by
    intro n
    calc topNormSq X.A (X.wt (D + j)) (Fn n)
        ≤ chartIntegral X.A (fun k y => ENNReal.ofReal 2 * ENNReal.ofReal (2 ^ D * ‖F₀ k y‖ ^ 2 *
            Real.exp (-X.wt (D + j) k y)) + ENNReal.ofReal 2 * ENNReal.ofReal (2 ^ D *
            ‖(F₀ - Fn n) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y))) := by
          unfold topNormSq
          refine chartIntegral_mono _ fun k y => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have htri : ‖Fn n k y‖ ≤ ‖F₀ k y‖ + ‖(F₀ - Fn n) k y‖ := by
            simpa using norm_sub_le (F₀ k y) (F₀ k y - Fn n k y)
          have hp : 0 ≤ 2 ^ D * Real.exp (-X.wt (D + j) k y) := by positivity
          have hsq : ‖Fn n k y‖ ^ 2 ≤ 2 * ‖F₀ k y‖ ^ 2 + 2 * ‖(F₀ - Fn n) k y‖ ^ 2 := by
            nlinarith [norm_nonneg (Fn n k y), norm_nonneg (F₀ k y),
              norm_nonneg ((F₀ - Fn n) k y), sq_nonneg (‖F₀ k y‖ - ‖(F₀ - Fn n) k y‖)]
          nlinarith [mul_le_mul_of_nonneg_right hsq hp]
      _ = ENNReal.ofReal 2 * topNormSq X.A (X.wt (D + j)) F₀ +
            ENNReal.ofReal 2 * topNormSq X.A (X.wt (D + j)) (F₀ - Fn n) := by
          rw [chartIntegral_add _ _ _ (hF₀m _), chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top,
            chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top]
          rfl
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal θ + ENNReal.ofReal 2 * ENNReal.ofReal (c₁ * B) := by
          exact add_le_add (mul_le_mul_right hF₀n _) (mul_le_mul_right (hFnb n) _)
      _ = ENNReal.ofReal (2 * θ + 2 * (c₁ * B)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]

  obtain ⟨φ', hφ', G, hGmem, hGlim⟩ := hC D X (D + j) Fn (2 * θ + 2 * (c₁ * B)) hFnmem hFnN
  have hsub : ∀ k y, Tendsto (fun m => F₀ k y - Fn (φ' m) k y) atTop (𝓝 (F₀ k y - G k y)) :=
    fun k y => tendsto_const_nhds.sub (hGlim k y)
  have hcontG : ∀ k, ContinuousOn (G k ∘ (X.A.chart k).symm) (X.A.chart k).target :=
    fun k => continuousOn_of_holoOn X.A k (hGmem.1 k)

  have hGb : topNormSq X.A (X.wt (D + j)) (F₀ - G) ≤ ENNReal.ofReal (c₁ * B) := by
    unfold topNormSq
    refine chartIntegral_le_of_liminf X.A (fun m k y => ENNReal.ofReal (2 ^ D *
      ‖(F₀ - Fn (φ' m)) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y))) _ _ (fun m k => ?_)
      (fun m => hFnb (φ' m)) (fun k y => ?_)
    · exact aem_dens' X (D + j) k (fun x => F₀ k x - Fn (φ' m) k x) ((hF₀c k).sub (hcontFn _ k))
    · have ht : Tendsto (fun m => ENNReal.ofReal (2 ^ D * ‖(F₀ - Fn (φ' m)) k y‖ ^ 2 *
          Real.exp (-X.wt (D + j) k y))) atTop (𝓝 (ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 *
          Real.exp (-X.wt (D + j) k y)))) :=
        ENNReal.tendsto_ofReal ((((hsub k y).norm.pow 2).const_mul _).mul_const _)
      exact ht.liminf_eq.ge

  have hGw : chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 *
      Real.exp (-X.wt (D + j) k y) * extFactor D ε 0 (extEv Z k y))) ≤ ENNReal.ofReal B := by
    refine chartIntegral_le_of_liminf X.A (fun m k y => ENNReal.ofReal (2 ^ D *
      ‖F₀ k y - Fn (φ' m) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) *
      extFactor D ε (δ (φ' m)) (extEv Z k y))) _ _ (fun m k => ?_) (fun m => hFnbd (φ' m))
      (fun k y => ?_)
    · exact aem_dens Z (D + j) k (fun x => F₀ k x - Fn (φ' m) k x)
        ((hF₀c k).sub (hcontFn _ k)) _ (measurable_extFactor D ε _)
    · rcases (extEv_nonneg Z k y).lt_or_eq with htpos | ht0
      · have hfac : Tendsto (fun m => extFactor D ε (δ (φ' m)) (extEv Z k y)) atTop
            (𝓝 (extFactor D ε 0 (extEv Z k y))) := by
          unfold extFactor
          refine Tendsto.div_const (Tendsto.inv₀ ?_ ?_) _
          · exact (tendsto_const_nhds.add ((hδlim.comp hφ'.tendsto_atTop).pow 2)).pow D
          · refine pow_ne_zero _ ?_
            rw [zero_pow two_ne_zero, add_zero]
            exact htpos.ne'
        have ht : Tendsto (fun m => ENNReal.ofReal (2 ^ D * ‖F₀ k y - Fn (φ' m) k y‖ ^ 2 *
            Real.exp (-X.wt (D + j) k y) * extFactor D ε (δ (φ' m)) (extEv Z k y))) atTop
            (𝓝 (ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y) *
              extFactor D ε 0 (extEv Z k y)))) :=
          ENNReal.tendsto_ofReal (((((hsub k y).norm.pow 2).const_mul _).mul_const _).mul hfac)
        exact ht.liminf_eq.ge
      · have h0 : extFactor D ε 0 (extEv Z k y) = 0 := by
          rw [← ht0]
          simp [extFactor, zero_pow (show D ≠ 0 by omega)]
        rw [h0, mul_zero, ENNReal.ofReal_zero]
        exact bot_le

  have hres0 := hN D X Z (D + j) ε hD hεpos' (F₀ - G) (fun k => (hF₀c k).sub (hcontG k))
    (fun k l x hx => by
      simp only [Pi.sub_apply]
      rw [hF₀tr k l x hx, hGmem.2.1 k l x hx]
      ring)
    (lt_of_le_of_lt hGw ENNReal.ofReal_lt_top)
  refine ⟨G, hGmem, fun x hx => ?_, ?_⟩
  · have h := hres0 x hx
    have h' : G (chartIdx X.A x) x = F₀ (chartIdx X.A x) x := by
      simp only [Pi.sub_apply, sub_eq_zero] at h
      exact h.symm
    rw [← hF₀res x hx]
    simp only [res, h']
  ·
    have hnum : 201 * θ + 201 / 200 * (c₁ * B) ≤ 140 * K := by
      have he := Real.exp_one_lt_d9
      have hl := Real.log_two_lt_d9
      have he0 := Real.exp_pos 1
      have hq : (1 + ε ^ 2) ^ D ≤ 201 / 200 := by linarith [hεb]
      have hc₁le : c₁ ≤ 2 * Real.exp 1 * (201 / 200) := by
        rw [hc₁]; gcongr
      have hel : Real.exp 1 * Real.log 2 < 1.8842 := by
        nlinarith [mul_lt_mul_of_pos_right he hl0]
      calc 201 * θ + 201 / 200 * (c₁ * B)
          ≤ 201 * θ + 201 / 200 * (2 * Real.exp 1 * (201 / 200) * B) := by
            have := mul_le_mul_of_nonneg_right hc₁le hBnn
            linarith
        _ = K * (2.01 + 1.010025 * (72 * (Real.exp 1 * Real.log 2) + 0.02 * Real.exp 1)) := by
            rw [hBeq, hθ]; ring
        _ ≤ K * 140 := by
            apply mul_le_mul_of_nonneg_left _ hK0
            nlinarith
        _ = 140 * K := by ring
    calc topNormSq X.A (X.wt (D + j)) G
        ≤ chartIntegral X.A (fun k y => ENNReal.ofReal 201 * ENNReal.ofReal (2 ^ D *
            ‖F₀ k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y)) + ENNReal.ofReal (201 / 200) *
            ENNReal.ofReal (2 ^ D * ‖(F₀ - G) k y‖ ^ 2 * Real.exp (-X.wt (D + j) k y))) := by
          unfold topNormSq
          refine chartIntegral_mono _ fun k y => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have htri : ‖G k y‖ ≤ ‖F₀ k y‖ + ‖(F₀ - G) k y‖ := by
            simpa using norm_sub_le (F₀ k y) (F₀ k y - G k y)
          have hp : 0 ≤ 2 ^ D * Real.exp (-X.wt (D + j) k y) := by positivity
          have hsq : ‖G k y‖ ^ 2 ≤ 201 * ‖F₀ k y‖ ^ 2 + 201 / 200 * ‖(F₀ - G) k y‖ ^ 2 := by
            nlinarith [norm_nonneg (G k y), norm_nonneg (F₀ k y), norm_nonneg ((F₀ - G) k y),
              sq_nonneg (200 * ‖F₀ k y‖ - ‖(F₀ - G) k y‖)]
          nlinarith [mul_le_mul_of_nonneg_right hsq hp]
      _ = ENNReal.ofReal 201 * topNormSq X.A (X.wt (D + j)) F₀ +
            ENNReal.ofReal (201 / 200) * topNormSq X.A (X.wt (D + j)) (F₀ - G) := by
          rw [chartIntegral_add _ _ _ (hF₀m _), chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top,
            chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top]
          rfl
      _ ≤ ENNReal.ofReal 201 * ENNReal.ofReal θ +
            ENNReal.ofReal (201 / 200) * ENNReal.ofReal (c₁ * B) := by
          exact add_le_add (mul_le_mul_right hF₀n _) (mul_le_mul_right hGb _)
      _ = ENNReal.ofReal (201 * θ + 201 / 200 * (c₁ * B)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (140 * K) := ENNReal.ofReal_le_ofReal hnum

end

end GroundTheory.Heights₂.Heights.EffectiveHS
