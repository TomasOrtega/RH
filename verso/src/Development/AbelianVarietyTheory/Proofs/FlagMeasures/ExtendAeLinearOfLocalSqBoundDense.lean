import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]`. Simplify using `only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h`. Conclude with `h.symm`.
-/
theorem lintegral_enorm_sq_Lp {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (f : Lp E 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

/- English proof (translation)
Establish `e` using `eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := ν) (p := 2) (by norm_num)`. Simplify using `only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at e`. Rewrite `h` using `[← e, ENNReal.ofReal_pow hB]`. Conclude with `(ENNReal.pow_le_pow_left_iff two_ne_zero).1 h`.
-/
theorem eLpNorm_two_le_of_lintegral {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (g : Q → E) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm g 2 ν ≤ ENNReal.ofReal B := by
  have e := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := ν) (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at e
  rw [← e, ENNReal.ofReal_pow hB] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

/- English proof (translation)
Introduce `X _ μ K hK hcov H _ _ E _ _ _ D hD F hadd hsmul hbd`. Use `choose C hC using hbd`. Use `set w : ℕ → ℝ := fun n => (2:ℝ)⁻¹ ^ n / (1 + max (C n) 0) with hw`. Establish `hwpos : ∀ n, 0 < w n` using `fun n => div_pos (pow_pos (by norm_num) n) (by have := le_max_right (C n) 0; linarith)`. Establish `hw0 : ∀ n, ENNReal.ofReal (w n) ≠ 0` using `fun n => by`.

Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `hwpos n`. Use `set ν : Measure X := Measure.sum (fun n => ENNReal.ofReal (w n) • μ.restrict (K n)) with hν`. Establish `hint : ∀ f : X → ENNReal, ∫⁻ x, f x ∂ν = ∑' n, ENNReal.ofReal (w n) * ∫⁻ x in K n, f x ∂μ`. Introduce `f`.

Rewrite using `[hν, lintegral_sum_measure]`. Use `congr 1`. Use function extensionality and compare the values at `n`. Rewrite using `[lintegral_smul_measure, smul_eq_mul]`. Establish `hνμ : ν ≪ μ`.

Use `Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_` and prove the remaining obligations. Rewrite using `[hν, Measure.sum_apply _ hs]`. Use `ENNReal.tsum_eq_zero.2 fun n => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul, measure_mono_null Set.inter_subset_left h0, mul_zero]`. Establish `hμν : μ ≪ ν`.

Use `Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_` and prove the remaining obligations. Rewrite `h0` using `[hν, Measure.sum_apply _ hs, ENNReal.tsum_eq_zero]`. Establish `h1 : ∀ n, μ (s ∩ K n) = 0` using `fun n => by`. Use `h0 n` as an intermediate fact. Rewrite `this` using `[Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 this).resolve_left (hw0 n)`. Establish `: s = ⋃ n, s ∩ K n` using `by rw [← Set.inter_iUnion, hcov, Set.inter_univ]`. Rewrite using `[this]`. Conclude with `measure_iUnion_null h1`. Establish `hsq : ∀ u ∈ D, ∫⁻ x, ‖F u x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((Real.sqrt 2 * ‖u‖) ^ 2)`.

Introduce `u hu`. Rewrite using `[hint]`. Establish `hB : (Real.sqrt 2 * ‖u‖) ^ 2 = ∑' n : ℕ, (2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2`. Rewrite using `[tsum_mul_right, tsum_geometric_inv_two, mul_pow, Real.sq_sqrt (by norm_num)]`. Rewrite using `[hB, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)]`.

Use `ENNReal.tsum_le_tsum fun n => ?_` and prove the remaining obligations. Establish `h2 : ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C n * ‖u‖ ^ 2)` using `(hC n u hu).2`. Establish `hM : 0 ≤ max (C n) 0` using `le_max_right _ _`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))`.

Use `_ = ENNReal.ofReal (w n * (max (C n) 0 * ‖u‖ ^ 2)) := (ENNReal.ofReal_mul (hwpos n).le).symm`. Use `_ ≤ ENNReal.ofReal ((2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2) := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[hw]`. Simplify using `only`.

Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) n) (sq_nonneg ‖u‖)]`. Establish `hae : ∀ u ∈ D, AEStronglyMeasurable (F u) ν` using `fun u hu => aestronglyMeasurable_sum_measure_iff.2 fun n => (hC n u hu).1.smul_measure _`. Establish `hmem : ∀ u ∈ D, MemLp (F u) 2 ν` using `fun u hu => ⟨hae u hu, (eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u hu)).trans_lt ENNReal.ofReal_lt_top⟩`. Set `L : D →ₗ[ℂ] Lp E 2 ν` to `{ toFun := fun u => (hmem u u.2).toLp (F u) map_add' := fun u v => by`.

Rewrite using `[← MemLp.toLp_add]`. Conclude with `MemLp.toLp_congr _ _ (hνμ.ae_le (hadd u u.2 v v.2))`. Use the proof step `map_smul' := fun b u => by`. Rewrite using `[RingHom.id_apply, ← MemLp.toLp_const_smul]`. Conclude with `MemLp.toLp_congr _ _ (hνμ.ae_le (hsmul b u u.2)) }`.

Establish `hL : ∀ u (hu : u ∈ D), L ⟨u, hu⟩ = (hmem u hu).toLp (F u)` using `fun _ _ => rfl`. Establish `hLb : ∃ c, ∀ u : D, ‖L u‖ ≤ c * ‖D.subtype u‖`. Use `⟨Real.sqrt 2, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[show L u = (hmem u u.2).toLp (F u) from rfl, Lp.norm_toLp]`. Conclude with `ENNReal.toReal_le_of_le_ofReal (by positivity) (eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u u.2))`.

Establish `hdense : DenseRange D.subtype` using `hD.denseRange_val`. Use `set Ext : H →L[ℂ] Lp E 2 ν := L.extendOfNorm D.subtype with hExtdef`. Establish `hExt : ∀ u (hu : u ∈ D), Ext u = (hmem u hu).toLp (F u)` using `fun u hu => by`. Rewrite using `[← hL u hu]`. Conclude with `LinearMap.extendOfNorm_eq hdense hLb ⟨u, hu⟩`.

Set `T : H → X → E` to `fun u => if u ∈ D then F u else ⇑(Ext u)`. Establish `hTae : ∀ u, T u =ᵐ[ν] Ext u`. Introduce `u`. Distinguish the cases in `hu : u ∈ D`. Simplify using `only [T, if_pos hu]`.

Rewrite using `[hExt u hu]`. Conclude with `(MemLp.coeFn_toLp _).symm`. Simplify using `only [T, if_neg hu]`. Both sides reduce to the same expression. Establish `hres : ∀ n, μ.restrict (K n) ≪ ν` using `fun n => (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hμν`.

Use `⟨T, fun u hu => if_pos hu, fun u u' => ?_, fun b u => ?_, fun n => ?_⟩` and prove the remaining obligations. Use `hμν.ae_le ?_ filter_upwards [hTae (u + u'), hTae u, hTae u', Lp.coeFn_add (Ext u) (Ext u')] with x h1 h2 h3 h4` and prove the remaining obligations. Rewrite using `[h1, map_add, h4, Pi.add_apply, ← h2, ← h3]`. Use `hμν.ae_le ?_ filter_upwards [hTae (b • u), hTae u, Lp.coeFn_smul b (Ext u)] with x h1 h2 h4` and prove the remaining obligations. Rewrite using `[h1, map_smul, h4, Pi.smul_apply, ← h2]`.

Use `⟨‖Ext‖ ^ 2 / w n, fun u => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `((Lp.aestronglyMeasurable (Ext u)).congr (hTae u).symm).mono_ac (hres n)`. Establish `e1 : ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ = ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ` using `lintegral_congr_ae ((hres n).ae_le ((hTae u).mono fun x hx => by simp only [hx]))`. Establish `e2 : ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2)`. Combine the equalities or inequalities in the displayed calculation.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (Ext.le_opNorm u) 2`. Establish `hd : ENNReal.ofReal (‖Ext‖ ^ 2 / w n * ‖u‖ ^ 2) = ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) / ENNReal.ofReal (w n)`. Rewrite using `[← ENNReal.ofReal_div_of_pos (hwpos n)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ ≤ _`. Rewrite using `[e1, hd, ENNReal.le_div_iff_mul_le (Or.inl (hw0 n)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]`. Conclude with `e2`.
-/
theorem extend_ae_linear_of_local_sq : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : Submodule ℂ H), Dense (D : Set H) → ∀ F : H → X → E,
    (∀ u ∈ D, ∀ u' ∈ D, F (u + u') =ᵐ[μ] fun x => F u x + F u' x) →
    (∀ (b : ℂ), ∀ u ∈ D, F (b • u) =ᵐ[μ] fun x => b • F u x) →
    (∀ n, ∃ C : ℝ, ∀ u ∈ D, AEStronglyMeasurable (F u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖F u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    ∃ T : H → X → E, (∀ u ∈ D, T u = F u) ∧
      (∀ u u' : H, T (u + u') =ᵐ[μ] fun x => T u x + T u' x) ∧
      (∀ (b : ℂ) (u : H), T (b • u) =ᵐ[μ] fun x => b • T u x) ∧
      (∀ n, ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (T u) (μ.restrict (K n)) ∧
        ∫⁻ x in K n, (‖T u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) := by
  intro X _ μ K hK hcov H _ _ E _ _ _ D hD F hadd hsmul hbd
  classical
  choose C hC using hbd
  set w : ℕ → ℝ := fun n => (2:ℝ)⁻¹ ^ n / (1 + max (C n) 0) with hw
  have hwpos : ∀ n, 0 < w n := fun n =>
    div_pos (pow_pos (by norm_num) n) (by have := le_max_right (C n) 0; linarith)
  have hw0 : ∀ n, ENNReal.ofReal (w n) ≠ 0 := fun n => by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hwpos n
  set ν : Measure X := Measure.sum (fun n => ENNReal.ofReal (w n) • μ.restrict (K n)) with hν
  have hint : ∀ f : X → ENNReal,
      ∫⁻ x, f x ∂ν = ∑' n, ENNReal.ofReal (w n) * ∫⁻ x in K n, f x ∂μ := by
    intro f
    rw [hν, lintegral_sum_measure]
    congr 1; funext n
    rw [lintegral_smul_measure, smul_eq_mul]
  have hνμ : ν ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      measure_mono_null Set.inter_subset_left h0, mul_zero]
  have hμν : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs, ENNReal.tsum_eq_zero] at h0
    have h1 : ∀ n, μ (s ∩ K n) = 0 := fun n => by
      have := h0 n
      rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (hw0 n)
    have : s = ⋃ n, s ∩ K n := by rw [← Set.inter_iUnion, hcov, Set.inter_univ]
    rw [this]; exact measure_iUnion_null h1
  have hsq : ∀ u ∈ D, ∫⁻ x, ‖F u x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((Real.sqrt 2 * ‖u‖) ^ 2) := by
    intro u hu
    rw [hint]
    have hB : (Real.sqrt 2 * ‖u‖) ^ 2 = ∑' n : ℕ, (2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2 := by
      rw [tsum_mul_right, tsum_geometric_inv_two, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hB, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    have h2 : ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C n * ‖u‖ ^ 2) := (hC n u hu).2
    have hM : 0 ≤ max (C n) 0 := le_max_right _ _
    calc ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (w n) * ENNReal.ofReal (max (C n) 0 * ‖u‖ ^ 2) := by
          gcongr
          exact h2.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
      _ = ENNReal.ofReal (w n * (max (C n) 0 * ‖u‖ ^ 2)) := (ENNReal.ofReal_mul (hwpos n).le).symm
      _ ≤ ENNReal.ofReal ((2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hw]
          simp only
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) n) (sq_nonneg ‖u‖)]
  have hae : ∀ u ∈ D, AEStronglyMeasurable (F u) ν := fun u hu =>
    aestronglyMeasurable_sum_measure_iff.2 fun n => (hC n u hu).1.smul_measure _
  have hmem : ∀ u ∈ D, MemLp (F u) 2 ν := fun u hu =>
    ⟨hae u hu, (eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u hu)).trans_lt
      ENNReal.ofReal_lt_top⟩
  let L : D →ₗ[ℂ] Lp E 2 ν :=
    { toFun := fun u => (hmem u u.2).toLp (F u)
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hadd u u.2 v v.2))
      map_smul' := fun b u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hsmul b u u.2)) }
  have hL : ∀ u (hu : u ∈ D), L ⟨u, hu⟩ = (hmem u hu).toLp (F u) := fun _ _ => rfl
  have hLb : ∃ c, ∀ u : D, ‖L u‖ ≤ c * ‖D.subtype u‖ := by
    refine ⟨Real.sqrt 2, fun u => ?_⟩
    rw [show L u = (hmem u u.2).toLp (F u) from rfl, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u u.2))
  have hdense : DenseRange D.subtype := hD.denseRange_val
  set Ext : H →L[ℂ] Lp E 2 ν := L.extendOfNorm D.subtype with hExtdef
  have hExt : ∀ u (hu : u ∈ D), Ext u = (hmem u hu).toLp (F u) := fun u hu => by
    rw [← hL u hu]
    exact LinearMap.extendOfNorm_eq hdense hLb ⟨u, hu⟩
  let T : H → X → E := fun u => if u ∈ D then F u else ⇑(Ext u)
  have hTae : ∀ u, T u =ᵐ[ν] Ext u := by
    intro u
    by_cases hu : u ∈ D
    · simp only [T, if_pos hu]
      rw [hExt u hu]
      exact (MemLp.coeFn_toLp _).symm
    · simp only [T, if_neg hu]
      rfl
  have hres : ∀ n, μ.restrict (K n) ≪ ν := fun n =>
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hμν
  refine ⟨T, fun u hu => if_pos hu, fun u u' => ?_, fun b u => ?_, fun n => ?_⟩
  · refine hμν.ae_le ?_
    filter_upwards [hTae (u + u'), hTae u, hTae u', Lp.coeFn_add (Ext u) (Ext u')]
      with x h1 h2 h3 h4
    rw [h1, map_add, h4, Pi.add_apply, ← h2, ← h3]
  · refine hμν.ae_le ?_
    filter_upwards [hTae (b • u), hTae u, Lp.coeFn_smul b (Ext u)] with x h1 h2 h4
    rw [h1, map_smul, h4, Pi.smul_apply, ← h2]
  · refine ⟨‖Ext‖ ^ 2 / w n, fun u => ⟨?_, ?_⟩⟩
    · exact ((Lp.aestronglyMeasurable (Ext u)).congr (hTae u).symm).mono_ac (hres n)
    · have e1 : ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ = ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ :=
        lintegral_congr_ae ((hres n).ae_le ((hTae u).mono fun x hx => by simp only [hx]))
      have e2 : ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) := by
        calc _ ≤ ∑' m, ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ :=
              ENNReal.le_tsum (f := fun m => ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ) n
          _ = ∫⁻ x, ‖Ext u x‖ₑ ^ 2 ∂ν := (hint _).symm
          _ = ENNReal.ofReal (‖Ext u‖ ^ 2) := lintegral_enorm_sq_Lp ν _
          _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (Ext.le_opNorm u) 2
      have hd : ENNReal.ofReal (‖Ext‖ ^ 2 / w n * ‖u‖ ^ 2)
          = ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) / ENNReal.ofReal (w n) := by
        rw [← ENNReal.ofReal_div_of_pos (hwpos n)]
        congr 1; ring
      change ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ ≤ _
      rw [e1, hd, ENNReal.le_div_iff_mul_le (Or.inl (hw0 n)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact e2

end GlobalTheory
