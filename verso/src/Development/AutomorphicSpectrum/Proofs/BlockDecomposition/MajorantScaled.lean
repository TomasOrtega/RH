import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantFiberBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantLePowNegStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDetInvMulMajorantStatement

noncomputable section

open MeasureTheory Matrix Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC

/- English proof (translation)
Introduce `h hdet`. Establish `hn : ∀ w : Fin 2 → ℂ, ‖w‖ = max ‖w 0‖ ‖w 1‖`. Introduce `w`. Use `le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_) (max_le (norm_le_pi_norm w 0) (norm_le_pi_norm w 1))` and prove the remaining obligations. Use `fin_cases i`.

Conclude with `le_max_left _ _`. Conclude with `le_max_right _ _`. Establish `hD : 0 < dt h` using `norm_pos_iff.mpr hdet`. Establish `he0 : eta h 0 = (Matrix.of h).det⁻¹ * (-h 1 0)`. Simplify using `[eta, Matrix.inv_def, Matrix.adjugate_fin_two]`.

Establish `he1 : eta h 1 = (Matrix.of h).det⁻¹ * h 0 0`. Simplify using `[eta, Matrix.inv_def, Matrix.adjugate_fin_two]`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hc`. Establish `hc0 : col h = 0` using `le_antisymm (not_lt.mp hc) (le_max_of_le_left (norm_nonneg _))`.

Establish `h0 : h 0 0 = 0`. Establish `: ‖h 0 0‖ ≤ 0` using `hc0 ▸ le_max_left _ _`. Conclude with `norm_le_zero_iff.mp this`. Establish `h1 : h 1 0 = 0`. Establish `: ‖h 1 0‖ ≤ 0` using `hc0 ▸ le_max_right _ _`.

Conclude with `norm_le_zero_iff.mp this`. Conclude with `hdet (by simp [Matrix.det_fin_two, h0, h1])`. Rewrite using `[hn, he0, he1, norm_mul, norm_mul, norm_neg, norm_inv, ← mul_max_of_nonneg _ _ (by positivity), col, dt, max_comm]`. Clear the denominators using the available nonvanishing facts.
-/
theorem L_eta : ∀ h : M22, (Matrix.of h).det ≠ 0 → 0 < col h ∧ ‖eta h‖ = col h / dt h := by
  intro h hdet
  have hn : ∀ w : Fin 2 → ℂ, ‖w‖ = max ‖w 0‖ ‖w 1‖ := by
    intro w
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
      (max_le (norm_le_pi_norm w 0) (norm_le_pi_norm w 1))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hD : 0 < dt h := norm_pos_iff.mpr hdet
  have he0 : eta h 0 = (Matrix.of h).det⁻¹ * (-h 1 0) := by
    simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]
  have he1 : eta h 1 = (Matrix.of h).det⁻¹ * h 0 0 := by
    simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]
  constructor
  · by_contra hc
    have hc0 : col h = 0 := le_antisymm (not_lt.mp hc) (le_max_of_le_left (norm_nonneg _))
    have h0 : h 0 0 = 0 := by
      have : ‖h 0 0‖ ≤ 0 := hc0 ▸ le_max_left _ _
      exact norm_le_zero_iff.mp this
    have h1 : h 1 0 = 0 := by
      have : ‖h 1 0‖ ≤ 0 := hc0 ▸ le_max_right _ _
      exact norm_le_zero_iff.mp this
    exact hdet (by simp [Matrix.det_fin_two, h0, h1])
  · rw [hn, he0, he1, norm_mul, norm_mul, norm_neg, norm_inv, ← mul_max_of_nonneg _ _ (by positivity), col, dt,
      max_comm]
    field_simp

/- English proof (translation)
Introduce `f`. Set `e` to `MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℂ)`. Establish `he : MeasurePreserving e volume volume` using `volume_preserving_piFinTwo _`. Set `s : M22 ≃ᵐ M22` to `e.trans (MeasurableEquiv.prodComm.trans e.symm)`. Establish `hs : MeasurePreserving s volume volume`.

Establish `hw : MeasurePreserving (Prod.swap : (Fin 2 → ℂ) × (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) volume volume` using `Measure.measurePreserving_swap`. Conclude with `((he.symm e).comp hw).comp he`. Establish `hsw : ∀ h, s h = swp h`. Introduce `h`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> rfl`. Use `hs.lintegral_comp_emb s.measurableEmbedding f` as an intermediate fact. Simplify `this` using `only [hsw]`.
-/
theorem L_swp : ∀ f : M22 → ENNReal, ∫⁻ h : M22, f (swp h) = ∫⁻ h : M22, f h := by
  intro f
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℂ)
  have he : MeasurePreserving e volume volume := volume_preserving_piFinTwo _
  let s : M22 ≃ᵐ M22 := e.trans (MeasurableEquiv.prodComm.trans e.symm)
  have hs : MeasurePreserving s volume volume := by
    have hw : MeasurePreserving (Prod.swap : (Fin 2 → ℂ) × (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) volume volume :=
      Measure.measurePreserving_swap
    exact ((he.symm e).comp hw).comp he
  have hsw : ∀ h, s h = swp h := by
    intro h
    funext i
    fin_cases i <;> rfl
  have := hs.lintegral_comp_emb s.measurableEmbedding f
  simpa only [hsw] using this

/- English proof (translation)
Introduce `ε β m`. Establish `h00 : Measurable fun h : M22 => h 0 0` using `(measurable_pi_apply 0).comp (measurable_pi_apply 0)`. Establish `h01 : Measurable fun h : M22 => h 0 1` using `(measurable_pi_apply 1).comp (measurable_pi_apply 0)`. Establish `h10 : Measurable fun h : M22 => h 1 0` using `(measurable_pi_apply 0).comp (measurable_pi_apply 1)`. Establish `h11 : Measurable fun h : M22 => h 1 1` using `(measurable_pi_apply 1).comp (measurable_pi_apply 1)`.

Establish `hz : Measurable fun h : M22 => h 1 1 - h 1 0 / h 0 0 * h 0 1` using `h11.sub ((h10.div h00).mul h01)`. Establish `hk : Measurable (kern ε β)`. Unfold `kern`. Use `fun_prop`. Establish `hset : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖ ∧ h 0 0 ≠ 0}` using `(measurableSet_le h10.norm h00.norm).inter (h00 (measurableSet_singleton 0).compl)`.

Unfold `gm`. Use `Measurable.ite hset ?_ measurable_const` and prove the remaining obligations. Use `hk.comp hz` as an intermediate fact. Simplify using `only [Function.comp_def] at this`. Conclude with `((((measurable_const.mul (h00.norm.pow_const _)).mul ((measurable_const.add h00.norm).pow_const m).inv).mul ((measurable_const.add h01.norm).pow_const m).inv).mul this)`.
-/
theorem L_measgm : ∀ (ε β : ℝ) (m : ℕ), Measurable (gm ε β m) := by
  intro ε β m
  have h00 : Measurable fun h : M22 => h 0 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 0)
  have h01 : Measurable fun h : M22 => h 0 1 := (measurable_pi_apply 1).comp (measurable_pi_apply 0)
  have h10 : Measurable fun h : M22 => h 1 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 1)
  have h11 : Measurable fun h : M22 => h 1 1 := (measurable_pi_apply 1).comp (measurable_pi_apply 1)
  have hz : Measurable fun h : M22 => h 1 1 - h 1 0 / h 0 0 * h 0 1 :=
    h11.sub ((h10.div h00).mul h01)
  have hk : Measurable (kern ε β) := by
    unfold kern
    fun_prop
  have hset : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖ ∧ h 0 0 ≠ 0} :=
    (measurableSet_le h10.norm h00.norm).inter (h00 (measurableSet_singleton 0).compl)
  unfold gm
  refine Measurable.ite hset ?_ measurable_const
  have := hk.comp hz
  simp only [Function.comp_def] at this
  exact ((((measurable_const.mul (h00.norm.pow_const _)).mul
    ((measurable_const.add h00.norm).pow_const m).inv).mul
    ((measurable_const.add h01.norm).pow_const m).inv).mul this)

/- English proof (translation)
Take `⟨C, hC, hg⟩` from `GlobalTheory.T.lintegral_majorant_le_pow_neg ε K m hε hK hk h3 hm2`. Use `⟨2 * C, by positivity, fun N hN β hβ => ?_⟩` and prove the remaining obligations. Establish `hg0 : ∀ h, 0 ≤ gm ε β m h`. Introduce `h`. Unfold `gm`.

Use `split_ifs`. Unfold `kern`. Check the signs of the components of the expression. Conclude with `le_rfl`. Establish `hmeas : Measurable (gm ε β m)` using `L_measgm ε β m`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun h => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_add (hg0 _) (hg0 _)]`. Conclude with `ENNReal.ofReal_le_ofReal (GlobalTheory.T.majorant_le_sum_swap ε β m N hε hβ hm2 hN h)`. Use `_ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m (swp h)) := lintegral_add_left hmeas.ennreal_ofReal _`.

Use `_ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) := by`. Rewrite using `[L_swp (fun h => ENNReal.ofReal (gm ε β m h))]`. Use `_ ≤ ENNReal.ofReal (C * β ^ (-ε)) + ENNReal.ofReal (C * β ^ (-ε)) := add_le_add (hg β hβ) (hg β hβ)`. Use `_ = ENNReal.ofReal (2 * C * β ^ (-ε)) := by`. Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hm_int (ε : ℝ) (hε : 0 < ε) (m : ℕ) (h3 : 3 ≤ m) (hm2 : 2 * ε ≤ m) (K : ℝ) (hK : 0 ≤ K)
    (hk : ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 * m ≤ N → ∀ β : ℝ, 0 < β →
      ∫⁻ h : M22, ENNReal.ofReal (hm ε N β h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  obtain ⟨C, hC, hg⟩ := GlobalTheory.T.lintegral_majorant_le_pow_neg ε K m hε hK hk h3 hm2
  refine ⟨2 * C, by positivity, fun N hN β hβ => ?_⟩
  have hg0 : ∀ h, 0 ≤ gm ε β m h := by
    intro h
    unfold gm
    split_ifs
    · unfold kern
      positivity
    · exact le_rfl
  have hmeas : Measurable (gm ε β m) := L_measgm ε β m
  calc ∫⁻ h : M22, ENNReal.ofReal (hm ε N β h)
      ≤ ∫⁻ h : M22, (ENNReal.ofReal (gm ε β m h) + ENNReal.ofReal (gm ε β m (swp h))) := by
        refine lintegral_mono fun h => ?_
        rw [← ENNReal.ofReal_add (hg0 _) (hg0 _)]
        exact ENNReal.ofReal_le_ofReal (GlobalTheory.T.majorant_le_sum_swap ε β m N hε hβ hm2 hN h)
    _ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m (swp h)) :=
        lintegral_add_left hmeas.ennreal_ofReal _
    _ = (∫⁻ h : M22, ENNReal.ofReal (gm ε β m h)) + ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) := by
        rw [L_swp (fun h => ENNReal.ofReal (gm ε β m h))]
    _ ≤ ENNReal.ofReal (C * β ^ (-ε)) + ENNReal.ofReal (C * β ^ (-ε)) := add_le_add (hg β hβ) (hg β hβ)
    _ = ENNReal.ofReal (2 * C * β ^ (-ε)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/- English proof (translation)
Introduce `ε hε`. Take `⟨K1, hK1, hk1⟩` from `GlobalTheory.T.lintegral_kernel_uniform_bound ε hε`. Take `⟨K2, hK2, hk2⟩` from `GlobalTheory.T.lintegral_kernel_uniform_bound (2 * ε) (by positivity)`. Use `set m : ℕ := max 3 ⌈2 * ε⌉₊ with hmdef`. Establish `h3 : 3 ≤ m` using `le_max_left _ _`.

Establish `hm2 : 2 * ε ≤ m` using `(Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)`. Take `⟨C, hC, hH⟩` from `hm_int ε hε m h3 hm2 K1 hK1 hk1`. Use `⟨2 * m, fun N hN => ⟨K2 * C, fun a b ha hb => ?_⟩⟩` and prove the remaining obligations. Establish `hNε : 2 * ε ≤ N`. Establish `: (2 * m : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `h0 : (0 : ℝ) ≤ m` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : 0 < ‖a‖` using `norm_pos_iff.mpr ha`. Establish `hB : 0 < ‖b‖` using `norm_pos_iff.mpr hb`. Use `set f : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b with hf`.

Establish `hfm : Measurable f` using `GlobalTheory.T.measurable_det_inv_mul_majorant N a b`. Establish `hf0 : ∀ p, 0 ≤ f p`. Introduce `p`. Simplify using `only [hf, jm]`. Check the signs of the components of the expression.

Establish `hper : ∀ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t)) ≤ ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h)`. Introduce `h`. Distinguish the cases in `hdet : (Matrix.of h).det = 0`. Simplify using `[hf, hdet]`. Establish `hD : 0 < dt h` using `norm_pos_iff.mpr hdet`.

Take `⟨hc, hE⟩` from `L_eta h hdet`. Establish `hE0 : 0 < ‖eta h‖` using `by rw [hE]; positivity`. Establish `hfe : ∀ t : ℂ, ENNReal.ofReal (f (h, t)) = ENNReal.ofReal ((dt h ^ 2)⁻¹) * ENNReal.ofReal (jm N h t a b)`. Introduce `t`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`.

Both sides reduce to the same expression. Repeatedly rewrite using `[hfe]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `(mul_le_mul_right (GlobalTheory.T.lintegral_majorant_fiber_bound ε K2 hε hK2 hk2 N hNε h a b ha hD hE0) _).trans ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`.

Use `ENNReal.ofReal_le_ofReal (le_of_eq ?_)` and prove the remaining obligations. Establish `hpow : (dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) = dt h ^ (-(2 + ε)) * col h ^ (-2 + 2 * ε)`. Rewrite using `[hE, Real.div_rpow hc.le hD.le, Real.rpow_add hD, Real.rpow_neg hD.le (2 + ε), Real.rpow_add hD, Real.rpow_add hD, two_mul ε, Real.rpow_add hD ε ε, Real.rpow_neg hD.le 2, Real.rpow_two]`. Establish `hP` using `Real.rpow_pos_of_pos hD ε`. Clear the denominators using the available nonvanishing facts.

Simplify using `only [hm]`. Rewrite using `[← hE]`. Combine the equalities or inequalities in the displayed calculation. Establish `hlin : ∫⁻ p, ENNReal.ofReal (f p) ≤ ENNReal.ofReal (K2 * C * (‖a‖ * ‖b‖) ^ (-ε))`. Rewrite using `[Measure.volume_eq_prod, lintegral_prod _ hfm.ennreal_ofReal.aemeasurable]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hA.le hB.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : Integrable f`.

Use `⟨hfm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]`. Conclude with `hlin.trans_lt ENNReal.ofReal_lt_top`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]`.

Conclude with `ENNReal.toReal_le_of_le_ofReal (by positivity) hlin`.
-/
theorem main : Ad3.K.LC.B.MajScaled := by
  intro ε hε
  obtain ⟨K1, hK1, hk1⟩ := GlobalTheory.T.lintegral_kernel_uniform_bound ε hε
  obtain ⟨K2, hK2, hk2⟩ := GlobalTheory.T.lintegral_kernel_uniform_bound (2 * ε) (by positivity)
  set m : ℕ := max 3 ⌈2 * ε⌉₊ with hmdef
  have h3 : 3 ≤ m := le_max_left _ _
  have hm2 : 2 * ε ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨C, hC, hH⟩ := hm_int ε hε m h3 hm2 K1 hK1 hk1
  refine ⟨2 * m, fun N hN => ⟨K2 * C, fun a b ha hb => ?_⟩⟩
  have hNε : 2 * ε ≤ N := by
    have : (2 * m : ℝ) ≤ N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set f : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b with hf
  have hfm : Measurable f := GlobalTheory.T.measurable_det_inv_mul_majorant N a b
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    simp only [hf, jm]
    positivity
  have hper : ∀ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t)) ≤
      ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h) := by
    intro h
    by_cases hdet : (Matrix.of h).det = 0
    · simp [hf, hdet]
    have hD : 0 < dt h := norm_pos_iff.mpr hdet
    obtain ⟨hc, hE⟩ := L_eta h hdet
    have hE0 : 0 < ‖eta h‖ := by rw [hE]; positivity
    have hfe : ∀ t : ℂ, ENNReal.ofReal (f (h, t)) =
        ENNReal.ofReal ((dt h ^ 2)⁻¹) * ENNReal.ofReal (jm N h t a b) := by
      intro t
      rw [← ENNReal.ofReal_mul (by positivity)]
      rfl
    simp_rw [hfe]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (GlobalTheory.T.lintegral_majorant_fiber_bound ε K2 hε hK2 hk2 N hNε h a b ha hD hE0) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hpow : (dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) =
        dt h ^ (-(2 + ε)) * col h ^ (-2 + 2 * ε) := by
      rw [hE, Real.div_rpow hc.le hD.le, Real.rpow_add hD, Real.rpow_neg hD.le (2 + ε), Real.rpow_add hD,
        Real.rpow_add hD, two_mul ε, Real.rpow_add hD ε ε, Real.rpow_neg hD.le 2, Real.rpow_two]
      have hP := Real.rpow_pos_of_pos hD ε
      field_simp
    simp only [hm]
    rw [← hE]
    calc _ = K2 * ‖a‖ ^ (-ε) * ((dt h ^ 2)⁻¹ * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε)) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by ring
      _ = _ := by rw [hpow]; ring
  have hlin : ∫⁻ p, ENNReal.ofReal (f p) ≤ ENNReal.ofReal (K2 * C * (‖a‖ * ‖b‖) ^ (-ε)) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hfm.ennreal_ofReal.aemeasurable]
    calc ∫⁻ h : M22, ∫⁻ t : ℂ, ENNReal.ofReal (f (h, t))
        ≤ ∫⁻ h : M22, ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (hm ε N ‖b‖ h) :=
          lintegral_mono hper
      _ = ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ∫⁻ h : M22, ENNReal.ofReal (hm ε N ‖b‖ h) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K2 * ‖a‖ ^ (-ε)) * ENNReal.ofReal (C * ‖b‖ ^ (-ε)) :=
          mul_le_mul_right (hH N hN ‖b‖ hB) _
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hA.le hB.le]
          congr 1
          ring
  have hint : Integrable f := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

end GlobalTheory.CompanionTheory.MajC
