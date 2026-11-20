import Mathlib

open MeasureTheory Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted.Gard

section Param

variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Establish `h : (fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1) = fun p => (iteratedFDeriv ℝ k Φ p).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ P Q)`. Use function extensionality and compare the values at `p`. Establish `e : (fun y => Φ (y, p.2)) = (fun z => Φ (z + (0, p.2))) ∘ (ContinuousLinearMap.inl ℝ P Q)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Establish `hs : ContDiff ℝ ∞ (fun z : P × Q => Φ (z + (0, p.2)))` using `hΦ.comp (contDiff_id.add contDiff_const)`. Rewrite using `[e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs _ (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `(ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))`.
-/
theorem continuous_iter_partial (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1 := by
  have h : (fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1) =
      fun p => (iteratedFDeriv ℝ k Φ p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
    funext p
    have e : (fun y => Φ (y, p.2)) =
        (fun z => Φ (z + (0, p.2))) ∘ (ContinuousLinearMap.inl ℝ P Q) := by
      funext y; simp
    have hs : ContDiff ℝ ∞ (fun z : P × Q => Φ (z + (0, p.2))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp
  rw [h]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

end Param

section Avg

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
The claim follows from `(hw.smul (hρ u)).integrable_of_hasCompactSupport hc.smul_right`.
-/
theorem integrable_w (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : G → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) (u : H) : Integrable (fun x => w x • ρ x u) μ :=
  (hw.smul (hρ u)).integrable_of_hasCompactSupport hc.smul_right

/- English proof (translation)
Set `L : H →ₗ[ℂ] H` to `{ toFun := fun u => ∫ x, w x • ρ x u ∂μ map_add' := fun u v => by`. Simplify using `only [map_add, smul_add]`. Conclude with `integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)`. Use the proof step `map_smul' := fun c u => by`. Simplify using `only [map_smul, RingHom.id_apply]`.

Rewrite using `[← integral_smul]`. Simplify using `only [smul_comm c] }`. Use `⟨L.mkContinuous (∫ x, ‖w x‖ ∂μ) fun u => ?_, fun u => rfl⟩` and prove the remaining obligations. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [norm_smul, hiso]`.

Conclude with `integral_mul_const _ _`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (hiso : ∀ x u, ‖ρ x u‖ = ‖u‖)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  refine ⟨L.mkContinuous (∫ x, ‖w x‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

/- English proof (translation)
Establish `hm` using `Measure.map_right_mul_eq_modularCharacterFun_smul μ k`. Establish `hemb : MeasurableEmbedding fun x : G => x * k` using `(MeasurableEquiv.mulRight k).measurableEmbedding`. Establish `hpos` using `hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1`. Establish `e1 : ∫ x, w (x * k) ∂μ = ∫ x, w x ∂μ`. Rewrite using `[← integral_mul_left_eq_self (fun x => w (x * k)) k⁻¹]`.

Simplify using `only [hk]`. Rewrite `e1` using `[← hemb.integral_map, hm, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]`. Establish `e2 : Measure.modularCharacterFun k = 1`. Establish `: ((Measure.modularCharacterFun k : NNReal) : ℝ) = 1`. Apply `mul_right_cancel₀ hpos.ne'` to reduce the goal to its premises.

Rewrite using `[e1, one_mul]`. Conclude with `this` after adjusting the coercions. Rewrite using `[← hemb.integral_map, hm, e2, one_smul]`.
-/
theorem integral_mul_right_of_conj {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w)
    (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (F : G → H) :
    ∫ x, F (x * k) ∂μ = ∫ x, F x ∂μ := by
  have hm := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have hemb : MeasurableEmbedding fun x : G => x * k := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have e1 : ∫ x, w (x * k) ∂μ = ∫ x, w x ∂μ := by
    rw [← integral_mul_left_eq_self (fun x => w (x * k)) k⁻¹]
    simp only [hk]
  rw [← hemb.integral_map, hm, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at e1
  have e2 : Measure.modularCharacterFun k = 1 := by
    have : ((Measure.modularCharacterFun k : NNReal) : ℝ) = 1 := by
      apply mul_right_cancel₀ hpos.ne'
      rw [e1, one_mul]
    exact_mod_cast this
  rw [← hemb.integral_map, hm, e2, one_smul]

/- English proof (translation)
Rewrite using `[← (ρ g).integral_comp_comm (integrable_w μ ρ hρ hw hc u), ← integral_mul_left_eq_self (fun x => w (g⁻¹ * x) • ρ x u) g]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[inv_mul_cancel_left, hmul, ContinuousLinearMap.map_smul_of_tower]`.
-/
theorem apply_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (g : G) (u : H) :
    ρ g (∫ x, w x • ρ x u ∂μ) = ∫ x, w (g⁻¹ * x) • ρ x u ∂μ := by
  rw [← (ρ g).integral_comp_comm (integrable_w μ ρ hρ hw hc u),
    ← integral_mul_left_eq_self (fun x => w (g⁻¹ * x) • ρ x u) g]
  congr 1
  funext x
  rw [inv_mul_cancel_left, hmul, ContinuousLinearMap.map_smul_of_tower]

/- English proof (translation)
Rewrite using `[apply_alt μ ρ hρ hmul hw hc, ← integral_mul_right_of_conj μ hw hc h0 h1 k hk (fun x => w (k⁻¹ * x) • ρ x u)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[← mul_assoc, hk, hmul]`.
-/
theorem T_comm (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (h0 : 0 ≤ w) (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (u : H) :
    ∫ x, w x • ρ x (ρ k u) ∂μ = ρ k (∫ x, w x • ρ x u ∂μ) := by
  rw [apply_alt μ ρ hρ hmul hw hc,
    ← integral_mul_right_of_conj μ hw hc h0 h1 k hk (fun x => w (k⁻¹ * x) • ρ x u)]
  congr 1
  funext x
  rw [← mul_assoc, hk, hmul]

/- English proof (translation)
Set `A : G → (Y →L[ℂ] H)` to `fun x => (ρ x).comp Y.subtypeL - Y.subtypeL`. Establish `hA : Continuous A`. Rewrite using `[continuous_clm_apply]`. Introduce `y`. Conclude with `(hρ y).sub continuous_const`.

Establish `hA1 : A 1 = 0`. Use extensionality with `y`. Simplify using `[A, h1]`. Use `⟨{x | ‖A x‖ < 1 / 2}, ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Conclude with `(isOpen_lt hA.norm continuous_const).mem_nhds (by simp [hA1])`.

Use `(A x).le_opNorm ⟨y, hy⟩` as an intermediate fact. Conclude with `this.trans (mul_le_mul_of_nonneg_right (le_of_lt hx) (norm_nonneg _))`.
-/
theorem exists_nhds_close (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (h1 : ∀ u, ρ 1 u = u)
    (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, ∀ y ∈ Y, ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖ := by
  let A : G → (Y →L[ℂ] H) := fun x => (ρ x).comp Y.subtypeL - Y.subtypeL
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro y
    exact (hρ y).sub continuous_const
  have hA1 : A 1 = 0 := by
    ext y
    simp [A, h1]
  refine ⟨{x | ‖A x‖ < 1 / 2}, ?_, fun x hx y hy => ?_⟩
  · exact (isOpen_lt hA.norm continuous_const).mem_nhds (by simp [hA1])
  · have := (A x).le_opNorm ⟨y, hy⟩
    exact this.trans (mul_le_mul_of_nonneg_right (le_of_lt hx) (norm_nonneg _))

/- English proof (translation)
Establish `hpos` using `hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1`. Establish `hwi : Integrable w μ` using `hw.integrable_of_hasCompactSupport hc`. Establish `e : ∫ x, w x • (ρ x y - y) ∂μ = -((∫ x, w x ∂μ) • y)`. Simplify using `only [smul_sub]`. Rewrite using `[integral_sub (integrable_w μ ρ hρ hw hc y) (hwi.smul_const y), hT, integral_smul_const, zero_sub]`.

Establish `b : ‖∫ x, w x • (ρ x y - y) ∂μ‖ ≤ ∫ x, w x * (1 / 2 * ‖y‖) ∂μ`. Use `norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_of_nonneg (h0 x)]`. Distinguish the cases in `hx : w x = 0`. Simplify using `[hx]`.

Conclude with `mul_le_mul_of_nonneg_left (hy x hx) (h0 x)`. Rewrite `b` using `[e, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const]`. Use `le_of_mul_le_mul_left b hpos` as an intermediate fact. Establish `h2 : ‖y‖ = 0` using `by linarith [norm_nonneg y]`. Conclude with `norm_eq_zero.1 h2`.
-/
theorem eq_zero_of_alt_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w) (h1 : w 1 ≠ 0)
    (y : H) (hy : ∀ x, w x ≠ 0 → ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖) (hT : ∫ x, w x • ρ x y ∂μ = 0) : y = 0 := by
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport hc
  have e : ∫ x, w x • (ρ x y - y) ∂μ = -((∫ x, w x ∂μ) • y) := by
    simp only [smul_sub]
    rw [integral_sub (integrable_w μ ρ hρ hw hc y) (hwi.smul_const y), hT, integral_smul_const, zero_sub]
  have b : ‖∫ x, w x • (ρ x y - y) ∂μ‖ ≤ ∫ x, w x * (1 / 2 * ‖y‖) ∂μ := by
    refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_of_nonneg (h0 x)]
    by_cases hx : w x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left (hy x hx) (h0 x)
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at b
  have := le_of_mul_le_mul_left b hpos
  have h2 : ‖y‖ = 0 := by linarith [norm_nonneg y]
  exact norm_eq_zero.1 h2

end Avg

/- English proof (translation)
Introduce `v hv`. Set `L : Y →ₗ[ℂ] Y` to `(T : H →ₗ[ℂ] H).restrict hT`. Establish `hL : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`.

Conclude with `Subtype.ext (hi y y.2 (congrArg Subtype.val hy))`. Take `⟨u, hu⟩` from `LinearMap.surjective_of_injective hL ⟨v, hv⟩`. Conclude with `⟨u, congrArg Subtype.val hu⟩`.
-/
theorem exists_preimage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (Y : Submodule ℂ H)
    [FiniteDimensional ℂ Y] (T : H →L[ℂ] H) (hT : ∀ y ∈ Y, T y ∈ Y) (hi : ∀ y ∈ Y, T y = 0 → y = 0) :
    ∀ v ∈ Y, ∃ u, T u = v := by
  intro v hv
  let L : Y →ₗ[ℂ] Y := (T : H →ₗ[ℂ] H).restrict hT
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hi y y.2 (congrArg Subtype.val hy))
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hL ⟨v, hv⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end CompanionTheory.D.gk.admitted.Gard
