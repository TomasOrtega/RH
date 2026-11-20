import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeConst

/- English proof (translation)
Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations. Establish `: Tendsto (fun r : ℝ => s * r) (𝓝 0) (𝓝 (s * 0))` using `(continuous_const.mul continuous_id).tendsto 0`. Rewrite `this` using `[mul_zero]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with r hr`.

Conclude with `mul_pos hs hr`.
-/
theorem tendsto_mul_nhdsGT {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => s * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun r : ℝ => s * r) (𝓝 0) (𝓝 (s * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hs hr

/- English proof (translation)
Use `((hh.comp (tendsto_mul_nhdsGT hs)).const_mul (s ^ d)).congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with r hr`. Establish `hr' : (0 : ℝ) < r` using `hr`. Simplify using `only [Function.comp, mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_scaled {h : ℝ → ℝ} {d : ℕ} {L s : ℝ} (hs : 0 < s)
    (hh : Tendsto (fun r => h r / r ^ d) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun r => h (s * r) / r ^ d) (𝓝[>] 0) (𝓝 (s ^ d * L)) := by
  refine ((hh.comp (tendsto_mul_nhdsGT hs)).const_mul (s ^ d)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  simp only [Function.comp, mul_pow]
  field_simp

/- English proof (translation)
Establish `t1 : Tendsto (fun κ : ℝ => κ⁻¹ ^ d * L) (𝓝[>] 1) (𝓝 L)`. Establish `: ContinuousAt (fun κ : ℝ => κ⁻¹ ^ d * L) 1`. Use `ContinuousAt.mul (ContinuousAt.pow (continuousAt_inv₀ one_ne_zero) d) continuousAt_const` and prove the remaining obligations. Simplify using `using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`. Establish `t2 : Tendsto (fun κ : ℝ => κ ^ d * L) (𝓝[>] 1) (𝓝 L)`.

Establish `: ContinuousAt (fun κ : ℝ => κ ^ d * L) 1` using `by fun_prop`. Simplify using `using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))`. Use `tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨κ, h1, h2⟩` from `((t1.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists`. Establish `h2' : (1 : ℝ) < κ` using `h2`.

Use `filter_upwards [(tendsto_scaled (inv_pos.2 (by linarith : 0 < κ)) hh).eventually (lt_mem_nhds h1), hs κ h2', self_mem_nhdsWithin] with r b1 b2 b3`. Establish `hr' : (0 : ℝ) < r` using `b3`. Conclude with `b1.trans_le (div_le_div_of_nonneg_right b2.1 (by positivity))`. Take `⟨κ, h1, h2⟩` from `((t2.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists`. Establish `h2' : (1 : ℝ) < κ` using `h2`.

Use `filter_upwards [(tendsto_scaled (by linarith : 0 < κ) hh).eventually (gt_mem_nhds h1), hs κ h2', self_mem_nhdsWithin] with r b1 b2 b3`. Establish `hr' : (0 : ℝ) < r` using `b3`. Conclude with `(div_le_div_of_nonneg_right b2.2 (by positivity)).trans_lt b1`.
-/
theorem tendsto_of_squeeze {f h : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hh : Tendsto (fun r => h r / r ^ d) (𝓝[>] 0) (𝓝 L))
    (hs : ∀ κ : ℝ, 1 < κ → ∀ᶠ r in 𝓝[>] (0 : ℝ), h (κ⁻¹ * r) ≤ f r ∧ f r ≤ h (κ * r)) :
    Tendsto (fun r => f r / r ^ d) (𝓝[>] 0) (𝓝 L) := by
  have t1 : Tendsto (fun κ : ℝ => κ⁻¹ ^ d * L) (𝓝[>] 1) (𝓝 L) := by
    have : ContinuousAt (fun κ : ℝ => κ⁻¹ ^ d * L) 1 := by
      refine ContinuousAt.mul (ContinuousAt.pow (continuousAt_inv₀ one_ne_zero) d) continuousAt_const
    simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have t2 : Tendsto (fun κ : ℝ => κ ^ d * L) (𝓝[>] 1) (𝓝 L) := by
    have : ContinuousAt (fun κ : ℝ => κ ^ d * L) 1 := by fun_prop
    simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨κ, h1, h2⟩ := ((t1.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have h2' : (1 : ℝ) < κ := h2
    filter_upwards [(tendsto_scaled (inv_pos.2 (by linarith : 0 < κ)) hh).eventually (lt_mem_nhds h1),
      hs κ h2', self_mem_nhdsWithin] with r b1 b2 b3
    have hr' : (0 : ℝ) < r := b3
    exact b1.trans_le (div_le_div_of_nonneg_right b2.1 (by positivity))
  · obtain ⟨κ, h1, h2⟩ := ((t2.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have h2' : (1 : ℝ) < κ := h2
    filter_upwards [(tendsto_scaled (by linarith : 0 < κ) hh).eventually (gt_mem_nhds h1),
      hs κ h2', self_mem_nhdsWithin] with r b1 b2 b3
    have hr' : (0 : ℝ) < r := b3
    exact (div_le_div_of_nonneg_right b2.2 (by positivity)).trans_lt b1

/- English proof (translation)
Use `borelize V`. Use `haveI : ProperSpace V := FiniteDimensional.proper_real V`. Use `set lam : Measure V := Measure.addHaar`. Take `⟨c, hc0, hct, hc⟩` from `GlobalTheory.CompactDualExists.exists_density_of_chart V M G lam μ e m ι L he h0 hd hL hL1 hm hn`. Establish `hb0 : 0 < (lam (ball 0 1)).toReal` using `ENNReal.toReal_pos (measure_ball_pos lam 0 one_pos).ne' measure_ball_lt_top.ne`.

Establish `hfin : ∀ r : ℝ, μ (e '' ball 0 r) ≠ ⊤` using `fun r => (lt_of_le_of_lt (measure_mono (Set.image_mono ball_subset_closedBall)) ((isCompact_closedBall (0 : V) r).image he).measure_lt_top).ne`. Use `⟨c.toReal * (lam (ball 0 1)).toReal, mul_pos (ENNReal.toReal_pos hc0 hct) hb0, tendsto_of_squeeze (h := fun r => (μ (e '' ball 0 r)).toReal) ?_ ?_⟩` and prove the remaining obligations. Use `(((ENNReal.tendsto_toReal hct).comp hc).mul_const _).congr' ?_ filter_upwards [self_mem_nhdsWithin] with r hr` and prove the remaining obligations. Establish `hr' : (0 : ℝ) < r` using `hr`. Simplify using `only [Function.comp]`.

Rewrite using `[Measure.addHaar_ball_of_pos lam 0 hr', ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Clear the denominators using the available nonvanishing facts. Introduce `κ hκ`. Establish `hκ0 : 0 < κ` using `by linarith`. Establish `hη : 0 < (1 - κ⁻¹) / 2`.

Use `inv_lt_one_of_one_lt₀ hκ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hd.hasFDerivAt.isLittleO.def hη`. Take `⟨δ, hδ, h2⟩` from `Metric.eventually_nhds_iff.1 h1`. Establish `h3 : ∀ x : V, ‖x‖ < δ → |‖m (e x) - m 1‖ - ‖x‖| ≤ (1 - κ⁻¹) / 2 * ‖x‖`.

Introduce `x hx`. Establish `h4` using `@h2 x (by simpa using hx)`. Simplify using `only [h0, sub_zero, LinearIsometry.coe_toContinuousLinearMap] at h4`. Establish `h5` using `abs_norm_sub_norm_le (m (e x) - m 1) (ι x)`. Rewrite `h5` using `[ι.norm_map]`.

Conclude with `h5.trans h4`. Establish `h6` using `hn δ hδ`. Rewrite `h6` using `[hi.nhds_eq_comap, mem_comap]`. Take `⟨t, ht, hts⟩` from `h6`. Take `⟨ρ, hρ, hρt⟩` from `nhds_basis_closedBall.mem_iff.1 ht`.

Establish `hk1 : κ⁻¹ * κ = 1` using `inv_mul_cancel₀ hκ0.ne'`. Establish `hk2 : 0 < κ⁻¹` using `inv_pos.2 hκ0`. Establish `hk3 : κ⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hκ`. Use `filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hρ)] with r hr`. Take `⟨hr0, hr⟩` from `hr`.

Rewrite `hr` using `[lt_min_iff]`. Establish `s2 : {g | ‖m g - m 1‖ ≤ r} ⊆ e '' ball 0 (κ * r)`. Introduce `g hg`. Establish `hg' : ‖m g - m 1‖ ≤ r` using `hg`. Take `⟨x, hx, rfl⟩` from `hts (hρt (mem_closedBall_iff_norm.2 (hg'.trans hr.2.le)))`.

Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[mem_ball_zero_iff]`. Establish `h7` using `(abs_le.1 (h3 x hx)).1`. Establish `h8 : (1 + κ⁻¹) / 2 * ‖x‖ ≤ r` using `by linarith`. Assume the negation of the conclusion as `h9`.

Use `push Not at h9`. Establish `h10 : (1 + κ⁻¹) / 2 * (κ * r) ≤ (1 + κ⁻¹) / 2 * ‖x‖` using `by gcongr`. Establish `h11 : (1 + κ⁻¹) / 2 * (κ * r) = (κ + 1) / 2 * r` using `by field_simp`. Use the polynomial consequences of the given equalities and inequalities. Establish `s1 : e '' ball 0 (κ⁻¹ * r) ⊆ {g | ‖m g - m 1‖ ≤ r}`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[mem_ball_zero_iff]`. Establish `h7` using `(abs_le.1 (h3 x (by nlinarith [hr.1]))).2`. Establish `h8 : ‖m (e x) - m 1‖ ≤ (3 - κ⁻¹) / 2 * ‖x‖` using `by linarith`. Establish `h9 : (3 - κ⁻¹) / 2 * ‖x‖ ≤ (3 - κ⁻¹) / 2 * (κ⁻¹ * r)` using `mul_le_mul_of_nonneg_left hx.le (by linarith)`.

Establish `h10 : (3 - κ⁻¹) / 2 * κ⁻¹ ≤ 1` using `by nlinarith`. Express the relevant statement in the definitionally equal form `‖m (e x) - m 1‖ ≤ r`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `⟨ENNReal.toReal_mono (ne_top_of_le_ne_top (hfin _) (measure_mono s2)) (measure_mono s1), ENNReal.toReal_mono (hfin _) (measure_mono s2)⟩`.
-/
theorem exists_limit_of_chart (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (e : V → G) (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e)
    (h0 : e 0 = 1) (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h)) (hn : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G))
    (hi : IsInducing m) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun r : ℝ => (μ {g | ‖m g - m 1‖ ≤ r}).toReal / r ^ Module.finrank ℝ V)
      (𝓝[>] 0) (𝓝 A) := by
  borelize V
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  set lam : Measure V := Measure.addHaar
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.CompactDualExists.exists_density_of_chart V M G lam μ e m ι L he h0 hd
    hL hL1 hm hn
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam 0 one_pos).ne' measure_ball_lt_top.ne
  have hfin : ∀ r : ℝ, μ (e '' ball 0 r) ≠ ⊤ := fun r =>
    (lt_of_le_of_lt (measure_mono (Set.image_mono ball_subset_closedBall))
      ((isCompact_closedBall (0 : V) r).image he).measure_lt_top).ne
  refine ⟨c.toReal * (lam (ball 0 1)).toReal, mul_pos (ENNReal.toReal_pos hc0 hct) hb0,
    tendsto_of_squeeze (h := fun r => (μ (e '' ball 0 r)).toReal) ?_ ?_⟩
  · refine (((ENNReal.tendsto_toReal hct).comp hc).mul_const _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    simp only [Function.comp]
    rw [Measure.addHaar_ball_of_pos lam 0 hr', ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    field_simp
  · intro κ hκ
    have hκ0 : 0 < κ := by linarith
    have hη : 0 < (1 - κ⁻¹) / 2 := by
      have := inv_lt_one_of_one_lt₀ hκ
      linarith
    have h1 := hd.hasFDerivAt.isLittleO.def hη
    obtain ⟨δ, hδ, h2⟩ := Metric.eventually_nhds_iff.1 h1
    have h3 : ∀ x : V, ‖x‖ < δ → |‖m (e x) - m 1‖ - ‖x‖| ≤ (1 - κ⁻¹) / 2 * ‖x‖ := by
      intro x hx
      have h4 := @h2 x (by simpa using hx)
      simp only [h0, sub_zero, LinearIsometry.coe_toContinuousLinearMap] at h4
      have h5 := abs_norm_sub_norm_le (m (e x) - m 1) (ι x)
      rw [ι.norm_map] at h5
      exact h5.trans h4
    have h6 := hn δ hδ
    rw [hi.nhds_eq_comap, mem_comap] at h6
    obtain ⟨t, ht, hts⟩ := h6
    obtain ⟨ρ, hρ, hρt⟩ := nhds_basis_closedBall.mem_iff.1 ht
    have hk1 : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ0.ne'
    have hk2 : 0 < κ⁻¹ := inv_pos.2 hκ0
    have hk3 : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hρ)] with r hr
    obtain ⟨hr0, hr⟩ := hr
    rw [lt_min_iff] at hr
    have s2 : {g | ‖m g - m 1‖ ≤ r} ⊆ e '' ball 0 (κ * r) := by
      intro g hg
      have hg' : ‖m g - m 1‖ ≤ r := hg
      obtain ⟨x, hx, rfl⟩ := hts (hρt (mem_closedBall_iff_norm.2 (hg'.trans hr.2.le)))
      refine ⟨x, ?_, rfl⟩
      rw [mem_ball_zero_iff] at hx ⊢
      have h7 := (abs_le.1 (h3 x hx)).1
      have h8 : (1 + κ⁻¹) / 2 * ‖x‖ ≤ r := by linarith
      by_contra h9
      push Not at h9
      have h10 : (1 + κ⁻¹) / 2 * (κ * r) ≤ (1 + κ⁻¹) / 2 * ‖x‖ := by gcongr
      have h11 : (1 + κ⁻¹) / 2 * (κ * r) = (κ + 1) / 2 * r := by field_simp
      nlinarith
    have s1 : e '' ball 0 (κ⁻¹ * r) ⊆ {g | ‖m g - m 1‖ ≤ r} := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ball_zero_iff] at hx
      have h7 := (abs_le.1 (h3 x (by nlinarith [hr.1]))).2
      have h8 : ‖m (e x) - m 1‖ ≤ (3 - κ⁻¹) / 2 * ‖x‖ := by linarith
      have h9 : (3 - κ⁻¹) / 2 * ‖x‖ ≤ (3 - κ⁻¹) / 2 * (κ⁻¹ * r) :=
        mul_le_mul_of_nonneg_left hx.le (by linarith)
      have h10 : (3 - κ⁻¹) / 2 * κ⁻¹ ≤ 1 := by nlinarith
      change ‖m (e x) - m 1‖ ≤ r
      nlinarith
    exact ⟨ENNReal.toReal_mono (ne_top_of_le_ne_top (hfin _) (measure_mono s2)) (measure_mono s1),
      ENNReal.toReal_mono (hfin _) (measure_mono s2)⟩

variable {n : ℕ}

def lieJ (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * Jm ε + Jm ε * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX,
      smul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lieJ {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ lieJ ε ↔ Xᴴ * Jm ε + Jm ε * X = 0 := Iff.rfl

def cplx (ε : Fin n → Bool) : (lieJ ε × lieJ ε) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun p := p.1.1 + Complex.I • p.2.1
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]; abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply,
      smul_comm c Complex.I]

/- English proof (translation)
Establish `hJ` using `Jm_mul_self ε`. Establish `hJ'` using `Jm_conjTranspose ε`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨a, b⟩ h`.

Establish `h1 : a.1 = -(Complex.I • b.1)` using `eq_neg_of_add_eq_zero_left h`. Establish `h2` using `mem_lieJ.1 a.2`. Establish `h3` using `eq_neg_of_add_eq_zero_left (mem_lieJ.1 b.2)`. Rewrite `h2` using `[h1, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.neg_mul, Matrix.smul_mul, h3, Matrix.mul_neg, Matrix.mul_smul, Complex.star_def, Complex.conj_I]`. Establish `h4 : (-2 * Complex.I) • (Jm ε * b.1) = 0`.

Rewrite using `[← h2]`. Use `module`. Establish `h5 : Jm ε * b.1 = 0`. Use `(smul_eq_zero.1 h4).resolve_left ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `h6 : b.1 = 0`. Rewrite using `[← Matrix.one_mul b.1, ← hJ, Matrix.mul_assoc, h5, Matrix.mul_zero]`. Rewrite `h1` using `[h6, smul_zero, neg_zero]`. Conclude with `Prod.ext (Subtype.ext h1) (Subtype.ext h6)`. Introduce `Z`.

Establish `e1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z` using `by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]`. Establish `e2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Establish `e3 : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ', Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Use `⟨(⟨(1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε), ?_⟩, ⟨(-Complex.I / 2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε), ?_⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[mem_lieJ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_sub, e3, Matrix.sub_mul, Matrix.mul_sub, e1, e2]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this]`. Use `module`.

Rewrite using `[mem_lieJ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_add, e3, Matrix.add_mul, Matrix.mul_add, e1, e2]`. Establish `: star (-Complex.I / 2 : ℂ) = Complex.I / 2` using `by simp`. Rewrite using `[this]`. Use `module`. Express the relevant statement in the definitionally equal form `(1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε) + Complex.I • ((-Complex.I / 2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) = Z`.

Establish `: Complex.I * (-Complex.I / 2) = 1 / 2`. Rewrite using `[← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]`. Rewrite using `[smul_smul, this]`. Use `module`.
-/
theorem cplx_bijective (ε : Fin n → Bool) : Function.Bijective (cplx ε) := by
  have hJ := Jm_mul_self ε
  have hJ' := Jm_conjTranspose ε
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ h
    have h1 : a.1 = -(Complex.I • b.1) := eq_neg_of_add_eq_zero_left h
    have h2 := mem_lieJ.1 a.2
    have h3 := eq_neg_of_add_eq_zero_left (mem_lieJ.1 b.2)
    rw [h1, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.neg_mul, Matrix.smul_mul, h3,
      Matrix.mul_neg, Matrix.mul_smul, Complex.star_def, Complex.conj_I] at h2
    have h4 : (-2 * Complex.I) • (Jm ε * b.1) = 0 := by
      rw [← h2]; module
    have h5 : Jm ε * b.1 = 0 := by
      refine (smul_eq_zero.1 h4).resolve_left ?_
      simp
    have h6 : b.1 = 0 := by
      rw [← Matrix.one_mul b.1, ← hJ, Matrix.mul_assoc, h5, Matrix.mul_zero]
    rw [h6, smul_zero, neg_zero] at h1
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h6)
  · intro Z
    have e1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    have e2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    have e3 : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ', Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    refine ⟨(⟨(1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε), ?_⟩,
      ⟨(-Complex.I / 2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε), ?_⟩), ?_⟩
    · rw [mem_lieJ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.conjTranspose_sub, e3, Matrix.sub_mul, Matrix.mul_sub, e1, e2]
      have : star (1 / 2 : ℂ) = 1 / 2 := by simp
      rw [this]; module
    · rw [mem_lieJ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.conjTranspose_add, e3, Matrix.add_mul, Matrix.mul_add, e1, e2]
      have : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
      rw [this]; module
    · change (1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε) +
        Complex.I • ((-Complex.I / 2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) = Z
      have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]
      rw [smul_smul, this]; module

/- English proof (translation)
Establish `h` using `(LinearEquiv.ofBijective _ (cplx_bijective ε)).finrank_eq`. Rewrite `h` using `[Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex, Fintype.card_fin]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem finrank_lieJ (ε : Fin n → Bool) : Module.finrank ℝ (lieJ ε) = n ^ 2 := by
  have h := (LinearEquiv.ofBijective _ (cplx_bijective ε)).finrank_eq
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex, Fintype.card_fin] at h
  nlinarith

def expJ (ε : Fin n → Bool) (X : lieJ ε) : UJ ε :=
  ⟨⟨NormedSpace.exp X.1, NormedSpace.exp (-X.1), UpqExpChart.exp_mul_exp_neg _,
    UpqExpChart.exp_neg_mul_exp _⟩, UpqExpChart.exp_unitary (Jm_mul_self ε) X.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uMat_expJ (ε : Fin n → Bool) (X : lieJ ε) : uMat (expJ ε X) = NormedSpace.exp X.1 := rfl

/- English proof (translation)
Introduce `_ _ h` and use `Subtype.ext (Units.ext h)`.
-/
theorem uMat_injective (ε : Fin n → Bool) : Function.Injective (uMat : UJ ε → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_uMat (ε : Fin n → Bool) : Continuous (uMat : UJ ε → _) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `UpqExpChart.continuous_matExp.comp continuous_subtype_val`. Conclude with `UpqExpChart.continuous_matExp.comp continuous_subtype_val.neg`.
-/
theorem continuous_expJ (ε : Fin n → Bool) : Continuous (expJ ε) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact UpqExpChart.continuous_matExp.comp continuous_subtype_val
  · exact UpqExpChart.continuous_matExp.comp continuous_subtype_val.neg

/- English proof (translation)
Take `⟨e, he, h0⟩` from `UpqExpChart.exists_chart (n := Fin n)`. Establish `hJ` using `Jm_mul_self ε`. Use `set J := Jm ε with hJdef`. Establish `hinj : Set.InjOn NormedSpace.exp e.source` using `he ▸ e.injOn`. Establish `hτ : Continuous fun Z : Matrix (Fin n) (Fin n) ℂ => J * (-Z)ᴴ * J` using `(continuous_const.matrix_mul continuous_neg.matrix_conjTranspose).matrix_mul continuous_const`.

Use `set W : Set (Matrix (Fin n) (Fin n) ℂ) := e.source ∩ (fun Z => J * (-Z)ᴴ * J) ⁻¹' e.source with hW`. Establish `hWo : IsOpen W` using `e.open_source.inter (e.open_source.preimage hτ)`. Establish `hW0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ W` using `⟨h0, by simpa using h0⟩`. Take `⟨T, hT, hTU⟩` from `(mem_nhds_subtype _ _ _).1 hU`. Take `⟨V, hVT, hV, hV0⟩` from `mem_nhds_iff.1 hT`.

Establish `hopen : IsOpen (NormedSpace.exp '' (V ∩ W))` using `he ▸ e.isOpen_image_of_subset_source (hV.inter hWo) fun _ h => h.2.1`. Use `mem_of_superset ((hopen.preimage (continuous_uMat ε)).mem_nhds ⟨0, ⟨hV0, hW0⟩, NormedSpace.exp_zero⟩) ?_` and prove the remaining obligations. Introduce and unpack `g ⟨Z, ⟨hZV, hZW⟩, hZ⟩`. Establish `hu : (uMat g)ᴴ * J * uMat g = J` using `g.2`. Rewrite `hu` using `[← hZ]`.

Establish `hfix : J * (-Z)ᴴ * J = Z` using `hinj hZW.2 hZW.1 (UpqExpChart.exp_twist hJ hu)`. Establish `hmem : Z ∈ lieJ ε`. Express the relevant statement in the definitionally equal form `Zᴴ * J + J * Z = 0`. Establish `: J * Z = -(Zᴴ * J)` using `by conv_lhs => rw [← hfix]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.conjTranspose_neg, Matrix.neg_mul]`.

Rewrite using `[this, add_neg_cancel]`. Conclude with `⟨⟨Z, hmem⟩, hTU (hVT hZV), uMat_injective ε hZ⟩`.
-/
theorem expJ_image_mem_nhds (ε : Fin n → Bool) {U : Set (lieJ ε)} (hU : U ∈ 𝓝 (0 : lieJ ε)) :
    expJ ε '' U ∈ 𝓝 (1 : UJ ε) := by
  obtain ⟨e, he, h0⟩ := UpqExpChart.exists_chart (n := Fin n)
  have hJ := Jm_mul_self ε
  set J := Jm ε with hJdef
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have hτ : Continuous fun Z : Matrix (Fin n) (Fin n) ℂ => J * (-Z)ᴴ * J :=
    (continuous_const.matrix_mul continuous_neg.matrix_conjTranspose).matrix_mul continuous_const
  set W : Set (Matrix (Fin n) (Fin n) ℂ) :=
    e.source ∩ (fun Z => J * (-Z)ᴴ * J) ⁻¹' e.source with hW
  have hWo : IsOpen W := e.open_source.inter (e.open_source.preimage hτ)
  have hW0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ W := ⟨h0, by simpa using h0⟩
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨V, hVT, hV, hV0⟩ := mem_nhds_iff.1 hT
  have hopen : IsOpen (NormedSpace.exp '' (V ∩ W)) :=
    he ▸ e.isOpen_image_of_subset_source (hV.inter hWo) fun _ h => h.2.1
  refine mem_of_superset ((hopen.preimage (continuous_uMat ε)).mem_nhds
    ⟨0, ⟨hV0, hW0⟩, NormedSpace.exp_zero⟩) ?_
  rintro g ⟨Z, ⟨hZV, hZW⟩, hZ⟩
  have hu : (uMat g)ᴴ * J * uMat g = J := g.2
  rw [← hZ] at hu
  have hfix : J * (-Z)ᴴ * J = Z := hinj hZW.2 hZW.1 (UpqExpChart.exp_twist hJ hu)
  have hmem : Z ∈ lieJ ε := by
    change Zᴴ * J + J * Z = 0
    have : J * Z = -(Zᴴ * J) := by
      conv_lhs => rw [← hfix]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
        Matrix.conjTranspose_neg, Matrix.neg_mul]
    rw [this, add_neg_cancel]
  exact ⟨⟨Z, hmem⟩, hTU (hVT hZV), uMat_injective ε hZ⟩

open scoped Matrix.Norms.Frobenius in
/- English proof (translation)
Rewrite using `[Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]`. Simplify using `[Formalism.REAL.hs]`.
-/
theorem sqrt_hs (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (Formalism.REAL.hs A) = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp [Formalism.REAL.hs]

open scoped Matrix.Norms.Frobenius in
/- English proof (translation)
Set `L₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)` to `LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _`. Establish `hL₀ : Continuous L₀` using `L₀.continuous_of_finiteDimensional`. Establish `h` using `exists_limit_of_chart (lieJ ε) (Matrix (Fin n) (Fin n) ℂ) (UJ ε) (muG ε) (expJ ε) uMat (lieJ ε).subtypeₗᵢ (fun g => L₀ (uMat g)) (continuous_expJ ε) (uMat_injective ε (by`. Rewrite using `[uMat_expJ]`. Conclude with `(NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))))`.

Use the proof step `(HasStrictFDerivAt.comp (0 : lieJ ε) (g := NormedSpace.exp) (f := Subtype.val) CompactDualExists.exp_strict (lieJ ε).subtypeL.hasStrictFDerivAt)`. Use the proof step `(hL₀.comp (continuous_uMat ε)).continuousAt`. Use the proof step `(by ext1 A; exact Matrix.one_mul A) (fun g h => rfl)`. Use the proof step `(fun r hr => expJ_image_mem_nhds ε (ball_mem_nhds 0 hr))`. Use the proof step `(uJEmb n ε).1.isInducing`.

Rewrite `h` using `[finrank_lieJ]`. Simplify using `only [sqrt_hs]`. Conclude with `h`.
-/
theorem exists_limit (ε : Fin n → Bool) : ∃ A : ℝ, 0 < A ∧ Tendsto
    (fun r : ℝ => (muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
    (𝓝[>] 0) (𝓝 A) := by
  let L₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have h := exists_limit_of_chart (lieJ ε) (Matrix (Fin n) (Fin n) ℂ) (UJ ε) (muG ε) (expJ ε) uMat
    (lieJ ε).subtypeₗᵢ (fun g => L₀ (uMat g)) (continuous_expJ ε)
    (uMat_injective ε (by
      rw [uMat_expJ]; exact (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))))
    (HasStrictFDerivAt.comp (0 : lieJ ε) (g := NormedSpace.exp) (f := Subtype.val)
      CompactDualExists.exp_strict (lieJ ε).subtypeL.hasStrictFDerivAt)
    (hL₀.comp (continuous_uMat ε)).continuousAt
    (by ext1 A; exact Matrix.one_mul A) (fun g h => rfl)
    (fun r hr => expJ_image_mem_nhds ε (ball_mem_nhds 0 hr))
    (uJEmb n ε).1.isInducing
  rw [finrank_lieJ] at h
  simp only [sqrt_hs]
  exact h

/- English proof (translation)
Introduce `n ε`. Take `⟨A, hA, h⟩` from `exists_limit ε`. Establish `hB : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal` using `ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' measure_ball_lt_top.ne`. Use `⟨_ / A, div_pos hB hA, ?_, fun c' hc' => ?_⟩` and prove the remaining obligations. Unfold `IsGauge`.

Use `h.const_mul ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal / A)` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hA.ne']`. Simplify `this` using `only [mul_div_assoc]`. Unfold `IsGauge at hc'`. Use `h.const_mul c'` as an intermediate fact.

Simplify using `only [mul_div_assoc] at hc'`. Rewrite using `[eq_div_iff hA.ne']`. Conclude with `tendsto_nhds_unique this hc'`.
-/
theorem exists_unique_isGauge : ∀ (n : ℕ) (ε : Fin n → Bool),
    ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c := by
  intro n ε
  obtain ⟨A, hA, h⟩ := exists_limit ε
  have hB : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' measure_ball_lt_top.ne
  refine ⟨_ / A, div_pos hB hA, ?_, fun c' hc' => ?_⟩
  · unfold IsGauge
    have := h.const_mul ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal / A)
    rw [div_mul_cancel₀ _ hA.ne'] at this
    simpa only [mul_div_assoc] using this
  · unfold IsGauge at hc'
    have := h.const_mul c'
    simp only [mul_div_assoc] at hc'
    rw [eq_div_iff hA.ne']
    exact tendsto_nhds_unique this hc'

end GlobalTheory.GaugeConst
