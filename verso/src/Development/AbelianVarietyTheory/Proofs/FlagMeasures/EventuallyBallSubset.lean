import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormExpSubOneLeExpNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrderedProductExpExpandingRealSmul

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory

namespace ProductChart

section Measure
open Metric Set Filter Topology
open scoped ENNReal

/- English proof (translation)
Establish `he : MeasurableEmbedding (U.domRestrict Θ)` using `ContinuousOn.measurableEmbedding hU.measurableSet hΘ.continuousOn hinj`. Use `set ν : Measure (EuclideanSpace ℝ (Fin N)) := (μ.comap (U.domRestrict Θ)).map Subtype.val with hν`. Establish `hνa : ∀ A, MeasurableSet A → ν A = μ (Θ '' (A ∩ U))`. Introduce `A hA`. Rewrite using `[hν, Measure.map_apply measurable_subtype_coe hA, he.comap_apply]`.

Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_preimage, Subtype.exists, Set.mem_inter_iff, Set.domRestrict_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hA, rfl⟩`.

Conclude with `⟨a, ⟨hA, ha⟩, rfl⟩`. Introduce and unpack `⟨a, ⟨hA, ha⟩, rfl⟩`. Conclude with `⟨a, ha, hA, rfl⟩`. Use `haveI : IsFiniteMeasureOnCompacts (K • ν) := ⟨fun A hA => by`. Rewrite using `[Measure.smul_apply, smul_eq_mul, hνa A hA.measurableSet]`.

Use `ENNReal.mul_lt_top hK.lt_top ?_` and prove the remaining obligations. Conclude with `(measure_mono (image_mono Set.inter_subset_left)).trans_lt (hA.image hΘ).measure_lt_top⟩`. Use `haveI : IsLocallyFiniteMeasure (K • ν) := inferInstance`. Establish `hle : volume.restrict U ≤ K • ν`. Use `Measure.le_iff.2 fun A hA => ?_` and prove the remaining obligations.

Rewrite using `[Measure.restrict_apply hA]`. Use `le_trans ?_ (measure_mono (μ := K • ν) (Set.inter_subset_left (t := U)))` and prove the remaining obligations. Use `ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_` and prove the remaining obligations. Use `(Besicovitch.vitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin N)))).measure_le_of_frequently_le (ρ := a • volume) (K • ν) Measure.smul_absolutelyContinuous (A ∩ U) ?_` as an intermediate fact. Simplify using `using this`.

Introduce `x hx`. Use `(Besicovitch.tendsto_filterAt volume x).frequently ?_` and prove the remaining obligations. Establish `h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ U` using `(eventually_closedBall_subset (hU.mem_nhds hx.2)).filter_mono nhdsWithin_le_nhds`. Use `((hb x hx.2 a ha).and h1).frequently.mono fun r hr => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, hνa _ measurableSet_closedBall, Set.inter_eq_left.2 hr.2]`.

Conclude with `hr.1`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[hν, lintegral_map (f := fun t => Φ (Θ t)) (hΦ.comp hΘ.measurable) measurable_subtype_coe, ← Set.range_domRestrict, ← he.map_comap, he.lintegral_map]`. Both sides reduce to the same expression.
-/
theorem lintegral_le_of_balls {N : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (Θ : EuclideanSpace ℝ (Fin N) → Y) (U : Set (EuclideanSpace ℝ (Fin N))) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (hU : IsOpen U) (hΘ : Continuous Θ) (hinj : InjOn Θ U)
    (hb : ∀ t ∈ U, ∀ a : ℝ≥0∞, a < 1 →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), a * volume (closedBall t r) ≤ K * μ (Θ '' closedBall t r))
    (Φ : Y → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ t in U, Φ (Θ t) ≤ K * ∫⁻ y in Θ '' U, Φ y ∂μ := by
  have he : MeasurableEmbedding (U.domRestrict Θ) :=
    ContinuousOn.measurableEmbedding hU.measurableSet hΘ.continuousOn hinj
  set ν : Measure (EuclideanSpace ℝ (Fin N)) := (μ.comap (U.domRestrict Θ)).map Subtype.val with hν
  have hνa : ∀ A, MeasurableSet A → ν A = μ (Θ '' (A ∩ U)) := by
    intro A hA
    rw [hν, Measure.map_apply measurable_subtype_coe hA, he.comap_apply]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, Set.mem_inter_iff, Set.domRestrict_apply]
    constructor
    · rintro ⟨a, ha, hA, rfl⟩; exact ⟨a, ⟨hA, ha⟩, rfl⟩
    · rintro ⟨a, ⟨hA, ha⟩, rfl⟩; exact ⟨a, ha, hA, rfl⟩
  haveI : IsFiniteMeasureOnCompacts (K • ν) := ⟨fun A hA => by
    rw [Measure.smul_apply, smul_eq_mul, hνa A hA.measurableSet]
    refine ENNReal.mul_lt_top hK.lt_top ?_
    exact (measure_mono (image_mono Set.inter_subset_left)).trans_lt (hA.image hΘ).measure_lt_top⟩
  haveI : IsLocallyFiniteMeasure (K • ν) := inferInstance
  have hle : volume.restrict U ≤ K • ν := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.restrict_apply hA]
    refine le_trans ?_ (measure_mono (μ := K • ν) (Set.inter_subset_left (t := U)))
    refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
    have := (Besicovitch.vitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin N)))).measure_le_of_frequently_le
      (ρ := a • volume) (K • ν) Measure.smul_absolutelyContinuous (A ∩ U) ?_
    · simpa using this
    intro x hx
    refine (Besicovitch.tendsto_filterAt volume x).frequently ?_
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ U :=
      (eventually_closedBall_subset (hU.mem_nhds hx.2)).filter_mono nhdsWithin_le_nhds
    refine ((hb x hx.2 a ha).and h1).frequently.mono fun r hr => ?_
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      hνa _ measurableSet_closedBall, Set.inter_eq_left.2 hr.2]
    exact hr.1
  calc ∫⁻ t in U, Φ (Θ t) ≤ ∫⁻ t, Φ (Θ t) ∂(K • ν) := lintegral_mono' hle le_rfl
    _ = K * ∫⁻ t, Φ (Θ t) ∂ν := by rw [lintegral_smul_measure, smul_eq_mul]
    _ = K * ∫⁻ y in Θ '' U, Φ y ∂μ := by
      congr 1
      rw [hν, lintegral_map (f := fun t => Φ (Θ t)) (hΦ.comp hΘ.measurable) measurable_subtype_coe,
        ← Set.range_domRestrict, ← he.map_comap, he.lintegral_map]
      rfl

end Measure

section Algebra

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/- English proof (translation)
Establish `h1` using `(hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)`. Establish `h2` using `(hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)`. Simplify using `only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, zero_add] at h1 h2`. Rewrite `h2` using `[← Real.exp_eq_exp_ℝ]`. Use `h1.norm_le_of_bounded h2 fun k => ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, norm_inv, Real.norm_natCast, smul_eq_mul]`. Use `gcongr`. Conclude with `norm_pow_le' x (by omega)`.
-/
theorem norm_exp_sub_one_le (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
    Nat.cast_one, inv_one, pow_zero, one_smul, zero_add] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun k => ?_
  rw [norm_smul, norm_inv, Real.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_pow_le' x (by omega)

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/- English proof (translation)
Establish `h : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1)` using `by noncomm_ring`. Establish `h1` using `norm_mul_le (x - 1) (y - 1)`. Establish `h2 : ‖x - 1‖ * ‖y - 1‖ ≤ (a - 1) * (b - 1)` using `mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)`. Establish `h3` using `norm_add₃_le (a := (x - 1) * (y - 1)) (b := x - 1) (c := y - 1)`. Rewrite using `[h]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_mul_sub_one_le {x y : A} {a b : ℝ} (hx : ‖x - 1‖ ≤ a - 1) (hy : ‖y - 1‖ ≤ b - 1) :
    ‖x * y - 1‖ ≤ a * b - 1 := by
  have h : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by noncomm_ring
  have h1 := norm_mul_le (x - 1) (y - 1)
  have h2 : ‖x - 1‖ * ‖y - 1‖ ≤ (a - 1) * (b - 1) :=
    mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)
  have h3 := norm_add₃_le (a := (x - 1) * (y - 1)) (b := x - 1) (c := y - 1)
  rw [h]; nlinarith

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/- English proof (translation)
Establish `h : x * e * y - e = (x - 1) * e * (y - 1) + (x - 1) * e + e * (y - 1)` using `by noncomm_ring`. Establish `ha : 0 ≤ a - 1` using `(norm_nonneg _).trans hx`. Establish `h1 : ‖(x - 1) * e‖ ≤ a - 1` using `(norm_mul_le _ _).trans (by`. Use `mul_le_mul hx he (norm_nonneg _) ha` as an intermediate fact. Use the proof step `linarith)`.

Establish `h2 : ‖e * (y - 1)‖ ≤ a - 1` using `(norm_mul_le _ _).trans (by`. Use `mul_le_mul he hy (norm_nonneg _) zero_le_one` as an intermediate fact. Use the proof step `linarith)`. Establish `h4 : ‖(x - 1) * e * (y - 1)‖ ≤ (a - 1) * (a - 1)` using `(norm_mul_le _ _).trans (mul_le_mul h1 hy (norm_nonneg _) ha)`. Establish `h3` using `norm_add₃_le (a := (x - 1) * e * (y - 1)) (b := (x - 1) * e) (c := e * (y - 1))`.

Rewrite using `[h]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_conj_sub_le {x y e : A} {a : ℝ} (hx : ‖x - 1‖ ≤ a - 1) (hy : ‖y - 1‖ ≤ a - 1)
    (he : ‖e‖ ≤ 1) : ‖x * e * y - e‖ ≤ a * a - 1 := by
  have h : x * e * y - e = (x - 1) * e * (y - 1) + (x - 1) * e + e * (y - 1) := by noncomm_ring
  have ha : 0 ≤ a - 1 := (norm_nonneg _).trans hx
  have h1 : ‖(x - 1) * e‖ ≤ a - 1 := (norm_mul_le _ _).trans (by
    have := mul_le_mul hx he (norm_nonneg _) ha; linarith)
  have h2 : ‖e * (y - 1)‖ ≤ a - 1 := (norm_mul_le _ _).trans (by
    have := mul_le_mul he hy (norm_nonneg _) zero_le_one; linarith)
  have h4 : ‖(x - 1) * e * (y - 1)‖ ≤ (a - 1) * (a - 1) := (norm_mul_le _ _).trans
    (mul_le_mul h1 hy (norm_nonneg _) ha)
  have h3 := norm_add₃_le (a := (x - 1) * e * (y - 1)) (b := (x - 1) * e) (c := e * (y - 1))
  rw [h]; nlinarith

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨0, 1, by simp, by simp, by simp, by simpa using hasStrictFDerivAt_const _ _, by simp⟩`. Consider the case `succ m ih`. Take `⟨L, B, h1, h2, h3, h4, h5⟩` from `ih (fun i => E i.succ) (fun i => φ i.succ) (fun i => hE _) (fun i => hφ _)`. Use `letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A`.

Establish `hd : HasStrictFDerivAt (fun y => NormedSpace.exp (φ 0 y • E 0)) ((φ 0).smulRight (NormedSpace.exp (φ 0 x • E 0) * E 0)) x`. Use `(hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (E 0) (φ 0 x)).hasStrictFDerivAt.comp x (φ 0).hasStrictFDerivAt` as an intermediate fact. Use `HasStrictFDerivAt.congr_fderiv this ?_` and prove the remaining obligations. Use extensionality with `v`. Simplify using the standard rewrite rules.

Establish `hn : ∀ u : ℝ, |u| ≤ s → ‖NormedSpace.exp (u • E 0) - 1‖ ≤ Real.exp s - 1`. Introduce `u hu`. Use `(norm_exp_sub_one_le _).trans ?_` and prove the remaining obligations. Use `gcongr`. Rewrite using `[norm_smul, Real.norm_eq_abs]`.

Use `mul_le_mul hu (hE 0) (norm_nonneg _) hs` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : NormedSpace.exp ((-φ 0 x) • E 0) * NormedSpace.exp (φ 0 x • E 0) = 1`. Rewrite using `[← NormedSpace.exp_add_of_commute (((Commute.refl (E 0)).smul_left _).smul_right _), ← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]`. Establish `hexp : Real.exp (((m + 1 : ℕ) : ℝ) * s) = Real.exp (m * s) * Real.exp s`.

Rewrite using `[← Real.exp_add]`. Use `push_cast`. Put the polynomial expressions in normal form. Simplify using `only [List.ofFn_succ, List.prod_cons]`. Use `⟨_, B * NormedSpace.exp ((-φ 0 x) • E 0), ?_, ?_, ?_, hd.mul' h4, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, ← mul_assoc (NormedSpace.exp _), hinv, one_mul, h1]`. Rewrite using `[hexp]; exact norm_mul_sub_one_le h2 (hn _ (by rw [abs_neg]; exact hφ 0))`. Rewrite using `[hexp, mul_comm (Real.exp _)]`. Conclude with `norm_mul_sub_one_le (hn _ (hφ 0)) h3`. Use `set P := (List.ofFn fun i : Fin m => NormedSpace.exp (φ i.succ x • E i.succ)).prod`.

Establish `h6` using `norm_conj_sub_le h2 h3 (hE 0)`. Establish `hmono : Real.exp (2 * m * s) - 1 ≤ Real.exp (2 * ((m + 1 : ℕ) : ℝ) * s) - 1` using `by gcongr; omega`. Rewrite `h6` using `[← Real.exp_add, show (m : ℝ) * s + m * s = 2 * m * s by ring]`. Establish `key : ∀ w : A, B * NormedSpace.exp ((-φ 0 x) • E 0) * (NormedSpace.exp (φ 0 x • E 0) * w) = B * w`. Introduce `w`.

Rewrite using `[mul_assoc, ← mul_assoc (NormedSpace.exp _), hinv, one_mul]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, op_smul_eq_mul, smul_mul_assoc, mul_add, mul_smul_comm, Fin.sum_univ_succ]`. Rewrite using `[key, mul_assoc (NormedSpace.exp _), key]`. Establish `h7 : ‖φ 0 v • (B * E 0 * P - E 0)‖ ≤ (Real.exp (2 * m * s) - 1) * |φ 0 v|`. Rewrite using `[norm_smul, Real.norm_eq_abs, mul_comm]`.

Use `gcongr`. Establish `h8` using `norm_add_le (B * L v - ∑ i : Fin m, φ i.succ v • E i.succ) (φ 0 v • (B * E 0 * P - E 0))`. Establish `h9` using `mul_le_mul_of_nonneg_right hmono (abs_nonneg (φ 0 v))`. Establish `h10` using `mul_le_mul_of_nonneg_right hmono (Finset.sum_nonneg (s := univ) fun (i : Fin m) _ => abs_nonneg (φ i.succ v))`. Establish `h11` using `h5 v`.

Use `le_trans (le_of_eq ?_) (h8.trans (by linarith))` and prove the remaining obligations. Use `congr 1`. Rewrite using `[smul_sub, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_deriv_prod {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : ℝ} (hs : 0 ≤ s)
    (x : X) (m : ℕ) (E : Fin m → A) (φ : Fin m → X →L[ℝ] ℝ) (hE : ∀ i, ‖E i‖ ≤ 1)
    (hφ : ∀ i, |φ i x| ≤ s) :
    ∃ (L : X →L[ℝ] A) (B : A),
      B * (List.ofFn fun i => NormedSpace.exp (φ i x • E i)).prod = 1 ∧
      ‖B - 1‖ ≤ Real.exp (m * s) - 1 ∧
      ‖(List.ofFn fun i => NormedSpace.exp (φ i x • E i)).prod - 1‖ ≤ Real.exp (m * s) - 1 ∧
      HasStrictFDerivAt (fun y => (List.ofFn fun i => NormedSpace.exp (φ i y • E i)).prod) L x ∧
      ∀ v, ‖B * L v - ∑ i, φ i v • E i‖ ≤ (Real.exp (2 * m * s) - 1) * ∑ i, |φ i v| := by
  induction m with
  | zero => exact ⟨0, 1, by simp, by simp, by simp, by simpa using hasStrictFDerivAt_const _ _, by simp⟩
  | succ m ih =>
    obtain ⟨L, B, h1, h2, h3, h4, h5⟩ := ih (fun i => E i.succ) (fun i => φ i.succ)
      (fun i => hE _) (fun i => hφ _)
    letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
    have hd : HasStrictFDerivAt (fun y => NormedSpace.exp (φ 0 y • E 0))
        ((φ 0).smulRight (NormedSpace.exp (φ 0 x • E 0) * E 0)) x := by
      have := (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (E 0) (φ 0 x)).hasStrictFDerivAt.comp x
        (φ 0).hasStrictFDerivAt
      refine HasStrictFDerivAt.congr_fderiv this ?_
      ext v; simp
    have hn : ∀ u : ℝ, |u| ≤ s → ‖NormedSpace.exp (u • E 0) - 1‖ ≤ Real.exp s - 1 := by
      intro u hu
      refine (norm_exp_sub_one_le _).trans ?_
      gcongr
      rw [norm_smul, Real.norm_eq_abs]
      have := mul_le_mul hu (hE 0) (norm_nonneg _) hs
      linarith
    have hinv : NormedSpace.exp ((-φ 0 x) • E 0) * NormedSpace.exp (φ 0 x • E 0) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (((Commute.refl (E 0)).smul_left _).smul_right _),
        ← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]
    have hexp : Real.exp (((m + 1 : ℕ) : ℝ) * s) = Real.exp (m * s) * Real.exp s := by
      rw [← Real.exp_add]; push_cast; ring_nf
    simp only [List.ofFn_succ, List.prod_cons]
    refine ⟨_, B * NormedSpace.exp ((-φ 0 x) • E 0), ?_, ?_, ?_, hd.mul' h4, fun v => ?_⟩
    · rw [mul_assoc, ← mul_assoc (NormedSpace.exp _), hinv, one_mul, h1]
    · rw [hexp]; exact norm_mul_sub_one_le h2 (hn _ (by rw [abs_neg]; exact hφ 0))
    · rw [hexp, mul_comm (Real.exp _)]; exact norm_mul_sub_one_le (hn _ (hφ 0)) h3
    · set P := (List.ofFn fun i : Fin m => NormedSpace.exp (φ i.succ x • E i.succ)).prod
      have h6 := norm_conj_sub_le h2 h3 (hE 0)
      have hmono : Real.exp (2 * m * s) - 1 ≤ Real.exp (2 * ((m + 1 : ℕ) : ℝ) * s) - 1 := by
        gcongr; omega
      rw [← Real.exp_add, show (m : ℝ) * s + m * s = 2 * m * s by ring] at h6
      have key : ∀ w : A, B * NormedSpace.exp ((-φ 0 x) • E 0) * (NormedSpace.exp (φ 0 x • E 0) * w) = B * w := by
        intro w; rw [mul_assoc, ← mul_assoc (NormedSpace.exp _), hinv, one_mul]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, op_smul_eq_mul, smul_mul_assoc, mul_add,
        mul_smul_comm, Fin.sum_univ_succ]
      rw [key, mul_assoc (NormedSpace.exp _), key]
      have h7 : ‖φ 0 v • (B * E 0 * P - E 0)‖ ≤ (Real.exp (2 * m * s) - 1) * |φ 0 v| := by
        rw [norm_smul, Real.norm_eq_abs, mul_comm]; gcongr
      have h8 := norm_add_le (B * L v - ∑ i : Fin m, φ i.succ v • E i.succ) (φ 0 v • (B * E 0 * P - E 0))
      have h9 := mul_le_mul_of_nonneg_right hmono (abs_nonneg (φ 0 v))
      have h10 := mul_le_mul_of_nonneg_right hmono
        (Finset.sum_nonneg (s := univ) fun (i : Fin m) _ => abs_nonneg (φ i.succ v))
      have h11 := h5 v
      refine le_trans (le_of_eq ?_) (h8.trans (by linarith))
      congr 1
      rw [smul_sub, mul_assoc]; abel

end Algebra

section Mat
open scoped Matrix.Norms.Frobenius
open GlobalTheory.NearUnitaryExp

variable {n : ℕ}

noncomputable def ip : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => ((X * Yᴴ).trace).re)
    (fun X X' Y => by simp [add_mul]) (fun a X Y => by simp)
    (fun X Y Y' => by simp [mul_add]) (fun a X Y => by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ip_apply (X Y : Matrix (Fin n) (Fin n) ℂ) : ip X Y = ((X * Yᴴ).trace).re := rfl

/- English proof (translation)
Rewrite using `[ip_apply, ip_apply, ← Complex.conj_re, ← Complex.star_def, ← Matrix.trace_conjTranspose]`. Simplify using the standard rewrite rules.
-/
theorem ip_symm (X Y : Matrix (Fin n) (Fin n) ℂ) : ip X Y = ip Y X := by
  rw [ip_apply, ip_apply, ← Complex.conj_re, ← Complex.star_def, ← Matrix.trace_conjTranspose]
  simp

/- English proof (translation)
Rewrite using `[norm_sq_eq_hs, hs_eq_re_trace, ip_apply, Matrix.trace_mul_comm]`.
-/
theorem ip_self (X : Matrix (Fin n) (Fin n) ℂ) : ip X X = ‖X‖ ^ 2 := by
  rw [norm_sq_eq_hs, hs_eq_re_trace, ip_apply, Matrix.trace_mul_comm]

noncomputable def coords {N : ℕ} (E : Fin N → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i => ip.flip (E i))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coords_apply {N : ℕ} (E : Fin N → Matrix (Fin n) (Fin n) ℂ) (X) (i : Fin N) :
    coords E X i = ip X (E i) := rfl

/- English proof (translation)
Use extensionality with `j`. Rewrite using `[coords_apply]`. Simplify using `[hE]`.
-/
theorem coords_sum {N : ℕ} {E : Fin N → Matrix (Fin n) (Fin n) ℂ}
    (hE : ∀ i j, ip (E i) (E j) = if i = j then 1 else 0) (v : EuclideanSpace ℝ (Fin N)) :
    coords E (∑ i, v i • E i) = v := by
  ext j
  rw [coords_apply]
  simp [hE]

/- English proof (translation)
Establish `h1 : ‖coords E X‖ ^ 2 = ∑ i, ip X (E i) * ip X (E i)`. Rewrite using `[EuclideanSpace.real_norm_sq_eq]`. Simplify using `[coords_apply, sq]`. Use `set Y := ∑ i, ip X (E i) • E i with hY`. Establish `h2 : ip X Y = ∑ i, ip X (E i) * ip X (E i)` using `by simp [hY]`.

Establish `h3 : ip Y Y = ∑ i, ip X (E i) * ip X (E i)` using `by simp [hY, hE]`. Establish `h4 : ip (X - Y) (X - Y) = ip X X - ip X Y - (ip Y X - ip Y Y)`. Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4` using `[ip_symm Y X, h2, h3, ip_self, ip_self]`.

Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_` and prove the remaining obligations. Use polynomial arithmetic with `[sq_nonneg ‖X - Y‖]`.
-/
theorem norm_coords_le {N : ℕ} {E : Fin N → Matrix (Fin n) (Fin n) ℂ}
    (hE : ∀ i j, ip (E i) (E j) = if i = j then 1 else 0) (X) : ‖coords E X‖ ≤ ‖X‖ := by
  have h1 : ‖coords E X‖ ^ 2 = ∑ i, ip X (E i) * ip X (E i) := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [coords_apply, sq]
  set Y := ∑ i, ip X (E i) • E i with hY
  have h2 : ip X Y = ∑ i, ip X (E i) * ip X (E i) := by simp [hY]
  have h3 : ip Y Y = ∑ i, ip X (E i) * ip X (E i) := by simp [hY, hE]
  have h4 : ip (X - Y) (X - Y) = ip X X - ip X Y - (ip Y X - ip Y Y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [ip_symm Y X, h2, h3, ip_self, ip_self] at h4
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  nlinarith [sq_nonneg ‖X - Y‖]

variable {ε : Fin n → Bool}

/- English proof (translation)
Establish `h : Xᴴ * Jm ε = -(Jm ε * X)` using `eq_neg_of_add_eq_zero_left hX`. Rewrite using `[← neg_mul, ← h, mul_assoc, Jm_mul_self, mul_one]`.
-/
theorem inG_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  rw [← neg_mul, ← h, mul_assoc, Jm_mul_self, mul_one]

/- English proof (translation)
Rewrite using `[← Complex.conj_eq_iff_im, ← Complex.star_def, ← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, inG_conjTranspose hX, inG_conjTranspose hY]`. Simplify using `only [mul_neg, trace_neg, neg_inj]`. Rewrite using `[← mul_assoc, ← mul_assoc, mul_assoc (Y * Jm ε), Matrix.trace_mul_comm]`. Simplify using `only [mul_assoc]`.
-/
theorem trace_im_eq_zero {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    ((X * Yᴴ).trace).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← Complex.star_def, ← Matrix.trace_conjTranspose,
    conjTranspose_mul, conjTranspose_conjTranspose, inG_conjTranspose hX, inG_conjTranspose hY]
  simp only [mul_neg, trace_neg, neg_inj]
  rw [← mul_assoc, ← mul_assoc, mul_assoc (Y * Jm ε), Matrix.trace_mul_comm]
  simp only [mul_assoc]

/- English proof (translation)
Establish `hc : ∀ i j, (E i * (E j)ᴴ).trace = if i = j then 1 else 0`. Introduce `i j`. Apply `Complex.ext` to reduce the goal to its premises. Apply the tactic sequence `rw [← ip_apply, hE]; split_ifs <;> simp`. Apply the tactic sequence `rw [trace_im_eq_zero (hG i) (hG j)]; split_ifs <;> simp`.

Establish `hco : ∀ (a : Fin (n ^ 2) → ℂ) j, ((∑ i, a i • E i) * (E j)ᴴ).trace = a j`. Introduce `a j`. Simplify using `[Finset.sum_mul, hc]`. Establish `hinj : Function.Injective (Fintype.linearCombination ℂ E)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Use function extensionality and compare the values at `j`. Rewrite using `[← hco a j, ← Fintype.linearCombination_apply, ha]`. Simplify using the standard rewrite rules. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_matrix, sq])).1 hinj`.

Take `⟨a, ha⟩` from `hsurj X`. Rewrite `ha` using `[Fintype.linearCombination_apply]`. Establish `: a = 0`. Use function extensionality and compare the values at `j`. Rewrite using `[← hco a j, ha]`.

Conclude with `Complex.ext (h0 j) (trace_im_eq_zero hX (hG j))`. Rewrite using `[← ha, this]`. Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_ip {E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i, inG ε (E i))
    (hE : ∀ i j, ip (E i) (E j) = if i = j then 1 else 0) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (h0 : ∀ i, ip X (E i) = 0) : X = 0 := by
  have hc : ∀ i j, (E i * (E j)ᴴ).trace = if i = j then 1 else 0 := by
    intro i j
    apply Complex.ext
    · rw [← ip_apply, hE]; split_ifs <;> simp
    · rw [trace_im_eq_zero (hG i) (hG j)]; split_ifs <;> simp
  have hco : ∀ (a : Fin (n ^ 2) → ℂ) j, ((∑ i, a i • E i) * (E j)ᴴ).trace = a j := by
    intro a j
    simp [Finset.sum_mul, hc]
  have hinj : Function.Injective (Fintype.linearCombination ℂ E) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    funext j
    rw [← hco a j, ← Fintype.linearCombination_apply, ha]; simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_matrix, sq])).1 hinj
  obtain ⟨a, ha⟩ := hsurj X
  rw [Fintype.linearCombination_apply] at ha
  have : a = 0 := by
    funext j
    rw [← hco a j, ha]
    exact Complex.ext (h0 j) (trace_im_eq_zero hX (hG j))
  rw [← ha, this]; simp

/- English proof (translation)
Use `set J := Jm ε with hJ`. Establish `hJJ : J * J = 1` using `Jm_mul_self ε`. Establish `hJh : Jᴴ = J` using `Jm_conjTranspose ε`. Establish `hJw : ∀ w : Matrix (Fin n) (Fin n) ℂ, J * (J * w) = w` using `fun w => by`. Rewrite using `[← mul_assoc, hJJ, one_mul]`.

Use `⟨1 / (2 * (‖J‖ * ‖J‖ + 1)), by positivity, fun g h hg hh hg1 hh1 hc => ?_⟩` and prove the remaining obligations. Use `set ρ := 1 / (2 * (‖J‖ * ‖J‖ + 1)) with hρ`. Establish `hρ0 : 0 < ρ` using `by positivity`. Establish `hρ1 : ρ * (‖J‖ * ‖J‖ + 1) = 1 / 2` using `by rw [hρ]; field_simp`. Use `set D := g - h with hD`.

Establish `hD0 : ∀ i, ip D (E i) = 0` using `fun i => by`. Rewrite using `[← coords_apply, hD, map_sub, hc, sub_self]`. Both sides reduce to the same expression. Establish `hX : inG ε (D - J * Dᴴ * J)`. Unfold `inG`.

Rewrite using `[← hJ]`. Simplify using `only [conjTranspose_sub, conjTranspose_mul, hJh, conjTranspose_conjTranspose, sub_mul, mul_sub, mul_assoc, hJJ, hJw, mul_one]`. Normalize the expressions using the abelian group laws. Establish `hX0 : D - J * Dᴴ * J = 0`. Use `eq_zero_of_ip hG hE hX fun i => ?_` and prove the remaining obligations.

Establish `: ip (J * Dᴴ * J) (E i) = -ip D (E i)`. Rewrite using `[ip_symm D, ip_apply, ip_apply, inG_conjTranspose (hG i), ← hJ]`. Simplify using `only [mul_neg, trace_neg, Complex.neg_re, mul_assoc, hJw]`. Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [mul_assoc, hJJ, mul_one]`.

Rewrite using `[Matrix.trace_mul_comm]`. Rewrite using `[map_sub, LinearMap.sub_apply, this, hD0]`. Simplify using the standard rewrite rules. Establish `hg' : gᴴ * J * g = J` using `hg`. Establish `hh' : hᴴ * J * h = J` using `hh`.

Establish `h1 : Dᴴ * J * g + hᴴ * J * D = 0`. Rewrite using `[hD, conjTranspose_sub, sub_mul, sub_mul, mul_sub, hg', hh']`. Normalize the expressions using the abelian group laws. Establish `h2 : D + D = -(J * Dᴴ * J * (g - 1) + J * (h - 1)ᴴ * J * D)`. Establish `h3 : J * Dᴴ * J = D` using `(sub_eq_zero.1 hX0).symm`.

Establish `h4` using `congrArg (J * ·) h1`. Simplify using `only [mul_add, mul_zero, ← mul_assoc] at h4`. Rewrite using `[conjTranspose_sub h 1, conjTranspose_one]`. Simplify using `only [mul_sub, sub_mul, mul_one, hJJ, one_mul]`. Rewrite using `[eq_neg_iff_add_eq_zero, ← h4, h3]`.

Normalize the expressions using the abelian group laws. Establish `h5 : ‖J * Dᴴ * J * (g - 1)‖ ≤ ‖J‖ * ‖D‖ * ‖J‖ * ρ`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations.

Use `gcongr`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.frobenius_norm_conjTranspose]`. Establish `h6 : ‖J * (h - 1)ᴴ * J * D‖ ≤ ‖J‖ * ρ * ‖J‖ * ‖D‖`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations.

Use `gcongr`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Use `(norm_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.frobenius_norm_conjTranspose]`.

Use `gcongr`. Establish `h7 : ‖D + D‖ = 2 * ‖D‖` using `by rw [← two_smul ℝ D, norm_smul]; simp`. Establish `h8` using `norm_add_le (J * Dᴴ * J * (g - 1)) (J * (h - 1)ᴴ * J * D)`. Rewrite `h8` using `[← norm_neg, ← h2, h7]`. Establish `h9 : ‖D‖ * (ρ * (‖J‖ * ‖J‖ + 1)) = ‖D‖ * (1 / 2)` using `by rw [hρ1]`.

Establish `h10 : 0 ≤ ‖D‖ * ρ` using `by positivity`. Establish `: ‖D‖ ≤ 0` using `by nlinarith`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 this)`.
-/
theorem exists_inj_near_one {E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i, inG ε (E i))
    (hE : ∀ i j, ip (E i) (E j) = if i = j then 1 else 0) :
    ∃ ρ > 0, ∀ g h : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → inUJ ε h → ‖g - 1‖ ≤ ρ → ‖h - 1‖ ≤ ρ →
      coords E g = coords E h → g = h := by
  set J := Jm ε with hJ
  have hJJ : J * J = 1 := Jm_mul_self ε
  have hJh : Jᴴ = J := Jm_conjTranspose ε
  have hJw : ∀ w : Matrix (Fin n) (Fin n) ℂ, J * (J * w) = w := fun w => by
    rw [← mul_assoc, hJJ, one_mul]
  refine ⟨1 / (2 * (‖J‖ * ‖J‖ + 1)), by positivity, fun g h hg hh hg1 hh1 hc => ?_⟩
  set ρ := 1 / (2 * (‖J‖ * ‖J‖ + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ * (‖J‖ * ‖J‖ + 1) = 1 / 2 := by rw [hρ]; field_simp
  set D := g - h with hD
  have hD0 : ∀ i, ip D (E i) = 0 := fun i => by
    rw [← coords_apply, hD, map_sub, hc, sub_self]; rfl
  have hX : inG ε (D - J * Dᴴ * J) := by
    unfold inG
    rw [← hJ]
    simp only [conjTranspose_sub, conjTranspose_mul, hJh, conjTranspose_conjTranspose, sub_mul,
      mul_sub, mul_assoc, hJJ, hJw, mul_one]
    abel
  have hX0 : D - J * Dᴴ * J = 0 := by
    refine eq_zero_of_ip hG hE hX fun i => ?_
    have : ip (J * Dᴴ * J) (E i) = -ip D (E i) := by
      rw [ip_symm D, ip_apply, ip_apply, inG_conjTranspose (hG i), ← hJ]
      simp only [mul_neg, trace_neg, Complex.neg_re, mul_assoc, hJw]
      rw [Matrix.trace_mul_comm]
      simp only [mul_assoc, hJJ, mul_one]
      rw [Matrix.trace_mul_comm]
    rw [map_sub, LinearMap.sub_apply, this, hD0]; simp
  have hg' : gᴴ * J * g = J := hg
  have hh' : hᴴ * J * h = J := hh
  have h1 : Dᴴ * J * g + hᴴ * J * D = 0 := by
    rw [hD, conjTranspose_sub, sub_mul, sub_mul, mul_sub, hg', hh']; abel
  have h2 : D + D = -(J * Dᴴ * J * (g - 1) + J * (h - 1)ᴴ * J * D) := by
    have h3 : J * Dᴴ * J = D := (sub_eq_zero.1 hX0).symm
    have h4 := congrArg (J * ·) h1
    simp only [mul_add, mul_zero, ← mul_assoc] at h4
    rw [conjTranspose_sub h 1, conjTranspose_one]
    simp only [mul_sub, sub_mul, mul_one, hJJ, one_mul]
    rw [eq_neg_iff_add_eq_zero, ← h4, h3]; abel
  have h5 : ‖J * Dᴴ * J * (g - 1)‖ ≤ ‖J‖ * ‖D‖ * ‖J‖ * ρ := by
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.frobenius_norm_conjTranspose]
  have h6 : ‖J * (h - 1)ᴴ * J * D‖ ≤ ‖J‖ * ρ * ‖J‖ * ‖D‖ := by
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.frobenius_norm_conjTranspose]
    gcongr
  have h7 : ‖D + D‖ = 2 * ‖D‖ := by rw [← two_smul ℝ D, norm_smul]; simp
  have h8 := norm_add_le (J * Dᴴ * J * (g - 1)) (J * (h - 1)ᴴ * J * D)
  rw [← norm_neg, ← h2, h7] at h8
  have h9 : ‖D‖ * (ρ * (‖J‖ * ‖J‖ + 1)) = ‖D‖ * (1 / 2) := by rw [hρ1]
  have h10 : 0 ≤ ‖D‖ * ρ := by positivity
  have : ‖D‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

open Metric Filter Topology in

/- English proof (translation)
Establish `hE1 : ∀ i, ‖E i‖ ≤ 1` using `fun i => by`. Use `hE i i` as an intermediate fact. Rewrite `this` using `[ip_self, if_pos rfl]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this.le`. Take `⟨L, B, h1, -, -, h4, h5⟩` from `exists_deriv_prod hs t (n ^ 2) E (fun i => EuclideanSpace.proj i) hE1 ht`.

Take `⟨ρ, hρ, hinj⟩` from `exists_inj_near_one hG hE`. Establish `h4' : HasStrictFDerivAt (fun y => uMat (Θ y)) L t`. Simplify using `only [hΘ]`. Conclude with `h4`. Establish `h1' : B * uMat (Θ t) = 1` using `by rw [hΘ]; exact h1`.

Establish `hB : B = uMat (Θ t)⁻¹`. Establish `: uMat (Θ t) * uMat (Θ t)⁻¹ = 1` using `by simp [uMat]`. Rewrite using `[← mul_one B, ← this, ← mul_assoc, h1', one_mul]`. Use `set δ : ℝ := n * (Real.exp (2 * n ^ 2 * s) - 1) with hδ`. Establish `he0 : 0 ≤ Real.exp (2 * n ^ 2 * s) - 1` using `sub_nonneg.2 (Real.one_le_exp (by positivity))`.

Establish `hδ0 : 0 ≤ δ` using `by positivity`. Establish `h6` using `h4'.const_mul B`. Establish `h7` using `(coords E).hasStrictFDerivAt.comp t h6`. Take `⟨S, hS, hap⟩` from `h7.approximates_deriv_on_nhds (c := ⟨1 - δ - lam, by linarith⟩) (Or.inr (by change (0 : ℝ) < 1 - δ - lam; exact sub_pos.2 hl))`. Establish `hlin : ∀ v, ‖coords E (B * L v) - v‖ ≤ δ * ‖v‖`.

Introduce `v`. Establish `a1 : coords E (B * L v) - v = coords E (B * L v - ∑ i, v i • E i)`. Rewrite using `[map_sub, coords_sum hE]`. Establish `a2 : ∑ i, |v i| ≤ n * ‖v‖`. Use `(pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations.

Use `sq_sum_le_card_mul_sum_sq.trans ?_` and prove the remaining obligations. Rewrite using `[mul_pow, EuclideanSpace.real_norm_sq_eq]`. Simplify using the standard rewrite rules. Rewrite using `[a1]`. Use `(norm_coords_le hE _).trans ((h5 v).trans ?_)` and prove the remaining obligations.

Rewrite using `[hδ, mul_comm (n : ℝ), mul_assoc _ (n : ℝ)]`. Use `push_cast`. Conclude with `mul_le_mul_of_nonneg_left a2 he0`. Establish `hap' : ApproximatesLinearOn (fun y => coords E (B * uMat (Θ y))) (ContinuousLinearMap.id ℝ _) S ⟨1 - lam, by linarith⟩`. Introduce `x hx y hy`.

Establish `a1` using `hap x hx y hy`. Establish `a2` using `hlin (x - y)`. Establish `a3` using `norm_add_le (coords E (B * uMat (Θ x)) - coords E (B * uMat (Θ y)) - coords E (B * L (x - y))) (coords E (B * L (x - y)) - (x - y))`. Express the relevant statement in the definitionally equal form `‖coords E (B * uMat (Θ x)) - coords E (B * uMat (Θ y)) - coords E (B * L (x - y))‖ ≤ (1 - δ - lam) * ‖x - y‖ at a1`. Express the relevant statement in the definitionally equal form `‖coords E (B * uMat (Θ x)) - coords E (B * uMat (Θ y)) - (x - y)‖ ≤ (1 - lam) * ‖x - y‖`.

Rewrite `a3` using `[sub_add_sub_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `inv : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n ^ 2)))).NonlinearRightInverse` to `⟨id, 1, fun y => by simp, fun y => rfl⟩`. Establish `hS2 : {y | ‖B * uMat (Θ y) - 1‖ ≤ ρ} ∈ 𝓝 t`. Use `h6.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hρ)` as an intermediate fact.

Use `filter_upwards [this] with y hy`. Simplify `hy` using `[h1', dist_eq_norm]`. Establish `e1` using `(eventually_closedBall_subset (inter_mem hS hS2)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))`. Establish `e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam * r ≤ ρ`. Establish `: Tendsto (fun r : ℝ => lam * r) (𝓝 0) (𝓝 (lam * 0))` using `tendsto_const_nhds.mul tendsto_id`.

Rewrite `this` using `[mul_zero]`. Conclude with `(this.eventually (ge_mem_nhds hρ)).filter_mono nhdsWithin_le_nhds`. Use `filter_upwards [e1, e2, self_mem_nhdsWithin] with r hr1 hr2 hr3 g hg`. Establish `hsurj` using `hap'.surjOn_closedBall_of_nonlinearRightInverse inv (le_of_lt hr3) (hr1.trans Set.inter_subset_left)`. Take `⟨y, hy, hyg⟩` from `@hsurj (coords E (uMat g)) (by`.

Rewrite using `[mem_closedBall, dist_eq_norm, h1', ← map_sub]`. Use `(norm_coords_le hE _).trans (hg.trans (le_of_eq ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `lam * r = (((1 : NNReal) : ℝ)⁻¹ - (1 - lam)) * r`. Use the proof step `simp)`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Establish `hm : B * uMat (Θ y) = uMat ((Θ t)⁻¹ * Θ y)` using `by rw [hB]; rfl`. Use `hinj (B * uMat (Θ y)) (uMat g) (by rw [hm]; exact ((Θ t)⁻¹ * Θ y).2) g.2 (hr1 hy).2 (hg.trans hr2) hyg` as an intermediate fact. Rewrite `this` using `[hm]`. Establish `: (Θ t)⁻¹ * Θ y = g` using `Subtype.ext (Units.ext this)`. Rewrite using `[← this, mul_inv_cancel_left]`.
-/
theorem eventually_ball_subset {s lam : ℝ} {E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i, inG ε (E i)) (hE : ∀ i j, ip (E i) (E j) = if i = j then 1 else 0) (hs : 0 ≤ s)
    (Θ : EuclideanSpace ℝ (Fin (n ^ 2)) → UJ ε)
    (hΘ : ∀ y, uMat (Θ y) = (List.ofFn fun i => NormedSpace.exp (y i • E i)).prod)
    (t : EuclideanSpace ℝ (Fin (n ^ 2))) (ht : ∀ i, |t i| ≤ s)
    (hl : lam < 1 - n * (Real.exp (2 * n ^ 2 * s) - 1)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ g : UJ ε, ‖uMat g - 1‖ ≤ lam * r → Θ t * g ∈ Θ '' closedBall t r := by
  have hE1 : ∀ i, ‖E i‖ ≤ 1 := fun i => by
    have := hE i i
    rw [ip_self, if_pos rfl] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this.le
  obtain ⟨L, B, h1, -, -, h4, h5⟩ := exists_deriv_prod hs t (n ^ 2) E
    (fun i => EuclideanSpace.proj i) hE1 ht
  obtain ⟨ρ, hρ, hinj⟩ := exists_inj_near_one hG hE
  have h4' : HasStrictFDerivAt (fun y => uMat (Θ y)) L t := by
    simp only [hΘ]; exact h4
  have h1' : B * uMat (Θ t) = 1 := by rw [hΘ]; exact h1
  have hB : B = uMat (Θ t)⁻¹ := by
    have : uMat (Θ t) * uMat (Θ t)⁻¹ = 1 := by simp [uMat]
    rw [← mul_one B, ← this, ← mul_assoc, h1', one_mul]
  set δ : ℝ := n * (Real.exp (2 * n ^ 2 * s) - 1) with hδ
  have he0 : 0 ≤ Real.exp (2 * n ^ 2 * s) - 1 := sub_nonneg.2 (Real.one_le_exp (by positivity))
  have hδ0 : 0 ≤ δ := by positivity
  have h6 := h4'.const_mul B
  have h7 := (coords E).hasStrictFDerivAt.comp t h6
  obtain ⟨S, hS, hap⟩ := h7.approximates_deriv_on_nhds (c := ⟨1 - δ - lam, by linarith⟩)
    (Or.inr (by change (0 : ℝ) < 1 - δ - lam; exact sub_pos.2 hl))
  have hlin : ∀ v, ‖coords E (B * L v) - v‖ ≤ δ * ‖v‖ := by
    intro v
    have a1 : coords E (B * L v) - v = coords E (B * L v - ∑ i, v i • E i) := by
      rw [map_sub, coords_sum hE]
    have a2 : ∑ i, |v i| ≤ n * ‖v‖ := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      refine sq_sum_le_card_mul_sum_sq.trans ?_
      rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
      simp
    rw [a1]
    refine (norm_coords_le hE _).trans ((h5 v).trans ?_)
    rw [hδ, mul_comm (n : ℝ), mul_assoc _ (n : ℝ)]
    push_cast
    exact mul_le_mul_of_nonneg_left a2 he0
  have hap' : ApproximatesLinearOn (fun y => coords E (B * uMat (Θ y)))
      (ContinuousLinearMap.id ℝ _) S ⟨1 - lam, by linarith⟩ := by
    intro x hx y hy
    have a1 := hap x hx y hy
    have a2 := hlin (x - y)
    have a3 := norm_add_le (coords E (B * uMat (Θ x)) - coords E (B * uMat (Θ y)) - coords E (B * L (x - y)))
      (coords E (B * L (x - y)) - (x - y))
    change ‖coords E (B * uMat (Θ x)) - coords E (B * uMat (Θ y)) - coords E (B * L (x - y))‖ ≤
      (1 - δ - lam) * ‖x - y‖ at a1
    change ‖coords E (B * uMat (Θ x)) - coords E (B * uMat (Θ y)) - (x - y)‖ ≤ (1 - lam) * ‖x - y‖
    rw [sub_add_sub_cancel] at a3
    linarith
  let inv : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n ^ 2)))).NonlinearRightInverse :=
    ⟨id, 1, fun y => by simp, fun y => rfl⟩
  have hS2 : {y | ‖B * uMat (Θ y) - 1‖ ≤ ρ} ∈ 𝓝 t := by
    have := h6.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hρ)
    filter_upwards [this] with y hy
    simpa [h1', dist_eq_norm] using hy
  have e1 := (eventually_closedBall_subset (inter_mem hS hS2)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam * r ≤ ρ := by
    have : Tendsto (fun r : ℝ => lam * r) (𝓝 0) (𝓝 (lam * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact (this.eventually (ge_mem_nhds hρ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [e1, e2, self_mem_nhdsWithin] with r hr1 hr2 hr3 g hg
  have hsurj := hap'.surjOn_closedBall_of_nonlinearRightInverse inv (le_of_lt hr3)
    (hr1.trans Set.inter_subset_left)
  obtain ⟨y, hy, hyg⟩ := @hsurj (coords E (uMat g)) (by
    rw [mem_closedBall, dist_eq_norm, h1', ← map_sub]
    refine (norm_coords_le hE _).trans (hg.trans (le_of_eq ?_))
    change lam * r = (((1 : NNReal) : ℝ)⁻¹ - (1 - lam)) * r
    simp)
  refine ⟨y, hy, ?_⟩
  have hm : B * uMat (Θ y) = uMat ((Θ t)⁻¹ * Θ y) := by rw [hB]; rfl
  have := hinj (B * uMat (Θ y)) (uMat g) (by rw [hm]; exact ((Θ t)⁻¹ * Θ y).2) g.2
    (hr1 hy).2 (hg.trans hr2) hyg
  rw [hm] at this
  have : (Θ t)⁻¹ * Θ y = g := Subtype.ext (Units.ext this)
  rw [← this, mul_inv_cancel_left]

/- English proof (translation)
Rewrite using `[(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]`. Express the relevant statement in the definitionally equal form `Continuous fun y => uMat (Θ y)`. Simplify using `only [hΘ, List.ofFn_eq_map]`. Use `letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := .restrictScalars ℚ ℝ _`. Conclude with `continuous_list_prod _ fun i _ => NormedSpace.exp_continuous.comp (by fun_prop)`.
-/
theorem continuous_chart {N : ℕ} {E : Fin N → Matrix (Fin n) (Fin n) ℂ}
    (Θ : EuclideanSpace ℝ (Fin N) → UJ ε)
    (hΘ : ∀ y, uMat (Θ y) = (List.ofFn fun i => NormedSpace.exp (y i • E i)).prod) :
    Continuous Θ := by
  rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
  change Continuous fun y => uMat (Θ y)
  simp only [hΘ, List.ofFn_eq_map]
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := .restrictScalars ℚ ℝ _
  exact continuous_list_prod _ fun i _ => NormedSpace.exp_continuous.comp (by fun_prop)

end Mat

open Filter Topology in
/- English proof (translation)
Establish `h1 : Tendsto (fun l : ℝ => K * l ^ N) (𝓝[<] (1 - δ)) (𝓝 (K * (1 - δ) ^ N))` using `(by fun_prop : Continuous fun l : ℝ => K * l ^ N).continuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Establish `h2` using `h1.eventually (lt_mem_nhds (ha.trans_le hK))`. Establish `h3 : ∀ᶠ l in 𝓝[<] (1 - δ), 0 < l` using `(lt_mem_nhds (sub_pos.2 hδ)).filter_mono nhdsWithin_le_nhds`. Take `⟨l, a1, a2, a3⟩` from `(h3.and ((eventually_mem_nhdsWithin (a := 1 - δ) (s := Set.Iio (1 - δ))).and h2)).exists`. Conclude with `⟨l, a1, a2, a3⟩`.
-/
theorem exists_ratio {N : ℕ} {δ a K : ℝ} (ha : a < 1) (hK : 1 ≤ K * (1 - δ) ^ N) (hδ : δ < 1) :
    ∃ lam, 0 < lam ∧ lam < 1 - δ ∧ a < K * lam ^ N := by
  have h1 : Tendsto (fun l : ℝ => K * l ^ N) (𝓝[<] (1 - δ)) (𝓝 (K * (1 - δ) ^ N)) :=
    (by fun_prop : Continuous fun l : ℝ => K * l ^ N).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 := h1.eventually (lt_mem_nhds (ha.trans_le hK))
  have h3 : ∀ᶠ l in 𝓝[<] (1 - δ), 0 < l :=
    (lt_mem_nhds (sub_pos.2 hδ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨l, a1, a2, a3⟩ := (h3.and ((eventually_mem_nhdsWithin (a := 1 - δ) (s := Set.Iio (1 - δ))).and h2)).exists
  exact ⟨l, a1, a2, a3⟩

/- English proof (translation)
Rewrite using `[Real.exp_nat_mul, ← mul_pow]`. Use `one_le_pow₀ ?_` and prove the remaining obligations. Use `Real.add_one_le_exp (2 * δ)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_exp_mul_pow {N : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    1 ≤ Real.exp (N * (2 * δ)) * (1 - δ) ^ N := by
  rw [Real.exp_nat_mul, ← mul_pow]
  refine one_le_pow₀ ?_
  have := Real.add_one_le_exp (2 * δ)
  nlinarith

open Metric Filter Topology in
open scoped ENNReal Matrix.Norms.Frobenius in

/- English proof (translation)
Introduce `n ε c s E Θ hc hG hE hs hn hΘ Φ hΦ`. Use `set K := Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) with hK`. Use `set δ : ℝ := n * (Real.exp (2 * n ^ 2 * s) - 1) with hδ`. Establish `he0 : 0 ≤ Real.exp (2 * n ^ 2 * s) - 1` using `sub_nonneg.2 (Real.one_le_exp (by positivity))`. Establish `hδ0 : 0 ≤ δ` using `by positivity`.

Establish `hδ1 : δ ≤ 1 / 2`. Use `le_trans ?_ hn` and prove the remaining obligations. Rewrite using `[hδ]`. Use `gcongr`. Evaluate the numerical expressions.

Establish `hK1 : 1 ≤ K * (1 - δ) ^ (n ^ 2)`. Use `one_le_exp_mul_pow (N := n ^ 2) hδ0 hδ1 using 3` and compare the differences between its conclusion and the goal. Rewrite using `[hδ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Set `Θ' : EuclideanSpace ℝ (Fin (n ^ 2)) → UJ ε` to `fun y => Θ y.ofLp`. Establish `hΘ' : ∀ y, uMat (Θ' y) = (List.ofFn fun i => NormedSpace.exp (y i • E i)).prod`. Introduce `y`. Simplify using `only [Θ', hΘ, Complex.coe_smul]`. Use `set Q := Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s) with hQ`.

Use `set Q₀ := Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Ioo (0 : ℝ) s) with hQ₀`. Establish `hQQ : Q₀ ⊆ Q` using `Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self`. Establish `hQo : IsOpen Q₀` using `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo`. Set `U : Set (EuclideanSpace ℝ (Fin (n ^ 2)))` to `WithLp.ofLp ⁻¹' Q₀`. Establish `hU : IsOpen U` using `hQo.preimage (PiLp.continuous_ofLp 2 _)`.

Establish `hinj : Set.InjOn Θ' U`. Introduce `x hx y hy hxy`. Establish `h1` using `GlobalTheory.ExpChartExpanding.expanding n E s hs.le hE x.ofLp y.ofLp fun i => ⟨hQQ hx i trivial, hQQ hy i trivial⟩`. Rewrite `h1` using `[← hΘ, ← hΘ, show Θ x.ofLp = Θ y.ofLp from hxy, sub_self, NearUnitaryExp.sqrt_hs_eq_norm, norm_zero]`. Establish `h2 : ‖x - y‖ = Real.sqrt (∑ i, (x.ofLp i - y.ofLp i) ^ 2)`.

Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← h2]`. Establish `: ‖x - y‖ ≤ 0` using `by nlinarith [norm_nonneg (x - y)]`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 this)`.

Establish `main` using `lintegral_le_of_balls (muG ε) Θ' U (ENNReal.ofReal (K * c)) ENNReal.ofReal_ne_top hU (continuous_chart Θ' hΘ') hinj ?_ Φ hΦ`. Establish `hae : Q =ᵐ[volume] Q₀` using `Measure.pi_Ioo_ae_eq_pi_Icc.symm`. Establish `hmp` using `(PiLp.volume_preserving_ofLp (Fin (n ^ 2))).setLIntegral_comp_preimage_emb (MeasurableEquiv.toLp 2 (Fin (n ^ 2) → ℝ)).symm.measurableEmbedding (fun t => Φ (Θ t)) Q₀`. Rewrite using `[setLIntegral_congr hae, ← hmp]`. Use `main.trans ?_` and prove the remaining obligations.

Use `gcongr`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x.ofLp, hQQ hx, rfl⟩`. Introduce `t ht a ha`. Establish `ha' : a.toReal < 1`.

Simplify using `using (ENNReal.toReal_lt_toReal ha.ne_top ENNReal.one_ne_top).2 ha`. Take `⟨lam, hl0, hl1, hl2⟩` from `exists_ratio ha' hK1 (by linarith)`. Establish `e1` using `eventually_ball_subset hG hE hs.le Θ' hΘ' t (fun i => by have := ht i trivial; rw [abs_of_pos this.1]; exact this.2.le) hl1`. Use `set ω := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)) with hω`. Establish `hω1 : ω ≠ ⊤` using `measure_ball_lt_top.ne`.

Establish `hω0 : 0 < ω.toReal` using `ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hω1`. Establish `hT : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Tendsto (fun r : ℝ => lam * r) (𝓝 0) (𝓝 (lam * 0))` using `tendsto_const_nhds.mul tendsto_id`. Rewrite `this` using `[mul_zero]`.

Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hl0 hr`. Establish `e2` using `((Tendsto.comp hc hT).const_mul (K * lam ^ (n ^ 2))).eventually (lt_mem_nhds (mul_lt_mul_of_pos_right hl2 hω0))`. Use `filter_upwards [e1, e2, self_mem_nhdsWithin] with r hr1 hr2 hr3`. Establish `hr : 0 < r` using `hr3`.

Use `set T := {g : UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ lam * r} with hT`. Establish `h1 : muG ε T ≤ muG ε (Θ' '' closedBall t r)`. Rewrite using `[← measure_preimage_mul (muG ε) (Θ' t) (Θ' '' closedBall t r)]`. Use `measure_mono fun g hg => hr1 g ?_` and prove the remaining obligations. Rewrite using `[← NearUnitaryExp.sqrt_hs_eq_norm]`.

Conclude with `hg`. Establish `h2 : a.toReal * (r ^ (n ^ 2) * ω.toReal) ≤ K * c * (muG ε T).toReal`. Express the relevant statement in the definitionally equal form `a.toReal * ω.toReal < K * lam ^ (n ^ 2) * (c * (muG ε T).toReal / (lam * r) ^ (n ^ 2)) at hr2`. Establish `h3 : K * lam ^ (n ^ 2) * (c * (muG ε T).toReal / (lam * r) ^ (n ^ 2)) = K * c * (muG ε T).toReal / r ^ (n ^ 2)`. Rewrite using `[mul_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite `hr2` using `[h3, lt_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, ← hω]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal ha.ne_top, ENNReal.ofReal_toReal hω1]`. Use `_ ≤ ENNReal.ofReal (K * c * (muG ε T).toReal) := ENNReal.ofReal_le_ofReal h2`. Use `_ = ENNReal.ofReal (K * c) * ENNReal.ofReal (muG ε T).toReal := ENNReal.ofReal_mul' ENNReal.toReal_nonneg`. Use `_ ≤ _ := by gcongr; exact ENNReal.ofReal_toReal_le.trans h1`.
-/
theorem lintegral_chart_le : ∀ (n : ℕ) (ε : Fin n → Bool) (c s : ℝ) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (Θ : (Fin (n ^ 2) → ℝ) → UJ ε), IsGauge ε c → (∀ i, inG ε (E i)) → (∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) → 0 < s → n * (Real.exp (3 * n ^ 2 * s) - 1) ≤ 1 / 2 → (∀ t, uMat (Θ t) = (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod) → ∀ Φ : UJ ε → ENNReal, Measurable Φ → ∫⁻ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s), Φ (Θ t) ≤ ENNReal.ofReal (Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) * c) * ∫⁻ y in Θ '' Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s), Φ y ∂(muG ε) := by
  intro n ε c s E Θ hc hG hE hs hn hΘ Φ hΦ
  set K := Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) with hK
  set δ : ℝ := n * (Real.exp (2 * n ^ 2 * s) - 1) with hδ
  have he0 : 0 ≤ Real.exp (2 * n ^ 2 * s) - 1 := sub_nonneg.2 (Real.one_le_exp (by positivity))
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    refine le_trans ?_ hn
    rw [hδ]; gcongr; norm_num
  have hK1 : 1 ≤ K * (1 - δ) ^ (n ^ 2) := by
    convert one_le_exp_mul_pow (N := n ^ 2) hδ0 hδ1 using 3
    rw [hδ]; push_cast; ring
  let Θ' : EuclideanSpace ℝ (Fin (n ^ 2)) → UJ ε := fun y => Θ y.ofLp
  have hΘ' : ∀ y, uMat (Θ' y) = (List.ofFn fun i => NormedSpace.exp (y i • E i)).prod := by
    intro y
    simp only [Θ', hΘ, Complex.coe_smul]
  set Q := Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s) with hQ
  set Q₀ := Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Ioo (0 : ℝ) s) with hQ₀
  have hQQ : Q₀ ⊆ Q := Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self
  have hQo : IsOpen Q₀ := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  let U : Set (EuclideanSpace ℝ (Fin (n ^ 2))) := WithLp.ofLp ⁻¹' Q₀
  have hU : IsOpen U := hQo.preimage (PiLp.continuous_ofLp 2 _)
  have hinj : Set.InjOn Θ' U := by
    intro x hx y hy hxy
    have h1 := GlobalTheory.ExpChartExpanding.expanding n E s hs.le hE x.ofLp y.ofLp
      fun i => ⟨hQQ hx i trivial, hQQ hy i trivial⟩
    rw [← hΘ, ← hΘ, show Θ x.ofLp = Θ y.ofLp from hxy, sub_self,
      NearUnitaryExp.sqrt_hs_eq_norm, norm_zero] at h1
    have h2 : ‖x - y‖ = Real.sqrt (∑ i, (x.ofLp i - y.ofLp i) ^ 2) := by
      rw [EuclideanSpace.norm_eq]; simp
    rw [← h2] at h1
    have : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have main := lintegral_le_of_balls (muG ε) Θ' U (ENNReal.ofReal (K * c)) ENNReal.ofReal_ne_top hU
    (continuous_chart Θ' hΘ') hinj ?_ Φ hΦ
  · have hae : Q =ᵐ[volume] Q₀ := Measure.pi_Ioo_ae_eq_pi_Icc.symm
    have hmp := (PiLp.volume_preserving_ofLp (Fin (n ^ 2))).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin (n ^ 2) → ℝ)).symm.measurableEmbedding (fun t => Φ (Θ t)) Q₀
    rw [setLIntegral_congr hae, ← hmp]
    refine main.trans ?_
    gcongr
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.ofLp, hQQ hx, rfl⟩
  intro t ht a ha
  have ha' : a.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal ha.ne_top ENNReal.one_ne_top).2 ha
  obtain ⟨lam, hl0, hl1, hl2⟩ := exists_ratio ha' hK1 (by linarith)
  have e1 := eventually_ball_subset hG hE hs.le Θ' hΘ' t
    (fun i => by have := ht i trivial; rw [abs_of_pos this.1]; exact this.2.le) hl1
  set ω := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)) with hω
  have hω1 : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hω0 : 0 < ω.toReal := ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hω1
  have hT : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun r : ℝ => lam * r) (𝓝 0) (𝓝 (lam * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hl0 hr
  have e2 := ((Tendsto.comp hc hT).const_mul (K * lam ^ (n ^ 2))).eventually
    (lt_mem_nhds (mul_lt_mul_of_pos_right hl2 hω0))
  filter_upwards [e1, e2, self_mem_nhdsWithin] with r hr1 hr2 hr3
  have hr : 0 < r := hr3
  set T := {g : UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ lam * r} with hT
  have h1 : muG ε T ≤ muG ε (Θ' '' closedBall t r) := by
    rw [← measure_preimage_mul (muG ε) (Θ' t) (Θ' '' closedBall t r)]
    refine measure_mono fun g hg => hr1 g ?_
    rw [← NearUnitaryExp.sqrt_hs_eq_norm]; exact hg
  have h2 : a.toReal * (r ^ (n ^ 2) * ω.toReal) ≤ K * c * (muG ε T).toReal := by
    change a.toReal * ω.toReal < K * lam ^ (n ^ 2) * (c * (muG ε T).toReal / (lam * r) ^ (n ^ 2)) at hr2
    have h3 : K * lam ^ (n ^ 2) * (c * (muG ε T).toReal / (lam * r) ^ (n ^ 2)) =
        K * c * (muG ε T).toReal / r ^ (n ^ 2) := by
      rw [mul_pow]; field_simp
    rw [h3, lt_div_iff₀ (by positivity)] at hr2
    linarith
  rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, ← hω]
  calc a * (ENNReal.ofReal (r ^ (n ^ 2)) * ω)
      = ENNReal.ofReal (a.toReal * (r ^ (n ^ 2) * ω.toReal)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal ha.ne_top, ENNReal.ofReal_toReal hω1]
    _ ≤ ENNReal.ofReal (K * c * (muG ε T).toReal) := ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (K * c) * ENNReal.ofReal (muG ε T).toReal :=
        ENNReal.ofReal_mul' ENNReal.toReal_nonneg
    _ ≤ _ := by gcongr; exact ENNReal.ofReal_toReal_le.trans h1

end ProductChart

end GlobalTheory
