import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import GroundTheory.LocalFields.LocalFourier
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocInv

open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Rewrite using `[measureReal_valBall _ (addCharConductor ψ - k), measureReal_valBall _ k, selfDualMeasure_real_valBall_zero]`. Establish `hq : (0 : ℝ) < residueCard K`. Conclude with `zero_lt_one.trans one_lt_residueCard` after adjusting the coercions. Establish `h` using `(inversion_const_eq_one_iff (K := K) (addCharConductor ψ) (Real.rpow_nonneg hq.le ((addCharConductor ψ : ℝ) / 2))).mpr rfl`. Establish `e : (residueCard K : ℝ) ^ (-(addCharConductor ψ - k)) * (residueCard K : ℝ) ^ (-k) = (residueCard K : ℝ) ^ (-addCharConductor ψ)`.

Rewrite using `[← zpow_add₀ hq.ne']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h, ← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem measureReal_dual_mul (ψ : AddChar K Circle) (k : ℤ) :
    (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) *
      (selfDualMeasure ψ).real (valBall K k) = 1 := by
  rw [measureReal_valBall _ (addCharConductor ψ - k), measureReal_valBall _ k,
    selfDualMeasure_real_valBall_zero]
  have hq : (0 : ℝ) < residueCard K := by
    exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have h := (inversion_const_eq_one_iff (K := K) (addCharConductor ψ)
    (Real.rpow_nonneg hq.le ((addCharConductor ψ : ℝ) / 2))).mpr rfl
  have e : (residueCard K : ℝ) ^ (-(addCharConductor ψ - k)) * (residueCard K : ℝ) ^ (-k) =
      (residueCard K : ℝ) ^ (-addCharConductor ψ) := by
    rw [← zpow_add₀ hq.ne']
    congr 1
    ring
  rw [← h, ← e]
  ring

/- English proof (translation)
Rewrite using `[Metric.tendsto_atTop]`. Introduce `ε hε`. Establish `hcont : ContinuousAt (fun h : K => Φ (h - z)) 0` using `(hΦ.comp (continuous_id.sub continuous_const)).continuousAt`. Establish `hnh : {h : K | dist (Φ (h - z)) (Φ (-z)) < ε / 2} ∈ 𝓝 (0 : K)`. Use `hcont.preimage_mem_nhds (Metric.ball_mem_nhds (Φ (0 - z)) (half_pos hε))` as an intermediate fact.

Simplify `this` using `[Metric.ball, zero_sub]`. Take `⟨m, -, hm⟩` from `hasBasis_nhds_zero_valBall.mem_iff.mp hnh`. Use `⟨m.toNat, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hkm : m ≤ (k : ℤ)` using `by omega`. Establish `hsub : (valBall K (k : ℤ) : Set K) ⊆ valBall K m` using `valBall_antitone hkm`.

Establish `hmul` using `measureReal_dual_mul ψ (k : ℤ)`. Use `set c : ℝ := (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) with hcdef`. Use `set v : ℝ := (selfDualMeasure ψ).real (valBall K (k : ℤ)) with hvdef`. Establish `hc0 : 0 ≤ c` using `measureReal_nonneg`. Establish `hfin : (selfDualMeasure ψ) (valBall K (k : ℤ) : Set K) < ∞` using `(isCompact_valBall _).measure_lt_top`.

Establish `hint : IntegrableOn (fun x => Φ (x - z)) (valBall K (k : ℤ)) (selfDualMeasure ψ)` using `(hΦ.comp (continuous_id.sub continuous_const)).continuousOn.integrableOn_compact (isCompact_valBall _)`. Establish `hintc : IntegrableOn (fun _ : K => Φ (-z)) (valBall K (k : ℤ)) (selfDualMeasure ψ)` using `integrableOn_const hfin.ne`. Establish `hdiff : (c : ℂ) * (∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) - Φ (-z) = (c : ℂ) * ∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)`. Rewrite using `[integral_sub hint hintc, setIntegral_const, Complex.real_smul, mul_sub, ← mul_assoc, ← hvdef]`. Establish `: (c : ℂ) * (v : ℂ) = 1` using `by exact_mod_cast hmul`.

Rewrite using `[this, one_mul]`. Establish `hbound : ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖ ≤ ε / 2 * v`. Use `norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_` and prove the remaining obligations. Use `hm (hsub hx)` as an intermediate fact. Rewrite `this` using `[Set.mem_setOf_eq, dist_eq_norm]`.

Conclude with `this.le`. Rewrite using `[dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show c * (ε / 2 * v) = ε / 2 * (c * v) by ring, hmul, mul_one]`. Use `_ < ε := half_lt_self hε`.
-/
theorem tendsto_mean (ψ : AddChar K Circle) {Φ : K → ℂ} (hΦ : Continuous Φ) (z : K) :
    Tendsto (fun k : ℕ =>
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) : ℝ) : ℂ) *
        ∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) atTop (𝓝 (Φ (-z))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcont : ContinuousAt (fun h : K => Φ (h - z)) 0 :=
    (hΦ.comp (continuous_id.sub continuous_const)).continuousAt
  have hnh : {h : K | dist (Φ (h - z)) (Φ (-z)) < ε / 2} ∈ 𝓝 (0 : K) := by
    have := hcont.preimage_mem_nhds (Metric.ball_mem_nhds (Φ (0 - z)) (half_pos hε))
    simpa [Metric.ball, zero_sub] using this
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hnh
  refine ⟨m.toNat, fun k hk => ?_⟩
  have hkm : m ≤ (k : ℤ) := by omega
  have hsub : (valBall K (k : ℤ) : Set K) ⊆ valBall K m := valBall_antitone hkm
  have hmul := measureReal_dual_mul ψ (k : ℤ)
  set c : ℝ := (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) with hcdef
  set v : ℝ := (selfDualMeasure ψ).real (valBall K (k : ℤ)) with hvdef
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hfin : (selfDualMeasure ψ) (valBall K (k : ℤ) : Set K) < ∞ :=
    (isCompact_valBall _).measure_lt_top
  have hint : IntegrableOn (fun x => Φ (x - z)) (valBall K (k : ℤ)) (selfDualMeasure ψ) :=
    (hΦ.comp (continuous_id.sub continuous_const)).continuousOn.integrableOn_compact
      (isCompact_valBall _)
  have hintc : IntegrableOn (fun _ : K => Φ (-z)) (valBall K (k : ℤ)) (selfDualMeasure ψ) :=
    integrableOn_const hfin.ne
  have hdiff : (c : ℂ) * (∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) - Φ (-z) =
      (c : ℂ) * ∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ) := by
    rw [integral_sub hint hintc, setIntegral_const, Complex.real_smul, mul_sub, ← mul_assoc,
      ← hvdef]
    have : (c : ℂ) * (v : ℂ) = 1 := by exact_mod_cast hmul
    rw [this, one_mul]
  have hbound : ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖ ≤
      ε / 2 * v := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    have := hm (hsub hx)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
  calc c * ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖
      ≤ c * (ε / 2 * v) := mul_le_mul_of_nonneg_left hbound hc0
    _ = ε / 2 := by
        rw [show c * (ε / 2 * v) = ε / 2 * (c * v) by ring, hmul, mul_one]
    _ < ε := half_lt_self hε

/- English proof (translation)
Use `set μ := selfDualMeasure ψ with hμ`. Establish `hfi : Integrable Φ μ` using `hΦ.integrable_of_hasCompactSupport hc`. Establish `hψc : Continuous fun x => (ψ x : ℂ)` using `continuous_subtype_val.comp hψ`. Establish `: IsFiniteMeasure (μ.restrict (valBall K (addCharConductor ψ - k)))` using `isFiniteMeasure_restrict.mpr (isCompact_valBall _).measure_lt_top.ne`. Set `G : K → K → ℂ` to `fun y x => Φ x * (ψ (x * y) : ℂ) * (ψ (y * z) : ℂ)`.

Establish `hG : Integrable (Function.uncurry G) ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ)`. Establish `hdom : Integrable (fun p : K × K => (1 : ℝ) * ‖Φ p.2‖) ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ)` using `(integrable_const (1 : ℝ)).mul_prod hfi.norm`. Use `hdom.mono' ?_ (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `((hΦ.comp continuous_snd).mul (hψc.comp (continuous_snd.mul continuous_fst))).mul (hψc.comp (continuous_fst.mul continuous_const))`.

Simplify using `[G, Function.uncurry, Circle.norm_coe]`. Establish `hB : ∫ y in valBall K (addCharConductor ψ - k), (∫ x, Φ x * (ψ (x * y) : ℂ) ∂μ) * (ψ (y * z) : ℂ) ∂μ = ∫ y in valBall K (addCharConductor ψ - k), ∫ x, G y x ∂μ ∂μ`. Use `congr 1`. Use extensionality with `y`. Conclude with `(integral_mul_const _ _).symm`.

Establish `hinner : ∀ x, ∫ y in valBall K (addCharConductor ψ - k), G y x ∂μ = (valBall K k : Set K).indicator (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z)`. Introduce `x`. Establish `e : ∀ y, G y x = Φ x * ((ψ.mulShift (x + z)) y : ℂ)` using `fun y => by`. Simplify using `only [G, AddChar.mulShift_apply]`. Rewrite using `[mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]`.

Use `congr 3`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Rewrite using `[integral_const_mul, integral_valBall_char]`. Distinguish the cases in `hxz : x + z ∈ valBall K k`.

Establish `ht : IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k)`. Rewrite using `[isTrivialOn_mulShift_iff_mem hψ hψ1]`. Simplify using `using hxz`. Rewrite using `[if_pos ht, Set.indicator_of_mem (show x + z ∈ (valBall K k : Set K) from hxz), add_sub_cancel_right, mul_comm]`. Establish `ht : ¬ IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k)`.

Rewrite using `[isTrivialOn_mulShift_iff_mem hψ hψ1]`. Simplify using `using hxz`. Rewrite using `[if_neg ht, Set.indicator_of_notMem (show x + z ∉ (valBall K k : Set K) from hxz), mul_zero]`. Rewrite using `[hB, integral_integral_swap hG]`. Simplify using `only [hinner]`.

Establish `hpre : ∫ x, (valBall K k : Set K).indicator (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) ∂μ = ∫ x, (valBall K k : Set K).indicator (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x ∂μ` using `integral_add_right_eq_self (fun x => (valBall K k : Set K).indicator (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x) z`. Rewrite using `[hpre, integral_indicator (measurableSet_valBall k), integral_const_mul]`.
-/
theorem setIntegral_fourier_mul_char {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) (z : K) (k : ℤ) :
    ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ) ∂(selfDualMeasure ψ) =
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) *
        ∫ x in valBall K k, Φ (x - z) ∂(selfDualMeasure ψ) := by
  set μ := selfDualMeasure ψ with hμ
  have hfi : Integrable Φ μ := hΦ.integrable_of_hasCompactSupport hc
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have : IsFiniteMeasure (μ.restrict (valBall K (addCharConductor ψ - k))) :=
    isFiniteMeasure_restrict.mpr (isCompact_valBall _).measure_lt_top.ne
  let G : K → K → ℂ := fun y x => Φ x * (ψ (x * y) : ℂ) * (ψ (y * z) : ℂ)
  have hG : Integrable (Function.uncurry G)
      ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ) := by
    have hdom : Integrable (fun p : K × K => (1 : ℝ) * ‖Φ p.2‖)
        ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod hfi.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hΦ.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul continuous_fst))).mul
        (hψc.comp (continuous_fst.mul continuous_const))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have hB : ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂μ) * (ψ (y * z) : ℂ) ∂μ =
      ∫ y in valBall K (addCharConductor ψ - k), ∫ x, G y x ∂μ ∂μ := by
    congr 1
    ext y
    exact (integral_mul_const _ _).symm
  have hinner : ∀ x, ∫ y in valBall K (addCharConductor ψ - k), G y x ∂μ =
      (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) := by
    intro x
    have e : ∀ y, G y x = Φ x * ((ψ.mulShift (x + z)) y : ℂ) := fun y => by
      simp only [G, AddChar.mulShift_apply]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3
      ring
    simp only [e]
    rw [integral_const_mul, integral_valBall_char]
    by_cases hxz : x + z ∈ valBall K k
    · have ht : IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_pos ht, Set.indicator_of_mem (show x + z ∈ (valBall K k : Set K) from hxz),
        add_sub_cancel_right, mul_comm]
    · have ht : ¬ IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_neg ht, Set.indicator_of_notMem (show x + z ∉ (valBall K k : Set K) from hxz),
        mul_zero]
  rw [hB, integral_integral_swap hG]
  simp only [hinner]
  have hpre : ∫ x, (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) ∂μ =
      ∫ x, (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x ∂μ :=
    integral_add_right_eq_self (fun x => (valBall K k : Set K).indicator
      (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x) z
  rw [hpre, integral_indicator (measurableSet_valBall k), integral_const_mul]

/- English proof (translation)
Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `exists_mem_valBall_neg_nat x`. Use `Set.mem_iUnion.mpr ⟨(n + m).toNat, ?_⟩` and prove the remaining obligations. Conclude with `valBall_antitone (by omega) hm`.
-/
theorem iUnion_valBall_sub (n : ℤ) : ⋃ k : ℕ, (valBall K (n - (k : ℤ)) : Set K) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨m, hm⟩ := exists_mem_valBall_neg_nat x
  refine Set.mem_iUnion.mpr ⟨(n + m).toNat, ?_⟩
  exact valBall_antitone (by omega) hm

/- English proof (translation)
Establish `hψc : Continuous fun x => (ψ x : ℂ)` using `continuous_subtype_val.comp hψ`. Establish `hF : Integrable (fun y => (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ)) (selfDualMeasure ψ)`. Use `hI.norm.mono' (hI.aestronglyMeasurable.mul (hψc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[Circle.norm_coe]`. Establish `hmono : Monotone fun k : ℕ => (valBall K (addCharConductor ψ - (k : ℤ)) : Set K)` using `fun a b hab => valBall_antitone (by omega)`.

Establish `hlim` using `tendsto_setIntegral_of_monotone (μ := selfDualMeasure ψ) (fun k : ℕ => measurableSet_valBall (K := K) (addCharConductor ψ - (k : ℤ))) hmono hF.integrableOn`. Rewrite `hlim` using `[iUnion_valBall_sub, setIntegral_univ]`. Use `tendsto_nhds_unique hlim ?_` and prove the remaining obligations. Use `(tendsto_mean ψ hΦ z).congr fun k => ?_` and prove the remaining obligations. Conclude with `(setIntegral_fourier_mul_char hψ hψ1 hΦ hc z (k : ℤ)).symm`.
-/
theorem inversion {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ))
      (selfDualMeasure ψ)) (z : K) :
    ∫ y, (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ)
      ∂(selfDualMeasure ψ) = Φ (-z) := by
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hF : Integrable (fun y => (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) *
      (ψ (y * z) : ℂ)) (selfDualMeasure ψ) := by
    refine hI.norm.mono' (hI.aestronglyMeasurable.mul
      (hψc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    simp [Circle.norm_coe]
  have hmono : Monotone fun k : ℕ => (valBall K (addCharConductor ψ - (k : ℤ)) : Set K) :=
    fun a b hab => valBall_antitone (by omega)
  have hlim := tendsto_setIntegral_of_monotone (μ := selfDualMeasure ψ)
    (fun k : ℕ => measurableSet_valBall (K := K) (addCharConductor ψ - (k : ℤ))) hmono
    hF.integrableOn
  rw [iUnion_valBall_sub, setIntegral_univ] at hlim
  refine tendsto_nhds_unique hlim ?_
  refine (tendsto_mean ψ hΦ z).congr fun k => ?_
  exact (setIntegral_fourier_mul_char hψ hψ1 hΦ hc z (k : ℤ)).symm

end GlobalTheory.CompanionTheory.SW.LocInv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

/- English proof (translation)
Introduce `K _ _ _ _ _ _ ψ hψ hψ1`. Conclude with `⟨inferInstance, fun Φ hΦ hc hI z => GlobalTheory.CompanionTheory.SW.LocInv.inversion hψ hψ1 hΦ hc hI z⟩`.
-/
theorem GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (ψ : AddChar K Circle), Continuous ψ → ψ ≠ 1 → SelfDual (GroundTheory.LocalField.selfDualMeasure ψ) (fun s t => ((ψ (s * t) : Circle) : ℂ)) := by
  intro K _ _ _ _ _ _ ψ hψ hψ1
  exact ⟨inferInstance, fun Φ hΦ hc hI z => GlobalTheory.CompanionTheory.SW.LocInv.inversion hψ hψ1 hΦ hc hI z⟩
