import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Filter Topology

namespace GlobalTheory.CompanionTheory.SDPadic

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

/- English proof (translation)
Establish `ha' : ∀ w y y', B w (y + y') = B w y * B w y'` using `fun w y y' => by rw [hs, ha, hs y, hs y']`. Use `set χ : V → ℂ := (N : Set V).indicator (fun _ => 1) with hχ`. Establish `hχc : Continuous χ` using `(IsClopen.continuous_indicator ⟨hNc.isClosed, hNo⟩ continuous_const)`. Establish `h1 : ∀ y, (N : Set V).indicator (fun y => (∫ x, f x * B x y ∂μ) * B y z) y = ∫ x, f x * (χ y * B (x + z) y) ∂μ`. Introduce `y`.

Distinguish the cases in `hy : y ∈ N`. Rewrite using `[Set.indicator_of_mem (by exact hy)]`. Simplify using `only [hχ, ← integral_mul_const]`. Use `congr 1`. Use extensionality with `x`.

Rewrite using `[Set.indicator_of_mem (by exact hy), ha, hs y]; ring`. Simplify using `[hχ, hy]`. Establish `h2 : ∀ x, ∫ y, f x * (χ y * B (x + z) y) ∂μ = (M : Set V).indicator (fun u => (μ.real N : ℂ) * f (u - z)) (x + z)`. Introduce `x`. Distinguish the cases in `hx : x + z ∈ M`.

Rewrite using `[Set.indicator_of_mem (by exact hx), integral_const_mul]`. Establish `e1 : (fun y => χ y * B (x + z) y) = χ`. Use extensionality with `y`. Distinguish the cases in `hy : y ∈ N`. Rewrite using `[(hM _).1 hx y hy, mul_one]`.

Simplify using `[hχ, hy]`. Rewrite using `[e1, hχ, integral_indicator_const _ hNo.measurableSet]`. Simplify using `[mul_comm]`. Rewrite using `[Set.indicator_of_notMem (by exact hx)]`. Establish `hx'` using `hx`.

Rewrite `hx'` using `[hM]`. Use `push Not at hx'`. Take `⟨n, hn, hn1⟩` from `hx'`. Use `GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ n _ hn1 fun y => ?_` and prove the remaining obligations. Establish `: χ (y + n) = χ y`.

Distinguish the cases in `hy : y ∈ N`. Simplify using `[hχ, hy, N.add_mem hy hn]`. Establish `: y + n ∉ N` using `fun h => hy (by simpa using N.sub_mem h hn)`. Simplify using `[hχ, hy, this]`. Rewrite using `[this, ha']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsw : ∫ y, ∫ x, f x * (χ y * B (x + z) y) ∂μ ∂μ = ∫ x, ∫ y, f x * (χ y * B (x + z) y) ∂μ ∂μ`. Use `integral_integral_swap (Continuous.integrable_of_hasCompactSupport ?_ ?_)` and prove the remaining obligations. Establish `: Continuous fun p : V × V => B (p.2 + z) p.1` using `hB.comp (f := fun p : V × V => (p.2 + z, p.1)) (by fun_prop)`. Conclude with `(hf.comp continuous_snd).mul ((hχc.comp continuous_fst).mul this)`.

Use `HasCompactSupport.intro (hNc.prod hfc) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, x⟩ h`. Simplify using `only [Set.mem_prod, not_and_or] at h`. Break down `h with h | h` into its components or cases. Simplify using `[Function.uncurry, hχ, Set.indicator_of_notMem h]`.

Simplify using `[Function.uncurry, image_eq_zero_of_notMem_tsupport h]`. Rewrite using `[← integral_indicator hNo.measurableSet, ← integral_indicator hMo.measurableSet]`. Repeatedly rewrite using `[h1]`. Rewrite using `[hsw]`. Repeatedly rewrite using `[h2]`.

Conclude with `integral_add_right_eq_self (μ := μ) ((M : Set V).indicator (fun u => (μ.real N : ℂ) * f (u - z))) z`.
-/
theorem trunc (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (z : V) :
    ∫ y in (N : Set V), (∫ x, f x * B x y ∂μ) * B y z ∂μ
      = ∫ u in (M : Set V), (μ.real N : ℂ) * f (u - z) ∂μ := by
  classical
  have ha' : ∀ w y y', B w (y + y') = B w y * B w y' := fun w y y' => by rw [hs, ha, hs y, hs y']
  set χ : V → ℂ := (N : Set V).indicator (fun _ => 1) with hχ
  have hχc : Continuous χ := (IsClopen.continuous_indicator ⟨hNc.isClosed, hNo⟩ continuous_const)
  have h1 : ∀ y, (N : Set V).indicator (fun y => (∫ x, f x * B x y ∂μ) * B y z) y
      = ∫ x, f x * (χ y * B (x + z) y) ∂μ := by
    intro y
    by_cases hy : y ∈ N
    · rw [Set.indicator_of_mem (by exact hy)]
      simp only [hχ, ← integral_mul_const]
      congr 1; ext x
      rw [Set.indicator_of_mem (by exact hy), ha, hs y]; ring
    · simp [hχ, hy]
  have h2 : ∀ x, ∫ y, f x * (χ y * B (x + z) y) ∂μ =
      (M : Set V).indicator (fun u => (μ.real N : ℂ) * f (u - z)) (x + z) := by
    intro x
    by_cases hx : x + z ∈ M
    · rw [Set.indicator_of_mem (by exact hx), integral_const_mul]
      have e1 : (fun y => χ y * B (x + z) y) = χ := by
        ext y
        by_cases hy : y ∈ N
        · rw [(hM _).1 hx y hy, mul_one]
        · simp [hχ, hy]
      rw [e1, hχ, integral_indicator_const _ hNo.measurableSet]
      simp [mul_comm]
    · rw [Set.indicator_of_notMem (by exact hx)]
      have hx' := hx
      rw [hM] at hx'
      push Not at hx'
      obtain ⟨n, hn, hn1⟩ := hx'
      refine GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ n _ hn1 fun y => ?_
      have : χ (y + n) = χ y := by
        by_cases hy : y ∈ N
        · simp [hχ, hy, N.add_mem hy hn]
        · have : y + n ∉ N := fun h => hy (by simpa using N.sub_mem h hn)
          simp [hχ, hy, this]
      rw [this, ha']; ring
  have hsw : ∫ y, ∫ x, f x * (χ y * B (x + z) y) ∂μ ∂μ = ∫ x, ∫ y, f x * (χ y * B (x + z) y) ∂μ ∂μ := by
    refine integral_integral_swap (Continuous.integrable_of_hasCompactSupport ?_ ?_)
    · have : Continuous fun p : V × V => B (p.2 + z) p.1 :=
        hB.comp (f := fun p : V × V => (p.2 + z, p.1)) (by fun_prop)
      exact (hf.comp continuous_snd).mul ((hχc.comp continuous_fst).mul this)
    · refine HasCompactSupport.intro (hNc.prod hfc) ?_
      rintro ⟨y, x⟩ h
      simp only [Set.mem_prod, not_and_or] at h
      rcases h with h | h
      · simp [Function.uncurry, hχ, Set.indicator_of_notMem h]
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h]
  rw [← integral_indicator hNo.measurableSet, ← integral_indicator hMo.measurableSet]
  simp_rw [h1]
  rw [hsw]
  simp_rw [h2]
  exact integral_add_right_eq_self (μ := μ) ((M : Set V).indicator (fun u => (μ.real N : ℂ) * f (u - z))) z

end GlobalTheory.CompanionTheory.SDPadic

/- English proof (translation)
Introduce `V _ _ _ _ _ _ _ _ χ L D ha hs hn hB hLD hanti hsm _ hDall hD hL`. Take `⟨μ, hμ, hinv⟩` from `GlobalTheory.JR.AbsInv.exists_selfDual χ hB hs ha (fun U hU => by`. Take `⟨n, hn⟩` from `hsm U hU`. Conclude with `⟨L n, D n, hn, (hLD n).1, (hLD n).2.1, (hLD n).2.2.1, (hLD n).2.2.2, hD n, hL n⟩)`. Establish `hone : ∀ n, μ.real (L n) * μ.real (D n) = 1`.

Introduce `n`. Use `set f : V → ℂ := (L n : Set V).indicator (fun _ => 1) with hf`. Establish `hcl : IsClopen (L n : Set V)` using `⟨(hLD n).2.1.isClosed, (hLD n).1⟩`. Establish `hfc : Continuous f` using `hcl.continuous_indicator continuous_const`. Establish `hfs : HasCompactSupport f` using `HasCompactSupport.intro (hLD n).2.1 fun x hx => by simp [hf, Set.indicator_of_notMem hx]`.

Establish `hfi : ∀ x, ∀ m ∈ L n, f (x + m) = f x`. Introduce `x m hm`. Distinguish the cases in `hx : x ∈ L n`. Simplify using `[hf, hx, (L n).add_mem hx hm]`. Establish `: x + m ∉ L n` using `fun h => hx (by simpa using (L n).sub_mem h hm)`.

Simplify using `[hf, hx, this]`. Establish `hfl : IsLocallyConstant f`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `: (fun y => y - x) ⁻¹' (L n : Set V) ∈ 𝓝 x` using `((hLD n).1.preimage (by fun_prop)).mem_nhds (by simp)`.

Use `filter_upwards [this] with y hy`. Use `hfi x _ hy` as an intermediate fact. Simplify using `using this`. Establish `e1` using `GlobalTheory.JR.AbsInv.fourB_fourB μ χ hB hs ha (L n) (D n) (hLD n).1 (hLD n).2.2.1 (hLD n).2.2.2 (hD n) (hL n) f hfc hfs hfi 0`. Rewrite `e1` using `[hinv f ⟨hfl, hfs⟩ 0]`.

Establish `e3 : f (-0) = 1` using `by simp [hf]`. Rewrite `e1` using `[e3, mul_one]`. Conclude with `e1.symm` after adjusting the coercions. Use `⟨μ, hμ, fun Φ hΦ hΦc hint z => ?_⟩` and prove the remaining obligations. Establish `hmono : Monotone (fun n => (D n : Set V))`.

Introduce `m n hmn y hy`. Conclude with `(hD n y).2 fun x hx => (hD m y).1 hy x (hanti hmn hx)`. Establish `hU : (⋃ n, (D n : Set V)) = Set.univ`. Use extensionality with `x`. Simplify using `using hDall x`.

Establish `hg : Integrable (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y z) μ`. Use `hint.mul_bdd (c := 1) ?_ (Eventually.of_forall fun y => (hn y z).le)` and prove the remaining obligations. Conclude with `(hB.comp (f := fun y : V => (y, z)) (by fun_prop)).aestronglyMeasurable`. Establish `t1` using `tendsto_setIntegral_of_monotone (μ := μ) (fun n => (hLD n).2.2.1.measurableSet) hmono (f := fun y => (∫ x, Φ x * χ x y ∂μ) * χ y z) (by rw [hU]; exact hg.integrableOn)`. Rewrite `t1` using `[hU, Measure.restrict_univ]`.

Use `tendsto_nhds_unique t1 ?_` and prove the remaining obligations. Rewrite using `[Metric.tendsto_atTop]`. Introduce `ε hε`. Establish `hc : Continuous fun u : V => Φ (u - z)` using `hΦ.comp (by fun_prop)`. Establish `hnh : {u : V | ‖Φ (u - z) - Φ (-z)‖ < ε / 2} ∈ 𝓝 (0 : V)` using `(isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hε)`.

Take `⟨n0, hn0⟩` from `hsm _ hnh`. Use `⟨n0, fun n hnn => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.SDPadic.trunc μ χ hB hs ha (L n) (D n) (hLD n).1 (hLD n).2.2.1 (hLD n).2.2.2 (hL n) Φ hΦ hΦc z, dist_eq_norm]`. Establish `hfin : μ (L n) < ⊤` using `(hLD n).2.1.measure_lt_top`. Establish `e : ∫ u in (L n : Set V), (μ.real (D n) : ℂ) * Φ (u - z) ∂μ - Φ (-z) = ∫ u in (L n : Set V), (μ.real (D n) : ℂ) * (Φ (u - z) - Φ (-z)) ∂μ`.

Repeatedly rewrite using `[mul_sub]`. Rewrite using `[integral_sub ((by fun_prop : Continuous fun u : V => (μ.real (D n) : ℂ) * Φ (u - z)).continuousOn.integrableOn_compact (hLD n).2.1) (continuous_const.continuousOn.integrableOn_compact (hLD n).2.1), setIntegral_const, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hone n]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Establish `hb` using `norm_setIntegral_le_of_norm_le_const (μ := μ) (s := (L n : Set V)) (C := μ.real (D n) * (ε / 2)) (f := fun u => (μ.real (D n) : ℂ) * (Φ (u - z) - Φ (-z))) hfin (fun u hu => by`.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]`. Conclude with `mul_le_mul_of_nonneg_left (le_of_lt (hn0 (hanti hnn hu))) measureReal_nonneg)`. Use `lt_of_le_of_lt hb ?_` and prove the remaining obligations. Use `hone n` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.CompanionTheory.SDPadic.exists_selfDual : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (L : ℤ → AddSubgroup V) (D : ℤ → AddSubgroup V), (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → Continuous (fun p : V × V => χ p.1 p.2) → (∀ n, IsOpen (L n : Set V) ∧ IsCompact (L n : Set V) ∧ IsOpen (D n : Set V) ∧ IsCompact (D n : Set V)) → Antitone L → (∀ U ∈ nhds (0 : V), ∃ n, (L n : Set V) ⊆ U) → (∀ x, ∃ n, x ∈ L n) → (∀ x, ∃ n, x ∈ D n) → (∀ n y, y ∈ D n ↔ ∀ x ∈ L n, χ x y = 1) → (∀ n x, x ∈ L n ↔ ∀ y ∈ D n, χ x y = 1) → ∃ μ : Measure V, SelfDual μ χ := by
  intro V _ _ _ _ _ _ _ _ χ L D ha hs hn hB hLD hanti hsm _ hDall hD hL
  classical
  obtain ⟨μ, hμ, hinv⟩ := GlobalTheory.JR.AbsInv.exists_selfDual χ hB hs ha (fun U hU => by
    obtain ⟨n, hn⟩ := hsm U hU
    exact ⟨L n, D n, hn, (hLD n).1, (hLD n).2.1, (hLD n).2.2.1, (hLD n).2.2.2, hD n, hL n⟩)
  have hone : ∀ n, μ.real (L n) * μ.real (D n) = 1 := by
    intro n
    set f : V → ℂ := (L n : Set V).indicator (fun _ => 1) with hf
    have hcl : IsClopen (L n : Set V) := ⟨(hLD n).2.1.isClosed, (hLD n).1⟩
    have hfc : Continuous f := hcl.continuous_indicator continuous_const
    have hfs : HasCompactSupport f :=
      HasCompactSupport.intro (hLD n).2.1 fun x hx => by simp [hf, Set.indicator_of_notMem hx]
    have hfi : ∀ x, ∀ m ∈ L n, f (x + m) = f x := by
      intro x m hm
      by_cases hx : x ∈ L n
      · simp [hf, hx, (L n).add_mem hx hm]
      · have : x + m ∉ L n := fun h => hx (by simpa using (L n).sub_mem h hm)
        simp [hf, hx, this]
    have hfl : IsLocallyConstant f := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have : (fun y => y - x) ⁻¹' (L n : Set V) ∈ 𝓝 x :=
        ((hLD n).1.preimage (by fun_prop)).mem_nhds (by simp)
      filter_upwards [this] with y hy
      have := hfi x _ hy
      simpa using this
    have e1 := GlobalTheory.JR.AbsInv.fourB_fourB μ χ hB hs ha (L n) (D n) (hLD n).1 (hLD n).2.2.1 (hLD n).2.2.2
      (hD n) (hL n) f hfc hfs hfi 0
    rw [hinv f ⟨hfl, hfs⟩ 0] at e1
    have e3 : f (-0) = 1 := by simp [hf]
    rw [e3, mul_one] at e1
    exact_mod_cast e1.symm
  refine ⟨μ, hμ, fun Φ hΦ hΦc hint z => ?_⟩
  have hmono : Monotone (fun n => (D n : Set V)) := by
    intro m n hmn y hy
    exact (hD n y).2 fun x hx => (hD m y).1 hy x (hanti hmn hx)
  have hU : (⋃ n, (D n : Set V)) = Set.univ := by
    ext x; simpa using hDall x
  have hg : Integrable (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y z) μ := by
    refine hint.mul_bdd (c := 1) ?_ (Eventually.of_forall fun y => (hn y z).le)
    exact (hB.comp (f := fun y : V => (y, z)) (by fun_prop)).aestronglyMeasurable
  have t1 := tendsto_setIntegral_of_monotone (μ := μ) (fun n => (hLD n).2.2.1.measurableSet) hmono
    (f := fun y => (∫ x, Φ x * χ x y ∂μ) * χ y z) (by rw [hU]; exact hg.integrableOn)
  rw [hU, Measure.restrict_univ] at t1
  refine tendsto_nhds_unique t1 ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : Continuous fun u : V => Φ (u - z) := hΦ.comp (by fun_prop)
  have hnh : {u : V | ‖Φ (u - z) - Φ (-z)‖ < ε / 2} ∈ 𝓝 (0 : V) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hε)
  obtain ⟨n0, hn0⟩ := hsm _ hnh
  refine ⟨n0, fun n hnn => ?_⟩
  rw [GlobalTheory.CompanionTheory.SDPadic.trunc μ χ hB hs ha (L n) (D n) (hLD n).1 (hLD n).2.2.1 (hLD n).2.2.2 (hL n) Φ hΦ hΦc z,
    dist_eq_norm]
  have hfin : μ (L n) < ⊤ := (hLD n).2.1.measure_lt_top
  have e : ∫ u in (L n : Set V), (μ.real (D n) : ℂ) * Φ (u - z) ∂μ - Φ (-z)
      = ∫ u in (L n : Set V), (μ.real (D n) : ℂ) * (Φ (u - z) - Φ (-z)) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub ((by fun_prop : Continuous fun u : V => (μ.real (D n) : ℂ) * Φ (u - z)).continuousOn.integrableOn_compact
        (hLD n).2.1)
      (continuous_const.continuousOn.integrableOn_compact (hLD n).2.1), setIntegral_const,
      Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hone n]
    simp
  rw [e]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := (L n : Set V)) (C := μ.real (D n) * (ε / 2))
    (f := fun u => (μ.real (D n) : ℂ) * (Φ (u - z) - Φ (-z))) hfin (fun u hu => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
      exact mul_le_mul_of_nonneg_left (le_of_lt (hn0 (hanti hnn hu))) measureReal_nonneg)
  refine lt_of_le_of_lt hb ?_
  have := hone n
  calc μ.real (D n) * (ε / 2) * μ.real (L n) = (μ.real (L n) * μ.real (D n)) * (ε / 2) := by ring
    _ < ε := by rw [this]; linarith
