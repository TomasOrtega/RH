import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Break down `le_or_gt 0 (t - a - 2) with h | h` into its components or cases. Use `Nat.ceil_lt_add_one h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Nat.ceil_eq_zero.mpr h.le]`.

Simplify using `only [CharP.cast_eq_zero, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Nat.le_ceil (t - a - 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma shell_mem (a t : ℝ) (ht : a + 1 < t) :
    a + 1 + (⌈t - a - 2⌉₊ : ℝ) < t ∧ t ≤ a + 2 + (⌈t - a - 2⌉₊ : ℝ) := by
  constructor
  · rcases le_or_gt 0 (t - a - 2) with h | h
    · have := Nat.ceil_lt_add_one h
      linarith
    · rw [Nat.ceil_eq_zero.mpr h.le]
      simp only [CharP.cast_eq_zero, add_zero]
      linarith
  · have := Nat.le_ceil (t - a - 2)
    linarith

/- English proof (translation)
Rewrite using `[← ENNReal.ofReal_mul (Real.exp_pos _).le]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]`. Establish `h1 : 0 < 1 + C` using `by linarith`. Establish `h2` using `Real.exp_pos (-(k : ℝ))`.

Establish `h3 : (1 + C)⁻¹ * C ≤ 1`. Rewrite using `[inv_mul_le_iff₀ h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 0 ≤ (1 + C)⁻¹` using `inv_nonneg.mpr h1.le`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h3 h2.le]`.
-/
lemma shell_coef (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(Real.log (1 + C) + k))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]
  have h1 : 0 < 1 + C := by linarith
  have h2 := Real.exp_pos (-(k : ℝ))
  have h3 : (1 + C)⁻¹ * C ≤ 1 := by
    rw [inv_mul_le_iff₀ h1]
    linarith
  have h4 : 0 ≤ (1 + C)⁻¹ := inv_nonneg.mpr h1.le
  nlinarith [mul_le_mul_of_nonneg_left h3 h2.le]

/- English proof (translation)
Establish `hKm : MeasurableSet K` using `hK.isClosed.measurableSet`. Unfold `vol`. Use `split_ifs with h`. Rewrite using `[Measure.ofMeasurable_apply K hKm]`. Unfold `volFun`.

Establish `hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e` using `fun x => (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hz) x (Set.mem_univ x)`. Use `choose e he hze using hz'`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source) (fun x _ => Set.mem_iUnion.mpr ⟨x, he x⟩)`. Establish `hbound : ∀ y : V n, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y`. Introduce `y`.

Distinguish the cases in `hy : y ∈ z '' K`. Rewrite using `[Set.indicator_of_mem hy]`. Establish `hidx : ∀ p ∈ K ∩ z ⁻¹' {y}, ∃ i ∈ t, p ∈ (e i).source`. Introduce `p hp`. Use `ht hp.1` as an intermediate fact.

Simplify using `only [Set.mem_iUnion] at this`. Take `⟨i, hi, hpi⟩` from `this`. Conclude with `⟨i, hi, hpi⟩`. Use `choose! f hf1 hf2 using hidx`. Establish `h1 : (K ∩ z ⁻¹' {y}).encard ≤ ((t : Set M)).encard`.

Use `Set.encard_le_encard_of_injOn (fun p hp => hf1 p hp) ?_` and prove the remaining obligations. Introduce `p hp q hq hpq`. Establish `hp'` using `hf2 p hp`. Establish `hq'` using `hf2 q hq`. Rewrite `hp'` using `[hpq]`.

Apply `(e (f q)).injOn hp' hq'` to reduce the goal to its premises. Establish `h3` using `congrFun (hze (f q))`. Rewrite using `[← h3 p, ← h3 q, Set.mem_singleton_iff.mp hp.2, Set.mem_singleton_iff.mp hq.2]`. Rewrite `h1` using `[Set.encard_coe_eq_coe_finsetCard]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Set.indicator_of_notMem hy]`. Establish `: K ∩ z ⁻¹' {y} = ∅`. Use extensionality with `p`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hp hzp`.

Conclude with `hy ⟨p, hp, hzp⟩`. Rewrite using `[this, Set.encard_empty]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using the standard rewrite rules.
-/
private lemma vol_lt_infty_of_compact {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) {K : Set M} (hK : IsCompact K) :
    vol n z K < ⊤ := by
  classical
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold vol
  split_ifs with h
  · rw [Measure.ofMeasurable_apply K hKm]
    unfold volFun
    have hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e :=
      fun x => (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hz) x (Set.mem_univ x)
    choose e he hze using hz'
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, he x⟩)
    have hbound : ∀ y : V n, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤
        (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ z '' K
      · rw [Set.indicator_of_mem hy]
        have hidx : ∀ p ∈ K ∩ z ⁻¹' {y}, ∃ i ∈ t, p ∈ (e i).source := by
          intro p hp
          have := ht hp.1
          simp only [Set.mem_iUnion] at this
          obtain ⟨i, hi, hpi⟩ := this
          exact ⟨i, hi, hpi⟩
        choose! f hf1 hf2 using hidx
        have h1 : (K ∩ z ⁻¹' {y}).encard ≤ ((t : Set M)).encard := by
          refine Set.encard_le_encard_of_injOn (fun p hp => hf1 p hp) ?_
          intro p hp q hq hpq
          have hp' := hf2 p hp
          have hq' := hf2 q hq
          rw [hpq] at hp'
          apply (e (f q)).injOn hp' hq'
          have h3 := congrFun (hze (f q))
          rw [← h3 p, ← h3 q, Set.mem_singleton_iff.mp hp.2, Set.mem_singleton_iff.mp hq.2]
        rw [Set.encard_coe_eq_coe_finsetCard] at h1
        calc ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ((t.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr h1
          _ = t.card := by simp
      · rw [Set.indicator_of_notMem hy]
        have : K ∩ z ⁻¹' {y} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hp hzp
          exact hy ⟨p, hp, hzp⟩
        rw [this, Set.encard_empty]
        simp
    calc ∫⁻ y, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ∫⁻ y, (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y :=
          lintegral_mono hbound
      _ = t.card * volume (z '' K) :=
          lintegral_indicator_const (hK.image hz.continuous).isClosed.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (hK.image hz.continuous).measure_lt_top
  · simp

/- English proof (translation)
Introduce `z hz e ph ψ v a he hK hph hψ hv`. Use `set g : M → ℝ := fun x => ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) with hg`. Establish `hgc : Continuous g`. Simplify using `only [hg]`. Use `fun_prop`.

Establish `hgm : Measurable fun x => ENNReal.ofReal (g x)` using `ENNReal.measurable_ofReal.comp hgc.measurable`. Establish `hfin : ∀ b : ℝ, ∫⁻ x in {x | e x ≤ b}, ENNReal.ofReal (g x) ∂vol n z < ⊤`. Introduce `b`. Conclude with `setLIntegral_lt_top_of_isCompact (vol_lt_infty_of_compact z hz (hK b)).ne (hK b) (f := fun x => (g x).toNNReal) (continuous_real_toNNReal.comp hgc)`. Use `set C : ℕ → ℝ := fun k => (∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z).toReal with hC`.

Establish `hC0 : ∀ k : ℕ, 0 ≤ C k` using `fun k => ENNReal.toReal_nonneg`. Establish `hCeq : ∀ k : ℕ, ∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z = ENNReal.ofReal (C k)` using `fun k => (ENNReal.ofReal_toReal (hfin _).ne).symm`. Use `set R : ℝ → ℝ := fun t => if a + 1 < t then Real.log (1 + C ⌈t - a - 2⌉₊) + ⌈t - a - 2⌉₊ else 0 with hR`. Establish `hterm0 : ∀ k : ℕ, 0 ≤ Real.log (1 + C k) + k` using `fun k => add_nonneg (Real.log_nonneg (by linarith [hC0 k])) (Nat.cast_nonneg k)`. Use `⟨R, ?_, ?_⟩` and prove the remaining obligations.

Introduce `b`. Use `⟨∑ k ∈ Finset.range (⌈b - a - 2⌉₊ + 1), (Real.log (1 + C k) + k), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Simplify using `only [Set.mem_Iic] at ht`. Simplify using `only [hR]`.

Use `split_ifs with h`. Conclude with `Finset.single_le_sum (f := fun k : ℕ => Real.log (1 + C k) + k) (fun k _ => hterm0 k) (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (by linarith))))`. Conclude with `Finset.sum_nonneg fun k _ => hterm0 k`. Introduce `χ hχ0 hχR`. Unfold `nV`.

Use `set S : ℕ → Set M := fun k => {x | a + 1 + k < e x ∧ e x ≤ a + 2 + k} with hS`. Establish `hSm : ∀ k, MeasurableSet (S k)` using `fun k => (measurableSet_lt measurable_const he.measurable).inter (measurableSet_le he.measurable measurable_const)`. Establish `hLm : MeasurableSet {x | e x ≤ a + 1}` using `measurableSet_le he.measurable measurable_const`. Establish `hpt : ∀ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ≤ {x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x + ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ENNReal.ofReal (g x)) x`. Introduce `x`.

Distinguish the cases in `hx : e x ≤ a + 1`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x | e x ≤ a + 1} from hx)]`. Use `le_trans ?_ le_self_add` and prove the remaining obligations. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Simplify using `only [hg]`.

Use `gcongr`. Combine the linear relations using `[hχ0 (e x)]`. Use `push_neg at hx`. Establish `hxS : x ∈ S ⌈e x - a - 2⌉₊` using `shell_mem a (e x) hx`. Use `le_trans ?_ (le_add_left (ENNReal.le_tsum ⌈e x - a - 2⌉₊))` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem hxS, ← ENNReal.ofReal_mul (Real.exp_pos _).le]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hRx : Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊ ≤ χ (e x)`. Use `hχR (e x) hx.le` as an intermediate fact. Simplify using `only [hR, if_pos hx] at this`.

Conclude with `this`. Simplify using `only [hg]`. Rewrite using `[show -(ph x + χ (e x) - ψ x) = -(χ (e x)) + (-ph x + ψ x) by ring, Real.exp_add]`. Establish `h1 : Real.exp (-(χ (e x))) ≤ Real.exp (-(Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊))` using `Real.exp_le_exp.mpr (by linarith)`. Establish `h2 : 0 ≤ ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x)` using `by positivity`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1 h2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_add_left (hgm.indicator hLm), lintegral_indicator hLm, lintegral_tsum (fun k => ((hgm.const_mul _).indicator (hSm k)).aemeasurable)]`. Use `congr 1`. Use `tsum_congr fun k => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_indicator (hSm k), lintegral_const_mul _ hgm]`. Use `_ ≤ ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z + ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) := by`. Use `add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hCeq k]`.

Conclude with `lintegral_mono_set (fun x hx => hx.2)`. Use `_ ≤ _ := shell_coef (C k) (hC0 k) k`. Use `_ < ⊤ := by`. Use `ENNReal.add_lt_top.mpr ⟨hfin (a + 1), ?_⟩` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) Real.summable_exp_neg_nat]`.

Conclude with `ENNReal.ofReal_lt_top`.
-/
theorem shell (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ShellStatement n M := by
  classical
  intro z hz e ph ψ v a he hK hph hψ hv
  set g : M → ℝ := fun x => ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hgc.measurable
  have hfin : ∀ b : ℝ, ∫⁻ x in {x | e x ≤ b}, ENNReal.ofReal (g x) ∂vol n z < ⊤ := by
    intro b
    exact setLIntegral_lt_top_of_isCompact (vol_lt_infty_of_compact z hz (hK b)).ne (hK b)
      (f := fun x => (g x).toNNReal) (continuous_real_toNNReal.comp hgc)
  set C : ℕ → ℝ := fun k => (∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z).toReal with hC
  have hC0 : ∀ k : ℕ, 0 ≤ C k := fun k => ENNReal.toReal_nonneg
  have hCeq : ∀ k : ℕ, ∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z = ENNReal.ofReal (C k) :=
    fun k => (ENNReal.ofReal_toReal (hfin _).ne).symm
  set R : ℝ → ℝ := fun t => if a + 1 < t then Real.log (1 + C ⌈t - a - 2⌉₊) + ⌈t - a - 2⌉₊ else 0 with hR
  have hterm0 : ∀ k : ℕ, 0 ≤ Real.log (1 + C k) + k :=
    fun k => add_nonneg (Real.log_nonneg (by linarith [hC0 k])) (Nat.cast_nonneg k)
  refine ⟨R, ?_, ?_⟩
  · intro b
    refine ⟨∑ k ∈ Finset.range (⌈b - a - 2⌉₊ + 1), (Real.log (1 + C k) + k), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_Iic] at ht
    simp only [hR]
    split_ifs with h
    · exact Finset.single_le_sum (f := fun k : ℕ => Real.log (1 + C k) + k) (fun k _ => hterm0 k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (by linarith))))
    · exact Finset.sum_nonneg fun k _ => hterm0 k
  · intro χ hχ0 hχR
    unfold nV
    set S : ℕ → Set M := fun k => {x | a + 1 + k < e x ∧ e x ≤ a + 2 + k} with hS
    have hSm : ∀ k, MeasurableSet (S k) := fun k =>
      (measurableSet_lt measurable_const he.measurable).inter (measurableSet_le he.measurable measurable_const)
    have hLm : MeasurableSet {x | e x ≤ a + 1} := measurableSet_le he.measurable measurable_const
    have hpt : ∀ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ≤
        {x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
        ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
          ENNReal.ofReal (g x)) x := by
      intro x
      by_cases hx : e x ≤ a + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | e x ≤ a + 1} from hx)]
        refine le_trans ?_ le_self_add
        apply ENNReal.ofReal_le_ofReal
        simp only [hg]
        gcongr
        linarith [hχ0 (e x)]
      · push_neg at hx
        have hxS : x ∈ S ⌈e x - a - 2⌉₊ := shell_mem a (e x) hx
        refine le_trans ?_ (le_add_left (ENNReal.le_tsum ⌈e x - a - 2⌉₊))
        rw [Set.indicator_of_mem hxS, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have hRx : Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊ ≤ χ (e x) := by
          have := hχR (e x) hx.le
          simp only [hR, if_pos hx] at this
          exact this
        simp only [hg]
        rw [show -(ph x + χ (e x) - ψ x) = -(χ (e x)) + (-ph x + ψ x) by ring, Real.exp_add]
        have h1 : Real.exp (-(χ (e x))) ≤ Real.exp (-(Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 ≤ ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    calc ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ∂vol n z
        ≤ ∫⁻ x, ({x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
          ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ENNReal.ofReal (g x)) x) ∂vol n z := lintegral_mono hpt
      _ = ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k, ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z := by
        rw [lintegral_add_left (hgm.indicator hLm), lintegral_indicator hLm,
          lintegral_tsum (fun k => ((hgm.const_mul _).indicator (hSm k)).aemeasurable)]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator (hSm k), lintegral_const_mul _ hgm]
      _ ≤ ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        calc ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z
            ≤ ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ENNReal.ofReal (C k) := by
              gcongr
              rw [← hCeq k]
              exact lintegral_mono_set (fun x hx => hx.2)
          _ ≤ _ := shell_coef (C k) (hC0 k) k
      _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨hfin (a + 1), ?_⟩
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) Real.summable_exp_neg_nat]
        exact ENNReal.ofReal_lt_top

end

end ReciprocityTheory.L2DbarEstimates.F
