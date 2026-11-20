import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MemSatSqIffConstantCoeffAndLinearCoeffEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

/- English proof (translation)
Set `ι : O →+* FractionRing O` to `algebraMap O (FractionRing O)`. Establish `hinj : Function.Injective ι` using `IsFractionRing.injective O (FractionRing O)`. Set `V : Submodule (FractionRing O) (σ → FractionRing O)` to `Submodule.span (FractionRing O) (Set.range fun k => fun i => ι (v k i))`. Establish `hmem : (fun i => ι (w i)) ∈ V`. Assume the negation of the conclusion as `hw'`.

Take `⟨f, hfw, hfV⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hw' inferInstance`. Set `e : σ → FractionRing O` to `fun i => if p i then f (fun j => if i = j then 1 else 0) else 0`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ e`. Use `choose d hd using fun i => hb i (Finset.mem_univ i)`. Establish `hd0 : d = 0`.

Apply `h d` to reduce the goal to its premises. Introduce `i hi`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hd i, map_zero]`. Simplify using `[e, hi]`.

Introduce `k`. Apply `hinj` to reduce the goal to its premises. Establish `hvk : f (fun i => ι (v k i)) = 0`. Establish `h1 : (fun i => ι (v k i)) ∈ V` using `Submodule.subset_span ⟨k, rfl⟩`. Establish `h2` using `Submodule.mem_map_of_mem (f := f) h1`.

Rewrite `h2` using `[hfV]`. Conclude with `(Submodule.mem_bot _).mp h2`. Rewrite `hvk` using `[LinearMap.pi_apply_eq_sum_univ]`. Rewrite using `[map_zero, map_sum]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hd i, mul_smul_comm]`. Use `_ = (b : O) • ∑ i, ι (v k i) • f (fun j => if i = j then 1 else 0) := by`. Rewrite using `[← Finset.smul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : p i`. Simplify using `[e, hi, smul_eq_mul]`. Simplify using `[e, hi, hv k i hi]`. Use `_ = 0 := by rw [hvk, smul_zero]`.

Establish `he : ∀ i, e i = 0`. Introduce `i`. Establish `h1 : (b : O) • e i = 0`. Rewrite using `[← hd i, hd0]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[Algebra.smul_def]`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. It suffices to derive a contradiction. Conclude with `nonZeroDivisors.coe_ne_zero b (hinj (by rw [map_zero]; exact h2))`. Conclude with `h2`.

Apply `hfw` to reduce the goal to its premises. Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : p i`. Establish `h3` using `he i`.

Simplify using `only [e, hi, if_true] at h3`. Rewrite using `[h3, smul_zero]`. Rewrite using `[hw i hi, map_zero, zero_smul]`. Rewrite `hmem` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hmem`.

Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ c`. Use `choose a ha using fun k => hb k (Finset.mem_univ k)`. Use `⟨b, nonZeroDivisors.coe_ne_zero b, a, fun i => hinj ?_⟩` and prove the remaining obligations. Establish `hi` using `congrFun hc i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi`.

Rewrite using `[map_mul, map_sum, ← hi, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ha k, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem span_of_ann {O : Type} [CommRing O] [IsDomain O] {σ : Type} [Fintype σ] (p : σ → Prop)
    {κ : Type} [Fintype κ] (v : κ → σ → O) (hv : ∀ k i, ¬ p i → v k i = 0)
    (h : ∀ d : σ → O, (∀ i, ¬ p i → d i = 0) → (∀ k, ∑ i, v k i * d i = 0) → d = 0)
    (w : σ → O) (hw : ∀ i, ¬ p i → w i = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ a : κ → O, ∀ i, c * w i = ∑ k, a k * v k i := by
  classical
  let ι : O →+* FractionRing O := algebraMap O (FractionRing O)
  have hinj : Function.Injective ι := IsFractionRing.injective O (FractionRing O)
  let V : Submodule (FractionRing O) (σ → FractionRing O) :=
    Submodule.span (FractionRing O) (Set.range fun k => fun i => ι (v k i))
  have hmem : (fun i => ι (w i)) ∈ V := by
    by_contra hw'
    obtain ⟨f, hfw, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw' inferInstance
    let e : σ → FractionRing O := fun i => if p i then f (fun j => if i = j then 1 else 0) else 0
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ e
    choose d hd using fun i => hb i (Finset.mem_univ i)
    have hd0 : d = 0 := by
      apply h d
      · intro i hi
        apply hinj
        rw [hd i, map_zero]
        simp [e, hi]
      · intro k
        apply hinj
        have hvk : f (fun i => ι (v k i)) = 0 := by
          have h1 : (fun i => ι (v k i)) ∈ V := Submodule.subset_span ⟨k, rfl⟩
          have h2 := Submodule.mem_map_of_mem (f := f) h1
          rw [hfV] at h2
          exact (Submodule.mem_bot _).mp h2
        rw [LinearMap.pi_apply_eq_sum_univ] at hvk
        rw [map_zero, map_sum]
        calc ∑ i, ι (v k i * d i) = ∑ i, (b : O) • (ι (v k i) * e i) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_mul, hd i, mul_smul_comm]
          _ = (b : O) • ∑ i, ι (v k i) • f (fun j => if i = j then 1 else 0) := by
              rw [← Finset.smul_sum]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hi : p i
              · simp [e, hi, smul_eq_mul]
              · simp [e, hi, hv k i hi]
          _ = 0 := by rw [hvk, smul_zero]
    have he : ∀ i, e i = 0 := by
      intro i
      have h1 : (b : O) • e i = 0 := by
        rw [← hd i, hd0]
        simp
      rw [Algebra.smul_def] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exfalso
        exact nonZeroDivisors.coe_ne_zero b (hinj (by rw [map_zero]; exact h2))
      · exact h2
    apply hfw
    rw [LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : p i
    · have h3 := he i
      simp only [e, hi, if_true] at h3
      rw [h3, smul_zero]
    · rw [hw i hi, map_zero, zero_smul]
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ c
  choose a ha using fun k => hb k (Finset.mem_univ k)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, a, fun i => hinj ?_⟩
  have hi := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [map_mul, map_sum, ← hi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ha k, Algebra.smul_def]
  ring

/- English proof (translation)
Apply the tactic sequence `rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp`.
-/
private theorem weight_single_one {σ : Type} (wt : σ → ℤ) (i : σ) :
    Finsupp.weight wt (Finsupp.single i 1) = wt i := by
  rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp

/- English proof (translation)
Introduce `O _ _ σ _ wt j κ _ F hF hx hd`. Use `haveI := Fintype.ofFinite κ`. Establish `hco : ∀ f ∈ Fgr O wt j, ∀ i, ¬ (wt i = j) → coeff (Finsupp.single i 1) (ser f) = 0`. Introduce `f hf i hi`. Rewrite `hf` using `[mem_Fgr]`.

Conclude with `hf (Finsupp.single i 1) (by rw [weight_single_one]; exact hi)`. Unfold `SpansCot`. Introduce `q hq`. Unfold `cotLat at hq`. Take `⟨g, ⟨hgj, hg0⟩, rfl⟩` from `Submodule.mem_map.mp hq`.

Establish `hg0' : x0 O wt g = 0` using `hg0`. Take `⟨c, hc, a, ha⟩` from `span_of_ann (fun i => wt i = j) (fun k i => coeff (Finsupp.single i 1) (ser (F k))) (fun k i hi => hco _ (hF k) i hi) hd (fun i => coeff (Finsupp.single i 1) (ser g)) (fun i hi => hco _ hgj i hi)`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Establish `hsat : c • g - ∑ k, a k • F k ∈ satSq (x0 O wt)`. Rewrite using `[mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← weightedSeriesOrigin_apply]`. Simplify using `[map_sub, map_sum, map_smul, hg0', hx]`. Introduce `i`. Establish `hser : ser (c • g - ∑ k, a k • F k) = c • ser g - ∑ k, a k • ser (F k)`.

Simplify using `[ser]`. Rewrite using `[hser, map_sub, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Conclude with `sub_eq_zero.mpr (ha i)`. Establish `heq : (satSq (x0 O wt)).mkQ (c • g) = (satSq (x0 O wt)).mkQ (∑ k, a k • F k)`.

Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `hsat`. Unfold `cotSpan`. Rewrite using `[← map_smul, heq, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem UpperTheory.spansCot_of_linear_terms_nondegenerate :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ) (j : ℤ) (κ : Type) [Finite κ] (F : κ → FA O wt),
        (∀ k, F k ∈ Fgr O wt j) → (∀ k, x0 O wt (F k) = 0) →
        (∀ d : σ → O, (∀ i, wt i ≠ j → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (F k)) * d i = 0) → d = 0) →
        SpansCot (x0 O wt) (Fgr O wt) j F := by
  intro O _ _ σ _ wt j κ _ F hF hx hd
  classical
  haveI := Fintype.ofFinite κ
  have hco : ∀ f ∈ Fgr O wt j, ∀ i, ¬ (wt i = j) → coeff (Finsupp.single i 1) (ser f) = 0 := by
    intro f hf i hi
    rw [mem_Fgr] at hf
    exact hf (Finsupp.single i 1) (by rw [weight_single_one]; exact hi)
  unfold SpansCot
  intro q hq
  unfold cotLat at hq
  obtain ⟨g, ⟨hgj, hg0⟩, rfl⟩ := Submodule.mem_map.mp hq
  have hg0' : x0 O wt g = 0 := hg0
  obtain ⟨c, hc, a, ha⟩ := span_of_ann (fun i => wt i = j)
    (fun k i => coeff (Finsupp.single i 1) (ser (F k))) (fun k i hi => hco _ (hF k) i hi) hd
    (fun i => coeff (Finsupp.single i 1) (ser g)) (fun i hi => hco _ hgj i hi)
  refine ⟨c, hc, ?_⟩
  have hsat : c • g - ∑ k, a k • F k ∈ satSq (x0 O wt) := by
    rw [mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero]
    constructor
    · rw [← weightedSeriesOrigin_apply]
      simp [map_sub, map_sum, map_smul, hg0', hx]
    · intro i
      have hser : ser (c • g - ∑ k, a k • F k) = c • ser g - ∑ k, a k • ser (F k) := by
        simp [ser]
      rw [hser, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact sub_eq_zero.mpr (ha i)
  have heq : (satSq (x0 O wt)).mkQ (c • g) = (satSq (x0 O wt)).mkQ (∑ k, a k • F k) := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hsat
  unfold cotSpan
  rw [← map_smul, heq, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
