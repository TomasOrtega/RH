import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.InstIsZLatticeDualLat

open Module
open scoped Real

noncomputable section

namespace PI.Tr

/- English proof (translation)
Use `set N : ℕ := finrank ℤ L + 1 with hN`. Establish `hr : (-(N : ℝ)) < -(finrank ℤ L : ℝ)`. Rewrite using `[hN]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs` using `ZLattice.summable_norm_sub_rpow L (-(N : ℝ)) hr (-w)`. Use `set C : ℝ := max 1 ((N.factorial : ℝ) / a ^ N) with hC`. Establish `key : ∀ u : ℝ, 0 < u → Real.exp (-a * u ^ 2) ≤ C * u ^ (-(N : ℝ))`. Introduce `u hu`. Rewrite using `[Real.rpow_neg hu.le, Real.rpow_natCast]`.

Establish `hinv : 0 ≤ (u ^ N)⁻¹` using `by positivity`. Break down `le_or_gt u 1 with h1 | h1` into its components or cases. Establish `h2 : 1 ≤ (u ^ N)⁻¹` using `(one_le_inv₀ (pow_pos hu N)).2 (pow_le_one₀ hu.le h1)`. Establish `h3 : Real.exp (-a * u ^ 2) ≤ 1` using `Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_max_left _ _`. Establish `h2 : (a * u) ^ N / (N.factorial : ℝ) ≤ Real.exp (a * u)` using `Real.pow_div_factorial_le_exp _ (by positivity) N`. Establish `h3 : Real.exp (a * u) ≤ Real.exp (a * u ^ 2)` using `Real.exp_le_exp.2 (by`. Establish `hu2 : u ≤ u ^ 2` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_left hu2 ha.le)`.

Rewrite using `[show -a * u ^ 2 = -(a * u ^ 2) by ring, Real.exp_neg]`. Establish `hpos : 0 < (a * u) ^ N / (N.factorial : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`. Clear the denominators using the available nonvanishing facts.

Use `_ ≤ C * (u ^ N)⁻¹ := by gcongr`. Conclude with `le_max_right _ _`. Use `Summable.of_nonneg_of_le (fun z => (Real.exp_pos _).le) (f := fun z : L => C * ‖(z : E) - -w‖ ^ (-(N : ℝ)) + (if (z : E) + w = 0 then 1 else 0)) ?_ ?_` and prove the remaining obligations. Introduce `z`. Distinguish the cases in `hz : (z : E) + w = 0`.

Establish `h0 : ‖(z : E) - -w‖ ^ (-(N : ℝ)) = 0`. Rewrite using `[sub_neg_eq_add, hz, norm_zero, Real.zero_rpow]`. Establish `: (0 : ℝ) < N` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hz, h0]`.

Establish `hu : 0 < ‖(z : E) + w‖` using `norm_pos_iff.2 hz`. Simplify using `only [hz, if_false, add_zero, sub_neg_eq_add]`. Conclude with `key _ hu`. Use `(hs.mul_left C).add ?_` and prove the remaining obligations. Apply `summable_of_finite_support` to reduce the goal to its premises.

Apply `Set.Subsingleton.finite` to reduce the goal to its premises. Introduce `z1 h1 z2 h2`. Simplify using `only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h1 h2`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[eq_neg_of_add_eq_zero_left h1, eq_neg_of_add_eq_zero_left h2]`.
-/
private theorem summable_exp_neg_mul_norm_add_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a)
    (w : E) : Summable fun z : L => Real.exp (-a * ‖(z : E) + w‖ ^ 2) := by
  classical
  set N : ℕ := finrank ℤ L + 1 with hN
  have hr : (-(N : ℝ)) < -(finrank ℤ L : ℝ) := by
    rw [hN]
    push_cast
    linarith
  have hs := ZLattice.summable_norm_sub_rpow L (-(N : ℝ)) hr (-w)
  set C : ℝ := max 1 ((N.factorial : ℝ) / a ^ N) with hC
  have key : ∀ u : ℝ, 0 < u → Real.exp (-a * u ^ 2) ≤ C * u ^ (-(N : ℝ)) := by
    intro u hu
    rw [Real.rpow_neg hu.le, Real.rpow_natCast]
    have hinv : 0 ≤ (u ^ N)⁻¹ := by positivity
    rcases le_or_gt u 1 with h1 | h1
    · have h2 : 1 ≤ (u ^ N)⁻¹ := (one_le_inv₀ (pow_pos hu N)).2 (pow_le_one₀ hu.le h1)
      have h3 : Real.exp (-a * u ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
      calc Real.exp (-a * u ^ 2) ≤ 1 := h3
        _ ≤ 1 * (u ^ N)⁻¹ := by linarith
        _ ≤ C * (u ^ N)⁻¹ := by
          gcongr
          exact le_max_left _ _
    · have h2 : (a * u) ^ N / (N.factorial : ℝ) ≤ Real.exp (a * u) :=
        Real.pow_div_factorial_le_exp _ (by positivity) N
      have h3 : Real.exp (a * u) ≤ Real.exp (a * u ^ 2) := Real.exp_le_exp.2 (by
        have hu2 : u ≤ u ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hu2 ha.le)
      rw [show -a * u ^ 2 = -(a * u ^ 2) by ring, Real.exp_neg]
      have hpos : 0 < (a * u) ^ N / (N.factorial : ℝ) := by positivity
      calc (Real.exp (a * u ^ 2))⁻¹ ≤ ((a * u) ^ N / (N.factorial : ℝ))⁻¹ :=
            inv_anti₀ hpos (h2.trans h3)
        _ = ((N.factorial : ℝ) / a ^ N) * (u ^ N)⁻¹ := by
          rw [mul_pow]
          field_simp
        _ ≤ C * (u ^ N)⁻¹ := by
          gcongr
          exact le_max_right _ _
  refine Summable.of_nonneg_of_le (fun z => (Real.exp_pos _).le)
    (f := fun z : L => C * ‖(z : E) - -w‖ ^ (-(N : ℝ)) + (if (z : E) + w = 0 then 1 else 0)) ?_ ?_
  · intro z
    by_cases hz : (z : E) + w = 0
    · have h0 : ‖(z : E) - -w‖ ^ (-(N : ℝ)) = 0 := by
        rw [sub_neg_eq_add, hz, norm_zero, Real.zero_rpow]
        have : (0 : ℝ) < N := by positivity
        linarith
      simp [hz, h0]
    · have hu : 0 < ‖(z : E) + w‖ := norm_pos_iff.2 hz
      simp only [hz, if_false, add_zero, sub_neg_eq_add]
      exact key _ hu
  · refine (hs.mul_left C).add ?_
    apply summable_of_finite_support
    apply Set.Subsingleton.finite
    intro z1 h1 z2 h2
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at h1 h2
    apply Subtype.ext
    rw [eq_neg_of_add_eq_zero_left h1, eq_neg_of_add_eq_zero_left h2]

/- English proof (translation)
Establish `hopen : IsOpenMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle))` using `IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe) (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)`. Use `hopen.isQuotientMap (by fun_prop) ?_` and prove the remaining obligations. Introduce `θ`. Use `⟨fun i => Function.surjInv QuotientAddGroup.mk_surjective (θ i), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Conclude with `Function.surjInv_eq QuotientAddGroup.mk_surjective (θ i)`.
-/
private theorem isQuotientMap_coe_unitAddTorus (ι : Type) [Fintype ι] :
    Topology.IsQuotientMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) := by
  have hopen : IsOpenMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  refine hopen.isQuotientMap (by fun_prop) ?_
  intro θ
  refine ⟨fun i => Function.surjInv QuotientAddGroup.mk_surjective (θ i), ?_⟩
  funext i
  exact Function.surjInv_eq QuotientAddGroup.mk_surjective (θ i)

/- English proof (translation)
Establish `hq` using `isQuotientMap_coe_unitAddTorus ι`. Establish `hfib : ∀ x y : ι → ℝ, (fun i => ((x i : ℝ) : UnitAddCircle)) = (fun i => ((y i : ℝ) : UnitAddCircle)) → G x = G y`. Introduce `x y hxy`. Establish `hk : ∀ i, ∃ k : ℤ, y i = x i + k`. Introduce `i`.

Establish `h` using `congr_fun hxy i`. Rewrite `h` using `[QuotientAddGroup.eq]`. Take `⟨k, hk⟩` from `AddSubgroup.mem_zmultiples_iff.1 h`. Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [zsmul_eq_mul, mul_one] at hk`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `choose k hk using hk`. Establish `hy : y = x + fun i => (k i : ℝ)` using `funext hk`. Rewrite using `[hy, hper]`. Set `F0 : UnitAddTorus ι → ℂ` to `fun θ => G (Function.surjInv hq.surjective θ)`.

Establish `hF0 : ∀ s : ι → ℝ, F0 (fun i => ((s i : ℝ) : UnitAddCircle)) = G s` using `fun s => hfib _ _ (Function.surjInv_eq hq.surjective _)`. Establish `hcont : Continuous F0`. Rewrite using `[hq.continuous_iff]`. Establish `hcomp : (F0 ∘ fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) = G` using `funext hF0`. Rewrite using `[hcomp]`.

Conclude with `hG`. Conclude with `⟨⟨F0, hcont⟩, hF0⟩`.
-/
private theorem exists_continuous_torus_lift_of_periodic {ι : Type} [Fintype ι] (G : (ι → ℝ) → ℂ) (hG : Continuous G)
    (hper : ∀ (s : ι → ℝ) (k : ι → ℤ), G (s + fun i => (k i : ℝ)) = G s) :
    ∃ F : C(UnitAddTorus ι, ℂ), ∀ s : ι → ℝ,
      F (fun i => ((s i : ℝ) : UnitAddCircle)) = G s := by
  have hq := isQuotientMap_coe_unitAddTorus ι
  have hfib : ∀ x y : ι → ℝ, (fun i => ((x i : ℝ) : UnitAddCircle)) =
      (fun i => ((y i : ℝ) : UnitAddCircle)) → G x = G y := by
    intro x y hxy
    have hk : ∀ i, ∃ k : ℤ, y i = x i + k := by
      intro i
      have h := congr_fun hxy i
      rw [QuotientAddGroup.eq] at h
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
      refine ⟨k, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hk
      linarith
    choose k hk using hk
    have hy : y = x + fun i => (k i : ℝ) := funext hk
    rw [hy, hper]
  let F0 : UnitAddTorus ι → ℂ := fun θ => G (Function.surjInv hq.surjective θ)
  have hF0 : ∀ s : ι → ℝ, F0 (fun i => ((s i : ℝ) : UnitAddCircle)) = G s := fun s =>
    hfib _ _ (Function.surjInv_eq hq.surjective _)
  have hcont : Continuous F0 := by
    rw [hq.continuous_iff]
    have hcomp : (F0 ∘ fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) = G := funext hF0
    rw [hcomp]
    exact hG
  exact ⟨⟨F0, hcont⟩, hF0⟩

/- English proof (translation)
Use `set ψ : (ι → ℝ) → ℂ := fun s => UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) with hψ`. Establish `hqper : ∀ (s : ι → ℝ) (k : ι → ℤ), (fun i => (((s + fun i => (k i : ℝ)) i : ℝ) : UnitAddCircle)) = fun i => ((s i : ℝ) : UnitAddCircle)`. Introduce `s k`. Use function extensionality and compare the values at `i`. Rewrite using `[QuotientAddGroup.eq]`.

Use `AddSubgroup.mem_zmultiples_iff.2 ⟨-k i, ?_⟩` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, mul_one, Pi.add_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hψcont : Continuous ψ` using `(UnitAddTorus.mFourier (-m)).continuous.comp (isQuotientMap_coe_unitAddTorus ι).continuous`.

Establish `hψle : ∀ s, ‖ψ s‖ ≤ 1`. Introduce `s`. Use `(UnitAddTorus.mFourier (-m)).norm_coe_le_norm (fun i => ((s i : ℝ) : UnitAddCircle))` as an intermediate fact. Rewrite `this` using `[UnitAddTorus.mFourier_norm]`. Then use the resulting hypothesis. Use `set S : (ι → ℤ) → Set (ι → ℝ) := fun k => {s | ∀ i, s i ∈ Set.Ioc (k i : ℝ) (k i + 1)} with hSdef`.

Establish `hSmeas : ∀ k, MeasurableSet (S k)`. Introduce `k`. Establish `hS : S k = ⋂ i, (fun s : ι → ℝ => s i) ⁻¹' Set.Ioc (k i : ℝ) (k i + 1)`. Use extensionality with `s`. Simplify using `[S]`.

Rewrite using `[hS]`. Conclude with `MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc`. Establish `hSmem : ∀ k s, s ∈ S k ↔ ∀ i, ⌈s i⌉ = k i + 1`. Introduce `k s`. Simplify using `only [S, Set.mem_setOf_eq, Set.mem_Ioc]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[Int.ceil_eq_iff]`. Use `push_cast`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨by linarith, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by linarith, h2⟩`. Establish `hSdisj : Pairwise (Function.onFun Disjoint S)`. Introduce `k k' hne`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `s h1 h2`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `e1` using `(hSmem k s).1 h1 i`.

Establish `e2` using `(hSmem k' s).1 h2 i`. Use linear arithmetic over natural numbers and integers. Establish `hSunion : (⋃ k, S k) = Set.univ`. Use extensionality with `s`. Simplify using `only [Set.mem_iUnion, Set.mem_univ, iff_true]`.

Conclude with `⟨fun i => ⌈s i⌉ - 1, (hSmem _ s).2 fun i => by ring⟩`. Establish `hS0 : S 0 = {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)}`. Use extensionality with `s`. Simplify using `[S]`. Establish `htrans : ∀ k : ι → ℤ, (fun s => s + fun i => (k i : ℝ)) ⁻¹' S k = S 0`.

Introduce `k`. Use extensionality with `s`. Simplify using `only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc, Pi.add_apply, Pi.zero_apply, Int.cast_zero, zero_add]`. Prove the components needed by the constructor for the conclusion. Introduce `hs i`.

Use `hs i` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Introduce `hs i`. Use `hs i` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.

Establish `hmp : ∀ k : ι → ℤ, MeasureTheory.MeasurePreserving (fun s : ι → ℝ => s + fun i => (k i : ℝ)) MeasureTheory.volume MeasureTheory.volume` using `fun k => MeasureTheory.measurePreserving_add_right MeasureTheory.volume _`. Establish `hme : ∀ k : ι → ℤ, MeasurableEmbedding (fun s : ι → ℝ => s + fun i => (k i : ℝ))` using `fun k => (Homeomorph.addRight _).measurableEmbedding`. Establish `hfi : MeasureTheory.Integrable (fun s => ψ s * h s)`. Use `MeasureTheory.Integrable.mono' hh.norm (hψcont.mul hcont).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[UnitAddTorus.mFourierCoeff_eq_integral F m 0, ← hS0]`. Establish `hint : ∀ s : ι → ℝ, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) • F (fun i => ((s i : ℝ) : UnitAddCircle)) = ∑' k : ι → ℤ, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ))`. Introduce `s`. Rewrite using `[hF, smul_eq_mul, ← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [ψ, hqper]`. Rewrite using `[MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint)]`. Rewrite using `[MeasureTheory.integral_tsum]`.

Establish `hEach : ∀ k : ι → ℤ, ∫ s in S 0, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) = ∫ s in S k, ψ s * h s`. Introduce `k`. Rewrite using `[← htrans k]`. Conclude with `(hmp k).setIntegral_preimage_emb (hme k) (fun s => ψ s * h s) (S k)`. Repeatedly rewrite using `[hEach]`.

Establish `hsum` using `MeasureTheory.hasSum_integral_iUnion hSmeas hSdisj hfi.integrableOn`. Rewrite `hsum` using `[hSunion, MeasureTheory.Measure.restrict_univ]`. Conclude with `hsum.tsum_eq`. Introduce `k`. Conclude with `((hψcont.mul hcont).comp (continuous_add_right _)).aestronglyMeasurable`.

Establish `hEach : ∀ k : ι → ℤ, ∫⁻ s in S 0, ‖ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ))‖ₑ = ∫⁻ s in S k, ‖ψ s * h s‖ₑ`. Introduce `k`. Rewrite using `[← htrans k]`. Conclude with `(hmp k).setLIntegral_comp_preimage_emb (hme k) (fun s => ‖ψ s * h s‖ₑ) (S k)`. Repeatedly rewrite using `[hEach]`.

Rewrite using `[← MeasureTheory.lintegral_iUnion hSmeas hSdisj, hSunion, MeasureTheory.Measure.restrict_univ]`. Conclude with `hfi.hasFiniteIntegral.ne`.
-/
private theorem mFourierCoeff_periodization_eq_integral {ι : Type} [Fintype ι] (h : (ι → ℝ) → ℂ) (hh : MeasureTheory.Integrable h)
    (hcont : Continuous h) (F : C(UnitAddTorus ι, ℂ))
    (hF : ∀ s : ι → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, h (s + fun i => (k i : ℝ)))
    (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff F m =
      ∫ s, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) * h s := by
  set ψ : (ι → ℝ) → ℂ := fun s => UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle))
    with hψ
  have hqper : ∀ (s : ι → ℝ) (k : ι → ℤ),
      (fun i => (((s + fun i => (k i : ℝ)) i : ℝ) : UnitAddCircle)) =
        fun i => ((s i : ℝ) : UnitAddCircle) := by
    intro s k
    funext i
    rw [QuotientAddGroup.eq]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨-k i, ?_⟩
    rw [zsmul_eq_mul, mul_one, Pi.add_apply]
    push_cast
    ring
  have hψcont : Continuous ψ :=
    (UnitAddTorus.mFourier (-m)).continuous.comp (isQuotientMap_coe_unitAddTorus ι).continuous
  have hψle : ∀ s, ‖ψ s‖ ≤ 1 := by
    intro s
    have := (UnitAddTorus.mFourier (-m)).norm_coe_le_norm (fun i => ((s i : ℝ) : UnitAddCircle))
    rwa [UnitAddTorus.mFourier_norm] at this
  set S : (ι → ℤ) → Set (ι → ℝ) := fun k => {s | ∀ i, s i ∈ Set.Ioc (k i : ℝ) (k i + 1)} with hSdef
  have hSmeas : ∀ k, MeasurableSet (S k) := by
    intro k
    have hS : S k = ⋂ i, (fun s : ι → ℝ => s i) ⁻¹' Set.Ioc (k i : ℝ) (k i + 1) := by
      ext s
      simp [S]
    rw [hS]
    exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc
  have hSmem : ∀ k s, s ∈ S k ↔ ∀ i, ⌈s i⌉ = k i + 1 := by
    intro k s
    simp only [S, Set.mem_setOf_eq, Set.mem_Ioc]
    refine forall_congr' fun i => ?_
    rw [Int.ceil_eq_iff]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    intro k k' hne
    rw [Function.onFun, Set.disjoint_left]
    intro s h1 h2
    apply hne
    funext i
    have e1 := (hSmem k s).1 h1 i
    have e2 := (hSmem k' s).1 h2 i
    omega
  have hSunion : (⋃ k, S k) = Set.univ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨fun i => ⌈s i⌉ - 1, (hSmem _ s).2 fun i => by ring⟩
  have hS0 : S 0 = {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    ext s
    simp [S]
  have htrans : ∀ k : ι → ℤ, (fun s => s + fun i => (k i : ℝ)) ⁻¹' S k = S 0 := by
    intro k
    ext s
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc, Pi.add_apply, Pi.zero_apply,
      Int.cast_zero, zero_add]
    constructor
    · intro hs i
      have := hs i
      constructor <;> linarith [this.1, this.2]
    · intro hs i
      have := hs i
      constructor <;> linarith [this.1, this.2]
  have hmp : ∀ k : ι → ℤ, MeasureTheory.MeasurePreserving (fun s : ι → ℝ => s + fun i => (k i : ℝ))
      MeasureTheory.volume MeasureTheory.volume := fun k =>
        MeasureTheory.measurePreserving_add_right MeasureTheory.volume _
  have hme : ∀ k : ι → ℤ, MeasurableEmbedding (fun s : ι → ℝ => s + fun i => (k i : ℝ)) :=
    fun k => (Homeomorph.addRight _).measurableEmbedding
  have hfi : MeasureTheory.Integrable (fun s => ψ s * h s) := by
    refine MeasureTheory.Integrable.mono' hh.norm (hψcont.mul hcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    calc ‖ψ s‖ * ‖h s‖ ≤ 1 * ‖h s‖ := by gcongr; exact hψle s
      _ = ‖h s‖ := one_mul _
  rw [UnitAddTorus.mFourierCoeff_eq_integral F m 0, ← hS0]
  have hint : ∀ s : ι → ℝ, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) •
      F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) := by
    intro s
    rw [hF, smul_eq_mul, ← tsum_mul_left]
    congr 1
    funext k
    simp only [ψ, hqper]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint)]
  rw [MeasureTheory.integral_tsum]
  · have hEach : ∀ k : ι → ℤ, ∫ s in S 0, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) =
        ∫ s in S k, ψ s * h s := by
      intro k
      rw [← htrans k]
      exact (hmp k).setIntegral_preimage_emb (hme k) (fun s => ψ s * h s) (S k)
    simp_rw [hEach]
    have hsum := MeasureTheory.hasSum_integral_iUnion hSmeas hSdisj hfi.integrableOn
    rw [hSunion, MeasureTheory.Measure.restrict_univ] at hsum
    exact hsum.tsum_eq
  · intro k
    exact ((hψcont.mul hcont).comp (continuous_add_right _)).aestronglyMeasurable
  · have hEach : ∀ k : ι → ℤ, ∫⁻ s in S 0,
        ‖ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ))‖ₑ = ∫⁻ s in S k, ‖ψ s * h s‖ₑ := by
      intro k
      rw [← htrans k]
      exact (hmp k).setLIntegral_comp_preimage_emb (hme k) (fun s => ‖ψ s * h s‖ₑ) (S k)
    simp_rw [hEach]
    rw [← MeasureTheory.lintegral_iUnion hSmeas hSdisj, hSunion, MeasureTheory.Measure.restrict_univ]
    exact hfi.hasFiniteIntegral.ne

/- English proof (translation)
Simplify using `only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]`. Rewrite using `[← Complex.exp_sum, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mFourier_coe_eq_exp' {ι : Type} [Fintype ι] (m : ι → ℤ) (s : ι → ℝ) :
    UnitAddTorus.mFourier m (fun i => ((s i : ℝ) : UnitAddCircle)) =
      Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (s i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/- English proof (translation)
Use `haveI : (MeasureTheory.Measure.map φ.symm MeasureTheory.volume).IsAddHaarMeasure := φ.symm.isAddHaarMeasure_map _`. Use `set ν : MeasureTheory.Measure E := MeasureTheory.Measure.map φ.symm MeasureTheory.volume with hνdef`. Establish `hν` using `MeasureTheory.Measure.isAddLeftInvariant_eq_smul ν (MeasureTheory.volume : MeasureTheory.Measure E)`. Use `set c := ν.addHaarScalarFactor MeasureTheory.volume with hcdef`. Establish `hc : c ≠ 0`.

Introduce `h0`. Rewrite `hν` using `[h0, zero_smul]`. Conclude with `(NeZero.ne ν) hν`. Use `⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc), fun t ht => ?_, fun t ht y => ?_⟩` and prove the remaining obligations. Establish `hg : MeasureTheory.Integrable (fun x : E => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ))`.

Establish `h0` using `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := ((π * t : ℝ) : ℂ)) (by simp; positivity) 0 (0 : E)`. Use `h0.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [zero_mul, add_zero, Complex.ofReal_exp]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgν : MeasureTheory.Integrable (fun x : E => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) ν`. Rewrite using `[hν]`. Conclude with `hg.smul_measure_nnreal`. Conclude with `(MeasureTheory.integrable_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv _).1 hgν`.

Establish `step1 : ∫ s : ι → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) * (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) = ∫ x, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) ∂ν` using `(MeasureTheory.integral_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv (fun x => Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ))).symm`. Rewrite using `[step1, hν, MeasureTheory.integral_smul_nnreal_measure]`. Establish `step2 : ∀ x : E, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) = Complex.exp (-((π * t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 + (-2 * π * Complex.I) * (inner ℝ y x : ℂ))`. Introduce `x`. Rewrite using `[Complex.ofReal_exp, ← Complex.exp_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[step2]`. Rewrite using `[GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simp; positivity) _ y]`.

Establish `e1 : ((π : ℂ) / ((π * t : ℝ) : ℂ)) ^ ((finrank ℝ E : ℂ) / 2) = ((t ^ (-(finrank ℝ E : ℝ) / 2) : ℝ) : ℂ)`. Rewrite using `[show ((π : ℂ) / ((π * t : ℝ) : ℂ)) = ((t⁻¹ : ℝ) : ℂ) by`. Use `push_cast`. Use the proof step `field_simp]`. Rewrite using `[show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity)]`.

Use `congr 1`. Rewrite using `[Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]`. Put the polynomial expressions in normal form. Establish `e2 : Complex.exp ((-2 * π * Complex.I) ^ 2 * (‖y‖ : ℂ) ^ 2 / (4 * ((π * t : ℝ) : ℂ))) = ((Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_exp]`.

Use `congr 1`. Establish `hpi : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast ht.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, NNReal.smul_def, Complex.real_smul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem integral_fourier_gaussian_eq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type} [Fintype ι]
    (φ : E ≃L[ℝ] (ι → ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧ (∀ t : ℝ, 0 < t → MeasureTheory.Integrable
      (fun s : ι → ℝ => (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ))) ∧ ∀ t : ℝ, 0 < t → ∀ y : E,
      ∫ s : ι → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) *
          (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) =
        ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) * Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
  haveI : (MeasureTheory.Measure.map φ.symm MeasureTheory.volume).IsAddHaarMeasure :=
    φ.symm.isAddHaarMeasure_map _
  set ν : MeasureTheory.Measure E := MeasureTheory.Measure.map φ.symm MeasureTheory.volume with hνdef
  have hν := MeasureTheory.Measure.isAddLeftInvariant_eq_smul ν (MeasureTheory.volume : MeasureTheory.Measure E)
  set c := ν.addHaarScalarFactor MeasureTheory.volume with hcdef
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hν
    exact (NeZero.ne ν) hν
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc), fun t ht => ?_, fun t ht y => ?_⟩
  · have hg : MeasureTheory.Integrable (fun x : E => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) := by
      have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
        (b := ((π * t : ℝ) : ℂ)) (by simp; positivity) 0 (0 : E)
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [zero_mul, add_zero, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hgν : MeasureTheory.Integrable (fun x : E => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) ν := by
      rw [hν]
      exact hg.smul_measure_nnreal
    exact (MeasureTheory.integrable_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv _).1 hgν
  have step1 : ∫ s : ι → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) *
        (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) =
      ∫ x, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
        (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) ∂ν :=
    (MeasureTheory.integral_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv
      (fun x => Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
        (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ))).symm
  rw [step1, hν, MeasureTheory.integral_smul_nnreal_measure]
  have step2 : ∀ x : E, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
      (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) =
      Complex.exp (-((π * t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 + (-2 * π * Complex.I) * (inner ℝ y x : ℂ)) := by
    intro x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [step2]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simp; positivity) _ y]
  have e1 : ((π : ℂ) / ((π * t : ℝ) : ℂ)) ^ ((finrank ℝ E : ℂ) / 2) =
      ((t ^ (-(finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((π : ℂ) / ((π * t : ℝ) : ℂ)) = ((t⁻¹ : ℝ) : ℂ) by
      push_cast
      field_simp]
    rw [show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    ring_nf
  have e2 : Complex.exp ((-2 * π * Complex.I) ^ 2 * (‖y‖ : ℂ) ^ 2 / (4 * ((π * t : ℝ) : ℂ))) =
      ((Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e1, e2, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `v0`. Establish `hs` using `summable_exp_neg_mul_norm_add_sq L (a := a / 2) (by positivity) v0`. Establish `hon : ContinuousOn (fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2)) (Metric.ball v0 1)`. Use `continuousOn_tsum (fun z => by fun_prop) (hs.mul_left (Real.exp a)) ?_` and prove the remaining obligations.

Introduce `z v hv`. Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h1 : ‖(z : E) + v0‖ ≤ ‖(z : E) + v‖ + ‖v - v0‖`. Establish `hzv : (z : E) + v0 = ((z : E) + v) - (v - v0)` using `by abel`.

Rewrite using `[hzv]`. Conclude with `norm_sub_le _ _`. Establish `h2 : ‖v - v0‖ < 1` using `by rwa [Metric.mem_ball, dist_eq_norm] at hv`. Establish `h3` using `norm_nonneg ((z : E) + v)`. Establish `h4` using `norm_nonneg (v - v0)`.

Establish `h6` using `norm_nonneg ((z : E) + v0)`. Establish `h5 : ‖(z : E) + v0‖ ^ 2 ≤ 2 * ‖(z : E) + v‖ ^ 2 + 2`. Use polynomial arithmetic with `[sq_nonneg (‖(z : E) + v‖ - ‖v - v0‖)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h5 ha.le]`. Conclude with `hon.continuousAt (Metric.ball_mem_nhds v0 one_pos)`.
-/
private theorem continuous_tsum_exp_neg_mul_norm_add_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Continuous fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro v0
  have hs := summable_exp_neg_mul_norm_add_sq L (a := a / 2) (by positivity) v0
  have hon : ContinuousOn (fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2))
      (Metric.ball v0 1) := by
    refine continuousOn_tsum (fun z => by fun_prop) (hs.mul_left (Real.exp a)) ?_
    intro z v hv
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : ‖(z : E) + v0‖ ≤ ‖(z : E) + v‖ + ‖v - v0‖ := by
      have hzv : (z : E) + v0 = ((z : E) + v) - (v - v0) := by abel
      rw [hzv]
      exact norm_sub_le _ _
    have h2 : ‖v - v0‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have h3 := norm_nonneg ((z : E) + v)
    have h4 := norm_nonneg (v - v0)
    have h6 := norm_nonneg ((z : E) + v0)
    have h5 : ‖(z : E) + v0‖ ^ 2 ≤ 2 * ‖(z : E) + v‖ ^ 2 + 2 := by
      nlinarith [sq_nonneg (‖(z : E) + v‖ - ‖v - v0‖)]
    nlinarith [mul_le_mul_of_nonneg_left h5 ha.le]
  exact hon.continuousAt (Metric.ball_mem_nhds v0 one_pos)

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `bR` to `b.ofZLatticeBasis ℝ Λ`. Set `φ : E ≃L[ℝ] (Module.Free.ChooseBasisIndex ℤ Λ → ℝ)` to `bR.equivFun.toContinuousLinearEquiv`. Establish `hφ : ∀ x i, φ x i = bR.repr x i` using `fun x i => rfl`. Set `d : Module.Free.ChooseBasisIndex ℤ Λ → E` to `fun i => (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (bR.coord i))`.

Establish `hd : ∀ i x, inner ℝ (d i) x = φ x i`. Introduce `i x`. Simplify using `[d, hφ, InnerProductSpace.toDual_symm_apply, Basis.coord_apply]`. Set `y : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) → E` to `fun m => ∑ i, (m i : ℝ) • d i`. Establish `hy : ∀ m x, inner ℝ (y m) x = ∑ i, (m i : ℝ) * φ x i`.

Introduce `m x`. Simplify using `[y, sum_inner, real_inner_smul_left, hd]`. Establish `hφΛ : ∀ (x : Λ) i, φ (x : E) i = (b.repr x i : ℝ)`. Introduce `x i`. Rewrite using `[hφ, Basis.ofZLatticeBasis_repr_apply]`.

Establish `hmem : ∀ m, y m ∈ dualLat Λ`. Introduce `m`. Rewrite using `[mem_dualLat]`. Introduce `x hx`. Use `⟨∑ i, m i * b.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations.

Rewrite using `[real_inner_comm, hy]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hφΛ ⟨x, hx⟩ i]`. Establish `hφb : ∀ j, φ (bR j) = Pi.single j 1`.

Introduce `j`. Use function extensionality and compare the values at `i`. Rewrite using `[hφ, Basis.repr_self]`. Simplify using `[Finsupp.single_apply, Pi.single_apply, eq_comm]`. Establish `hinj : Function.Injective y`.

Introduce `m m' h`. Use function extensionality and compare the values at `j`. Establish `h2` using `congrArg (fun z => inner ℝ z (bR j)) h`. Simplify using `only [hy, hφb] at h2`. Simplify using `[Pi.single_apply] at h2`.

Conclude with `h2` after adjusting the coercions. Establish `hsurj : ∀ z ∈ dualLat Λ, ∃ m, y m = z`. Introduce `z hz`. Rewrite `hz` using `[mem_dualLat]`. Establish `hbΛ : ∀ j, bR j ∈ Λ`.

Introduce `j`. Rewrite using `[Basis.ofZLatticeBasis_apply]`. Conclude with `(b j).2`. Use `choose n hn using fun j => hz (bR j) (hbΛ j)`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Apply `InnerProductSpace.ext_inner_left_basis bR` to reduce the goal to its premises. Introduce `j`. Rewrite using `[real_inner_comm, hy, hφb, hn j]`. Simplify using `[Pi.single_apply]`. Set `D : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) ≃ dualLat Λ` to `Equiv.ofBijective (fun m => ⟨y m, hmem m⟩) ⟨fun m m' h => hinj (congrArg Subtype.val h), fun z => by`.

Take `⟨m, hm⟩` from `hsurj z.1 z.2`. Conclude with `⟨m, Subtype.ext hm⟩⟩`. Use `⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, φ, b.equivFun.symm.toEquiv, D, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[φ.apply_symm_apply]`. Use function extensionality and compare the values at `i`. Rewrite using `[hφΛ]`. Establish `h3` using `congr_fun (b.equivFun.apply_symm_apply k) i`. Simplify using `only [Basis.equivFun_apply] at h3`.

Conclude with `h3` after adjusting the coercions. Introduce `m x`. Conclude with `hy m x`.
-/
private theorem exists_coords_zLattice_dual_basis {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (ι : Type) (_ : Fintype ι) (φ : E ≃L[ℝ] (ι → ℝ)) (B : (ι → ℤ) ≃ Λ)
      (D : (ι → ℤ) ≃ dualLat Λ),
      (∀ k, ((B k : Λ) : E) = φ.symm (fun i => (k i : ℝ))) ∧
      (∀ m x, inner ℝ ((D m : dualLat Λ) : E) x = ∑ i, (m i : ℝ) * φ x i) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := b.ofZLatticeBasis ℝ Λ
  let φ : E ≃L[ℝ] (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) := bR.equivFun.toContinuousLinearEquiv
  have hφ : ∀ x i, φ x i = bR.repr x i := fun x i => rfl
  let d : Module.Free.ChooseBasisIndex ℤ Λ → E :=
    fun i => (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (bR.coord i))
  have hd : ∀ i x, inner ℝ (d i) x = φ x i := by
    intro i x
    simp [d, hφ, InnerProductSpace.toDual_symm_apply, Basis.coord_apply]
  let y : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) → E := fun m => ∑ i, (m i : ℝ) • d i
  have hy : ∀ m x, inner ℝ (y m) x = ∑ i, (m i : ℝ) * φ x i := by
    intro m x
    simp [y, sum_inner, real_inner_smul_left, hd]
  have hφΛ : ∀ (x : Λ) i, φ (x : E) i = (b.repr x i : ℝ) := by
    intro x i
    rw [hφ, Basis.ofZLatticeBasis_repr_apply]
  have hmem : ∀ m, y m ∈ dualLat Λ := by
    intro m
    rw [mem_dualLat]
    intro x hx
    refine ⟨∑ i, m i * b.repr ⟨x, hx⟩ i, ?_⟩
    rw [real_inner_comm, hy]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφΛ ⟨x, hx⟩ i]
  have hφb : ∀ j, φ (bR j) = Pi.single j 1 := by
    intro j
    funext i
    rw [hφ, Basis.repr_self]
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hinj : Function.Injective y := by
    intro m m' h
    funext j
    have h2 := congrArg (fun z => inner ℝ z (bR j)) h
    simp only [hy, hφb] at h2
    simp [Pi.single_apply] at h2
    exact_mod_cast h2
  have hsurj : ∀ z ∈ dualLat Λ, ∃ m, y m = z := by
    intro z hz
    rw [mem_dualLat] at hz
    have hbΛ : ∀ j, bR j ∈ Λ := by
      intro j
      rw [Basis.ofZLatticeBasis_apply]
      exact (b j).2
    choose n hn using fun j => hz (bR j) (hbΛ j)
    refine ⟨n, ?_⟩
    apply InnerProductSpace.ext_inner_left_basis bR
    intro j
    rw [real_inner_comm, hy, hφb, hn j]
    simp [Pi.single_apply]
  let D : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) ≃ dualLat Λ :=
    Equiv.ofBijective (fun m => ⟨y m, hmem m⟩)
      ⟨fun m m' h => hinj (congrArg Subtype.val h), fun z => by
        obtain ⟨m, hm⟩ := hsurj z.1 z.2
        exact ⟨m, Subtype.ext hm⟩⟩
  refine ⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, φ, b.equivFun.symm.toEquiv, D, ?_, ?_⟩
  · intro k
    apply φ.injective
    rw [φ.apply_symm_apply]
    funext i
    rw [hφΛ]
    have h3 := congr_fun (b.equivFun.apply_symm_apply k) i
    simp only [Basis.equivFun_apply] at h3
    exact_mod_cast h3
  · intro m x
    exact hy m x

/- English proof (translation)
Introduce `E _ _ _ Λ _ _`. Use `letI : MeasurableSpace E := borel E`. Use `haveI : BorelSpace E := ⟨rfl⟩`. Take `⟨ι, _, φ, B, D, hB, hD⟩` from `exists_coords_zLattice_dual_basis Λ`. Take `⟨κ, hκ, hInt, hG⟩` from `integral_fourier_gaussian_eq φ`.

Establish `sum1 : ∀ t : ℝ, 0 < t → ∀ v : E, Summable fun x : Λ => Real.exp (-π * t * ‖(x : E) + v‖ ^ 2)`. Introduce `t ht v`. Use `(summable_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity) v).congr fun z => ?_` and prove the remaining obligations. Put the polynomial expressions in normal form. Establish `sum2 : ∀ t : ℝ, 0 < t → Summable fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t)`.

Introduce `t ht`. Use `(summable_exp_neg_mul_norm_add_sq (dualLat Λ) (a := π / t) (by positivity) 0).congr fun z => ?_` and prove the remaining obligations. Rewrite using `[add_zero]`. Put the polynomial expressions in normal form. Use `⟨sum1, sum2, κ, hκ, fun t ht v => ?_⟩` and prove the remaining obligations.

Use `set P : E → ℝ := fun w => ∑' x : Λ, Real.exp (-π * t * ‖(x : E) + w‖ ^ 2) with hP`. Establish `hPcont : Continuous P`. Use `(continuous_tsum_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity)).congr fun w => ?_` and prove the remaining obligations. Simplify using `only [hP]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Put the polynomial expressions in normal form. Establish `hPper : ∀ (w : E) (z : Λ), P (w + z) = P w`. Introduce `w z`. Establish `e0` using `(Equiv.addRight z).tsum_eq (fun x : Λ => Real.exp (-π * t * ‖(x : E) + w‖ ^ 2))`.

Simplify using `only [hP]`. Rewrite using `[← e0]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Equiv.coe_addRight, Submodule.coe_add]`.

Use `congr 3`. Use `abel_nf`. Use `set G : (ι → ℝ) → ℂ := fun s => ((P (φ.symm s) : ℝ) : ℂ) with hGdef`. Establish `hGcont : Continuous G` using `Complex.continuous_ofReal.comp (hPcont.comp φ.symm.continuous)`. Establish `hGper : ∀ (s : ι → ℝ) (k : ι → ℤ), G (s + fun i => (k i : ℝ)) = G s`.

Introduce `s k`. Simplify using `only [hGdef, map_add, ← hB k]`. Rewrite using `[hPper]`. Take `⟨F, hF⟩` from `exists_continuous_torus_lift_of_periodic G hGcont hGper`. Use `set h : (ι → ℝ) → ℂ := fun s => (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) with hhdef`.

Establish `hhcont : Continuous h` using `Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul ((continuous_norm.comp φ.symm.continuous).pow 2)))`. Establish `hFh : ∀ s : ι → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) = ∑' k : ι → ℤ, h (s + fun i => (k i : ℝ))`. Introduce `s`. Rewrite using `[hF]`. Simplify using `only [hGdef, hP]`.

Rewrite using `[Complex.ofReal_tsum, ← B.tsum_eq]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [hhdef, map_add, hB k, add_comm]`. Establish `hcoef : ∀ m : ι → ℤ, UnitAddTorus.mFourierCoeff F m = ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) * Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) : ℝ) : ℂ)`.

Introduce `m`. Rewrite using `[mFourierCoeff_periodization_eq_integral h (hInt t ht) hhcont F hFh m, ← hG t ht (D m)]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[mFourier_coe_eq_exp', hD, φ.apply_symm_apply]`.

Use `congr 2`. Simplify using `only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsumc : Summable (UnitAddTorus.mFourierCoeff F)`. Establish `e1 : UnitAddTorus.mFourierCoeff F = fun m => ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) * Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) : ℝ) : ℂ)` using `funext hcoef`.

Rewrite using `[e1]`. Apply `Complex.summable_ofReal.2` to reduce the goal to its premises. Apply `Summable.mul_left` to reduce the goal to its premises. Conclude with `(D.summable_iff (f := fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t))).2 (sum2 t ht)`. Establish `hs` using `UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumc (fun i => ((φ v i : ℝ) : UnitAddCircle))`.

Rewrite `hs` using `[hF]`. Simplify using `only [hGdef, ContinuousLinearEquiv.symm_apply_apply] at hs`. Establish `hre` using `Complex.reCLM.hasSum hs`. Simplify using `only [Complex.reCLM_apply, Complex.ofReal_re] at hre`. Establish `hterm : ∀ m : ι → ℤ, (UnitAddTorus.mFourierCoeff F m • UnitAddTorus.mFourier m (fun i => ((φ v i : ℝ) : UnitAddCircle))).re = κ * t ^ (-(finrank ℝ E : ℝ) / 2) * (Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) * Real.cos (2 * π * inner ℝ ((D m : dualLat Λ) : E) v))`.

Introduce `m`. Rewrite using `[hcoef, mFourier_coe_eq_exp', smul_eq_mul, Complex.re_ofReal_mul]`. Establish `e2 : (2 * π * Complex.I * ∑ i, (m i : ℂ) * (φ v i : ℂ)) = ((2 * π * inner ℝ ((D m : dualLat Λ) : E) v : ℝ) : ℂ) * Complex.I`. Rewrite using `[hD]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, Complex.exp_ofReal_mul_I_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre2 : HasSum (fun y : dualLat Λ => κ * t ^ (-(finrank ℝ E : ℝ) / 2) * (Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * inner ℝ (y : E) v))) (P v)`. Rewrite using `[← D.hasSum_iff]`.

Use `hre.congr_fun ?_` and prove the remaining obligations. Introduce `m`. Conclude with `(hterm m).symm`. Rewrite using `[← tsum_mul_left]`. Conclude with `hre2.tsum_eq.symm`.
-/
theorem poissonGauss : PoissonGauss := by
  intro E _ _ _ Λ _ _
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨ι, _, φ, B, D, hB, hD⟩ := exists_coords_zLattice_dual_basis Λ
  obtain ⟨κ, hκ, hInt, hG⟩ := integral_fourier_gaussian_eq φ
  have sum1 : ∀ t : ℝ, 0 < t → ∀ v : E,
      Summable fun x : Λ => Real.exp (-π * t * ‖(x : E) + v‖ ^ 2) := by
    intro t ht v
    refine (summable_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity) v).congr fun z => ?_
    ring_nf
  have sum2 : ∀ t : ℝ, 0 < t →
      Summable fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by
    intro t ht
    refine (summable_exp_neg_mul_norm_add_sq (dualLat Λ) (a := π / t) (by positivity) 0).congr fun z => ?_
    rw [add_zero]
    ring_nf
  refine ⟨sum1, sum2, κ, hκ, fun t ht v => ?_⟩
  set P : E → ℝ := fun w => ∑' x : Λ, Real.exp (-π * t * ‖(x : E) + w‖ ^ 2) with hP
  have hPcont : Continuous P := by
    refine (continuous_tsum_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity)).congr fun w => ?_
    simp only [hP]
    congr 1
    funext x
    ring_nf
  have hPper : ∀ (w : E) (z : Λ), P (w + z) = P w := by
    intro w z
    have e0 := (Equiv.addRight z).tsum_eq (fun x : Λ => Real.exp (-π * t * ‖(x : E) + w‖ ^ 2))
    simp only [hP]
    rw [← e0]
    congr 1
    funext x
    simp only [Equiv.coe_addRight, Submodule.coe_add]
    congr 3
    abel_nf
  set G : (ι → ℝ) → ℂ := fun s => ((P (φ.symm s) : ℝ) : ℂ) with hGdef
  have hGcont : Continuous G := Complex.continuous_ofReal.comp (hPcont.comp φ.symm.continuous)
  have hGper : ∀ (s : ι → ℝ) (k : ι → ℤ), G (s + fun i => (k i : ℝ)) = G s := by
    intro s k
    simp only [hGdef, map_add, ← hB k]
    rw [hPper]
  obtain ⟨F, hF⟩ := exists_continuous_torus_lift_of_periodic G hGcont hGper
  set h : (ι → ℝ) → ℂ := fun s => (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) with hhdef
  have hhcont : Continuous h :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_norm.comp φ.symm.continuous).pow 2)))
  have hFh : ∀ s : ι → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, h (s + fun i => (k i : ℝ)) := by
    intro s
    rw [hF]
    simp only [hGdef, hP]
    rw [Complex.ofReal_tsum, ← B.tsum_eq]
    congr 1
    funext k
    simp only [hhdef, map_add, hB k, add_comm]
  have hcoef : ∀ m : ι → ℤ, UnitAddTorus.mFourierCoeff F m =
      ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) *
        Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) : ℝ) : ℂ) := by
    intro m
    rw [mFourierCoeff_periodization_eq_integral h (hInt t ht) hhcont F hFh m, ← hG t ht (D m)]
    congr 1
    funext s
    rw [mFourier_coe_eq_exp', hD, φ.apply_symm_apply]
    congr 2
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  have hsumc : Summable (UnitAddTorus.mFourierCoeff F) := by
    have e1 : UnitAddTorus.mFourierCoeff F = fun m => ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) *
        Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) : ℝ) : ℂ) := funext hcoef
    rw [e1]
    apply Complex.summable_ofReal.2
    apply Summable.mul_left
    exact (D.summable_iff (f := fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t))).2 (sum2 t ht)
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumc
    (fun i => ((φ v i : ℝ) : UnitAddCircle))
  rw [hF] at hs
  simp only [hGdef, ContinuousLinearEquiv.symm_apply_apply] at hs
  have hre := Complex.reCLM.hasSum hs
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  have hterm : ∀ m : ι → ℤ, (UnitAddTorus.mFourierCoeff F m •
      UnitAddTorus.mFourier m (fun i => ((φ v i : ℝ) : UnitAddCircle))).re =
      κ * t ^ (-(finrank ℝ E : ℝ) / 2) * (Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) *
        Real.cos (2 * π * inner ℝ ((D m : dualLat Λ) : E) v)) := by
    intro m
    rw [hcoef, mFourier_coe_eq_exp', smul_eq_mul, Complex.re_ofReal_mul]
    have e2 : (2 * π * Complex.I * ∑ i, (m i : ℂ) * (φ v i : ℂ)) =
        ((2 * π * inner ℝ ((D m : dualLat Λ) : E) v : ℝ) : ℂ) * Complex.I := by
      rw [hD]
      push_cast
      ring
    rw [e2, Complex.exp_ofReal_mul_I_re]
    ring
  have hre2 : HasSum (fun y : dualLat Λ => κ * t ^ (-(finrank ℝ E : ℝ) / 2) *
      (Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * inner ℝ (y : E) v))) (P v) := by
    rw [← D.hasSum_iff]
    refine hre.congr_fun ?_
    intro m
    exact (hterm m).symm
  rw [← tsum_mul_left]
  exact hre2.tsum_eq.symm

end PI.Tr
