import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankLocalForm

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, fun Y hY => ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ T`. Use `filter_upwards [hT.isOpen.mem_nhds hx, hΨ.1.1.eventually_eq x] with y hy h`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hy, h]`. Use `filter_upwards [hT.compl.isOpen.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]`. Use `HasCompactSupport.mono hΨ.1.2 fun y hy h => hy ?_` and prove the remaining obligations. Distinguish the cases in `hy' : y ∈ T`.

Rewrite using `[Set.indicator_of_mem hy', h]`. Conclude with `Set.indicator_of_notMem hy' _`. Distinguish the cases in `hy' : Y ∈ T`. Rewrite using `[Set.indicator_of_mem hy', hΨ.2 Y hY]`. Conclude with `Set.indicator_of_notMem hy' _`.
-/
theorem indicator_mem_fullRk {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} {T : Set (Matrix (Fin n) (Fin d) k)} (hT : IsClopen T)
    {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d) :
    T.indicator Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ T
    · filter_upwards [hT.isOpen.mem_nhds hx, hΨ.1.1.eventually_eq x] with y hy h
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, h]
    · filter_upwards [hT.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · refine HasCompactSupport.mono hΨ.1.2 fun y hy h => hy ?_
    by_cases hy' : y ∈ T
    · rw [Set.indicator_of_mem hy', h]
    · exact Set.indicator_of_notMem hy' _
  · by_cases hy' : Y ∈ T
    · rw [Set.indicator_of_mem hy', hΨ.2 Y hY]
    · exact Set.indicator_of_notMem hy' _

/- English proof (translation)
Establish `hF0 : F 0 = 0`. Use `hF 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 1` as an intermediate fact. Simplify using `at this`. Conclude with `this`. Establish `hFsum : ∀ (t : Finset ι) (c : ι → ℂ), F (∑ i ∈ t, c i • (A i).1) = ∑ i ∈ t, c i • F (A i).1`.

Introduce `t c`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [hF0]`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hF _ (A a).2 _ ((GlobalTheory.FullRankCoinv.fullRk k n d).sum_mem fun i _ => (GlobalTheory.FullRankCoinv.fullRk k n d).smul_mem _ (A i).2), ih]`.

Set `v : Matrix (Fin n) (Fin d) k → ι → ℂ` to `fun Y i => if i ∈ s then (B i).1 Y else 0`. Establish `hv : IsLocallyConstant v`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `: ∀ᶠ y in 𝓝 x, ∀ i ∈ s, (B i).1 y = (B i).1 x` using `(Filter.eventually_all_finset s).2 fun i _ => (B i).2.1.1.eventually_eq x`.

Use `filter_upwards [this] with y hy`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i ∈ s`. Simplify using `[v, hi, hy i hi]`. Simplify using `[v, hi]`.

Set `K : Set (Matrix (Fin n) (Fin d) k)` to `⋃ i ∈ s, tsupport (B i).1`. Establish `hK : IsCompact K` using `s.isCompact_biUnion fun i _ => (B i).2.1.2`. Establish `hR : (v '' K).Finite` using `by haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Rewrite using `[Set.image_eq_range]`. Conclude with `(hv.comp_continuous continuous_subtype_val).range_finite`.

Establish `hvK : ∀ Y, v Y ≠ 0 → Y ∈ K`. Introduce `Y hY`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hY`. Distinguish the cases in `his : i ∈ s`. Simplify using `only [v, his, if_true, Pi.zero_apply] at hi`.

Conclude with `Set.mem_biUnion his (subset_tsupport _ hi)`. Simplify using `[v, his] at hi`. Establish `hE : ∀ w : ι → ℂ, ∃ E : GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y, E.1 Y = if v Y = w ∧ w ≠ 0 then 1 else 0`. Introduce `w`. Distinguish the cases in `hw : w = 0`.

Conclude with `⟨0, fun Y => by simp [hw]⟩`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hw`. Establish `hcl : IsClopen (v ⁻¹' {w})` using `hv.isClopen_fiber w`. Use `⟨⟨(v ⁻¹' {w}).indicator ((w i)⁻¹ • (B i).1), indicator_mem_fullRk hcl ((GlobalTheory.FullRankCoinv.fullRk k n d).smul_mem _ (B i).2)⟩, fun Y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hY : v Y = w`.

Establish `his : i ∈ s`. Assume the negation of the conclusion as `his`. Apply `hi` to reduce the goal to its premises. Rewrite using `[← hY]`. Simplify using `[v, his]`.

Establish `hBi : (B i).1 Y = w i` using `by rw [← hY]; simp [v, his]`. Simplify using `only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, hY, if_true, hw, ne_eq, not_false_eq_true, and_self, Pi.smul_apply, smul_eq_mul, hBi]`. Conclude with `inv_mul_cancel₀ hi`. Simplify using `[Set.indicator, hY]`. Use `choose E hEv using hE`.

Use `set T := hR.toFinset`. Establish `hdec : ∀ i ∈ s, B i = ∑ w ∈ T, w i • E w`. Introduce `i hi`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `Y`.

Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hEv]`. Distinguish the cases in `h0 : v Y = 0`. Establish `: (B i).1 Y = 0`. Use `congrFun h0 i` as an intermediate fact.

Simplify `this` using `[v, hi]`. Rewrite using `[this]`. Use `(Finset.sum_eq_zero fun w _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `hw : w = 0`. Simplify using `[hw]`.

Establish `: ¬ (v Y = w)` using `fun h => hw (h ▸ h0)`. Simplify using `[this]`. Rewrite using `[Finset.sum_eq_single (v Y)]`. Simplify using `[h0, v, hi]`. Introduce `w _ hw`.

Simplify using `[Ne.symm hw]`. Introduce `hn`. Conclude with `absurd (hR.mem_toFinset.mpr ⟨Y, hvK Y h0, rfl⟩) hn`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[hdec i hi, map_sum]`. Simplify using the standard rewrite rules. Use `_ = ∑ w ∈ T, Bf (∑ i ∈ s, (starRingEnd ℂ) (w i) • A i) (E w) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum, LinearMap.sum_apply]`. Simplify using the standard rewrite rules. Use `_ = 0 := by`. Use `Finset.sum_eq_zero fun w _ => hloc _ _ fun Y hY => ?_` and prove the remaining obligations. Rewrite `hY` using `[hEv]`.

Establish `hY' : v Y = w ∧ w ≠ 0`. Assume the negation of the conclusion as `hc`. Simplify using `[hc] at hY`. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`.

Rewrite using `[hFsum, Finset.sum_apply, ← h Y]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `: w i = (B i).1 Y` using `by rw [← hY'.1]; simp [v, hi]`. Simplify using `[this, mul_comm]`.
-/
theorem key (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (F : (Matrix (Fin n) (Fin d) k → ℂ) → Matrix (Fin n) (Fin d) k → ℂ)
    (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ)
    (hF : ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Ψ' ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ c : ℂ,
      F (c • Ψ + Ψ') = c • F Ψ + F Ψ')
    (hloc : ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Ψ₂.1 Y ≠ 0 → F Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0)
    {ι : Type} (s : Finset ι) (A B : ι → GlobalTheory.FullRankCoinv.fullRk k n d)
    (h : ∀ Y, ∑ i ∈ s, F (A i).1 Y * (starRingEnd ℂ) ((B i).1 Y) = 0) :
    ∑ i ∈ s, Bf (A i) (B i) = 0 := by
  classical
  have hF0 : F 0 = 0 := by
    have := hF 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 1
    simp at this
    exact this
  have hFsum : ∀ (t : Finset ι) (c : ι → ℂ),
      F (∑ i ∈ t, c i • (A i).1) = ∑ i ∈ t, c i • F (A i).1 := by
    intro t c
    induction t using Finset.induction_on with
    | empty => simp [hF0]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hF _ (A a).2 _ ((GlobalTheory.FullRankCoinv.fullRk k n d).sum_mem fun i _ => (GlobalTheory.FullRankCoinv.fullRk k n d).smul_mem _ (A i).2), ih]

  let v : Matrix (Fin n) (Fin d) k → ι → ℂ := fun Y i => if i ∈ s then (B i).1 Y else 0
  have hv : IsLocallyConstant v := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, (B i).1 y = (B i).1 x :=
      (Filter.eventually_all_finset s).2 fun i _ => (B i).2.1.1.eventually_eq x
    filter_upwards [this] with y hy
    funext i
    by_cases hi : i ∈ s
    · simp [v, hi, hy i hi]
    · simp [v, hi]
  let K : Set (Matrix (Fin n) (Fin d) k) := ⋃ i ∈ s, tsupport (B i).1
  have hK : IsCompact K := s.isCompact_biUnion fun i _ => (B i).2.1.2
  have hR : (v '' K).Finite := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [Set.image_eq_range]
    exact (hv.comp_continuous continuous_subtype_val).range_finite
  have hvK : ∀ Y, v Y ≠ 0 → Y ∈ K := by
    intro Y hY
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hY
    by_cases his : i ∈ s
    · simp only [v, his, if_true, Pi.zero_apply] at hi
      exact Set.mem_biUnion his (subset_tsupport _ hi)
    · simp [v, his] at hi

  have hE : ∀ w : ι → ℂ, ∃ E : GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y, E.1 Y = if v Y = w ∧ w ≠ 0 then 1 else 0 := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, fun Y => by simp [hw]⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hcl : IsClopen (v ⁻¹' {w}) := hv.isClopen_fiber w
    refine ⟨⟨(v ⁻¹' {w}).indicator ((w i)⁻¹ • (B i).1),
      indicator_mem_fullRk hcl ((GlobalTheory.FullRankCoinv.fullRk k n d).smul_mem _ (B i).2)⟩, fun Y => ?_⟩
    by_cases hY : v Y = w
    · have his : i ∈ s := by
        by_contra his
        apply hi
        rw [← hY]
        simp [v, his]
      have hBi : (B i).1 Y = w i := by rw [← hY]; simp [v, his]
      simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, hY, if_true, hw, ne_eq,
        not_false_eq_true, and_self, Pi.smul_apply, smul_eq_mul, hBi]
      exact inv_mul_cancel₀ hi
    · simp [Set.indicator, hY]
  choose E hEv using hE
  set T := hR.toFinset
  have hdec : ∀ i ∈ s, B i = ∑ w ∈ T, w i • E w := by
    intro i hi
    apply Subtype.ext
    funext Y
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hEv]
    by_cases h0 : v Y = 0
    · have : (B i).1 Y = 0 := by
        have := congrFun h0 i
        simpa [v, hi] using this
      rw [this]
      refine (Finset.sum_eq_zero fun w _ => ?_).symm
      by_cases hw : w = 0
      · simp [hw]
      · have : ¬ (v Y = w) := fun h => hw (h ▸ h0)
        simp [this]
    · rw [Finset.sum_eq_single (v Y)]
      · simp [h0, v, hi]
      · intro w _ hw
        simp [Ne.symm hw]
      · intro hn
        exact absurd (hR.mem_toFinset.mpr ⟨Y, hvK Y h0, rfl⟩) hn

  calc ∑ i ∈ s, Bf (A i) (B i)
      = ∑ i ∈ s, ∑ w ∈ T, (starRingEnd ℂ) (w i) * Bf (A i) (E w) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hdec i hi, map_sum]
        simp
    _ = ∑ w ∈ T, Bf (∑ i ∈ s, (starRingEnd ℂ) (w i) • A i) (E w) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [map_sum, LinearMap.sum_apply]
        simp
    _ = 0 := by
        refine Finset.sum_eq_zero fun w _ => hloc _ _ fun Y hY => ?_
        rw [hEv] at hY
        have hY' : v Y = w ∧ w ≠ 0 := by
          by_contra hc
          simp [hc] at hY
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul]
        rw [hFsum, Finset.sum_apply, ← h Y]
        refine Finset.sum_congr rfl fun i hi => ?_
        have : w i = (B i).1 Y := by rw [← hY'.1]; simp [v, hi]
        simp [this, mul_comm]

/- English proof (translation)
Introduce `k _ _ _ _ n d F Bf hF hloc`. Establish `hF0 : F 0 = 0`. Use `hF 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 1` as an intermediate fact. Simplify using `at this`. Conclude with `this`.

Establish `hFs : ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ c : ℂ, F (c • Ψ) = c • F Ψ`. Introduce `Ψ hΨ c`. Use `hF Ψ hΨ 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem c` as an intermediate fact. Simplify `this` using `[hF0]`. Set `Tm : (GlobalTheory.FullRankCoinv.fullRk k n d × GlobalTheory.FullRankCoinv.fullRk k n d →₀ ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)` to `Finsupp.linearCombination ℂ (fun p => fun Y => F p.1.1 Y * (starRingEnd ℂ) (p.2.1 Y))`.

Set `Bm : (GlobalTheory.FullRankCoinv.fullRk k n d × GlobalTheory.FullRankCoinv.fullRk k n d →₀ ℂ) →ₗ[ℂ] ℂ` to `Finsupp.linearCombination ℂ (fun p => Bf p.1 p.2)`. Establish `hker : LinearMap.ker Tm ≤ LinearMap.ker Bm`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Establish `h` using `key k n d F Bf hF hloc x.support (fun p => x p • p.1) (fun p => p.2) (fun Y => by`.

Use `congrFun hx Y` as an intermediate fact. Simplify using `only [Tm, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [Submodule.coe_smul]`.

Rewrite using `[hFs _ p.1.2]`. Simplify using `[mul_assoc])`. Simplify using `only [Bm, Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Set `g : LinearMap.range Tm →ₗ[ℂ] ℂ` to `(LinearMap.ker Tm).liftQ Bm hker ∘ₗ Tm.quotKerEquivRange.symm.toLinearMap`. Take `⟨Λ, hΛ⟩` from `LinearMap.exists_extend g`. Use `⟨Λ, fun Ψ₁ Ψ₂ => ?_⟩` and prove the remaining obligations. Establish `e3 : Tm.quotKerEquivRange.symm ⟨Tm (Finsupp.single (Ψ₁, Ψ₂) 1), LinearMap.mem_range_self _ _⟩ = (LinearMap.ker Tm).mkQ (Finsupp.single (Ψ₁, Ψ₂) 1)` using `LinearMap.quotKerEquivRange_symm_apply_image _ _ _`.

Establish `e1 : Λ (Tm (Finsupp.single (Ψ₁, Ψ₂) 1)) = Bm (Finsupp.single (Ψ₁, Ψ₂) 1)`. Use `LinearMap.congr_fun hΛ ⟨Tm (Finsupp.single (Ψ₁, Ψ₂) 1), LinearMap.mem_range_self _ _⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `Λ (Tm (Finsupp.single (Ψ₁, Ψ₂) 1)) = (LinearMap.ker Tm).liftQ Bm hker (Tm.quotKerEquivRange.symm ⟨Tm (Finsupp.single (Ψ₁, Ψ₂) 1), LinearMap.mem_range_self _ _⟩) at this`. Rewrite using `[this, e3, Submodule.mkQ_apply, Submodule.liftQ_apply]`. Establish `e4 : Tm (Finsupp.single (Ψ₁, Ψ₂) 1) = fun Y => F Ψ₁.1 Y * (starRingEnd ℂ) (Ψ₂.1 Y)`.

Simplify using `[Tm, Finsupp.linearCombination_single]`. Establish `e5 : Bm (Finsupp.single (Ψ₁, Ψ₂) 1) = Bf Ψ₁ Ψ₂`. Simplify using `[Bm, Finsupp.linearCombination_single]`. Rewrite using `[← e5, ← e1, e4]`.
-/
theorem formP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (F : (Matrix (Fin n) (Fin d) k → ℂ) → Matrix (Fin n) (Fin d) k → ℂ)
    (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ),
    (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Ψ' ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ c : ℂ, F (c • Ψ + Ψ') = c • F Ψ + F Ψ') →
    (∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Ψ₂.1 Y ≠ 0 → F Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0) →
    ∃ Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
      Bf Ψ₁ Ψ₂ = Λ (fun Y => F Ψ₁.1 Y * (starRingEnd ℂ) (Ψ₂.1 Y)) := by
  intro k _ _ _ _ n d F Bf hF hloc
  classical
  have hF0 : F 0 = 0 := by
    have := hF 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem 1
    simp at this
    exact this
  have hFs : ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ c : ℂ, F (c • Ψ) = c • F Ψ := by
    intro Ψ hΨ c
    have := hF Ψ hΨ 0 (GlobalTheory.FullRankCoinv.fullRk k n d).zero_mem c
    simpa [hF0] using this
  let Tm : (GlobalTheory.FullRankCoinv.fullRk k n d × GlobalTheory.FullRankCoinv.fullRk k n d →₀ ℂ) →ₗ[ℂ]
      (Matrix (Fin n) (Fin d) k → ℂ) :=
    Finsupp.linearCombination ℂ (fun p => fun Y => F p.1.1 Y * (starRingEnd ℂ) (p.2.1 Y))
  let Bm : (GlobalTheory.FullRankCoinv.fullRk k n d × GlobalTheory.FullRankCoinv.fullRk k n d →₀ ℂ) →ₗ[ℂ] ℂ :=
    Finsupp.linearCombination ℂ (fun p => Bf p.1 p.2)
  have hker : LinearMap.ker Tm ≤ LinearMap.ker Bm := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := key k n d F Bf hF hloc x.support (fun p => x p • p.1) (fun p => p.2) (fun Y => by
      have := congrFun hx Y
      simp only [Tm, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Submodule.coe_smul]
      rw [hFs _ p.1.2]
      simp [mul_assoc])
    simp only [Bm, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp
  let g : LinearMap.range Tm →ₗ[ℂ] ℂ := (LinearMap.ker Tm).liftQ Bm hker ∘ₗ Tm.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend g
  refine ⟨Λ, fun Ψ₁ Ψ₂ => ?_⟩
  have e3 : Tm.quotKerEquivRange.symm ⟨Tm (Finsupp.single (Ψ₁, Ψ₂) 1), LinearMap.mem_range_self _ _⟩ =
      (LinearMap.ker Tm).mkQ (Finsupp.single (Ψ₁, Ψ₂) 1) :=
    LinearMap.quotKerEquivRange_symm_apply_image _ _ _
  have e1 : Λ (Tm (Finsupp.single (Ψ₁, Ψ₂) 1)) = Bm (Finsupp.single (Ψ₁, Ψ₂) 1) := by
    have := LinearMap.congr_fun hΛ ⟨Tm (Finsupp.single (Ψ₁, Ψ₂) 1), LinearMap.mem_range_self _ _⟩
    change Λ (Tm (Finsupp.single (Ψ₁, Ψ₂) 1)) = (LinearMap.ker Tm).liftQ Bm hker
      (Tm.quotKerEquivRange.symm ⟨Tm (Finsupp.single (Ψ₁, Ψ₂) 1), LinearMap.mem_range_self _ _⟩) at this
    rw [this, e3, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have e4 : Tm (Finsupp.single (Ψ₁, Ψ₂) 1) = fun Y => F Ψ₁.1 Y * (starRingEnd ℂ) (Ψ₂.1 Y) := by
    simp [Tm, Finsupp.linearCombination_single]
  have e5 : Bm (Finsupp.single (Ψ₁, Ψ₂) 1) = Bf Ψ₁ Ψ₂ := by
    simp [Bm, Finsupp.linearCombination_single]
  rw [← e5, ← e1, e4]

end GlobalTheory.FullRankLocalForm
