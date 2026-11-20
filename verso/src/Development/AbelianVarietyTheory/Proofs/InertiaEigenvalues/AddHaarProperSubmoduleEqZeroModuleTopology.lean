import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Set Pointwise Metric

namespace GlobalTheory.HaarNullSub

/- English proof (translation)
Use `haveI := hμ`. Use `haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`. Use `haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V`. Use `haveI : ContinuousSMul F V := inferInstance`. Set `e₀ : V ≃ₗ[F] (Fin (Module.finrank F V) → F)` to `(Module.finBasis F V).equivFun`.

Establish `hc : Continuous e₀` using `IsModuleTopology.continuous_of_linearMap e₀.toLinearMap`. Establish `hc' : Continuous e₀.symm` using `IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap`. Set `h : V ≃ₜ (Fin (Module.finrank F V) → F)` to `{ e₀.toEquiv with continuous_toFun := hc, continuous_invFun := hc' }`. Establish `hcl : IsClosed (s : Set V)`. Establish `h1 : IsClosed ((s.map e₀.toLinearMap : Submodule F _) : Set (Fin (Module.finrank F V) → F))` using `Submodule.closed_of_finiteDimensional _`.

Establish `h2 : (s : Set V) = h ⁻¹' ((s.map e₀.toLinearMap : Submodule F _) : Set _)`. Use extensionality with `v`. Simplify using `[h, Submodule.mem_map]`. Rewrite using `[h2]`. Conclude with `h1.preimage h.continuous`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, x ∉ s := by`. Simplify `hs` using `only [Submodule.eq_top_iff', not_exists, Ne, not_forall]`. Take `⟨c, c0, c1⟩` from `NormedField.exists_norm_lt_one F`. Set `u : ℕ → V` to `fun n => c ^ n • x`. Establish `hu : Tendsto u atTop (𝓝 0)`.

Establish `: Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_norm_lt_one c1`. Simplify `this.smul_const x` using `[u]`. Establish `hC : IsCompact (insert 0 (range u))` using `hu.isCompact_insert_range`. Establish `hdisj : ∀ A ⊆ (s : Set V), Pairwise (Function.onFun Disjoint fun n => {u n} + A)`. Introduce `A hA m n hmn`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `_ ⟨_, rfl, a, ha, rfl⟩ ⟨_, rfl, b, hb, hab⟩`. Apply `hx` to reduce the goal to its premises. Establish `hne : c ^ m - c ^ n ≠ 0`. Introduce `h0`.

Apply `hmn` to reduce the goal to its premises. Establish `: ‖c‖ ^ m = ‖c‖ ^ n` using `by rw [← norm_pow, ← norm_pow, sub_eq_zero.mp h0]`. Conclude with `pow_right_injective₀ c0 (ne_of_lt c1) this.symm |>.symm`. Establish `hmem : (c ^ m - c ^ n) • x ∈ s`. Establish `: (c ^ m - c ^ n) • x = b - a`.

Simplify using `only [u] at hab`. Rewrite using `[sub_smul, show c ^ m • x = c ^ n • x + b - a by rw [hab]; abel]; abel`. Rewrite using `[this]`. Conclude with `s.sub_mem (hA hb) (hA ha)`. Conclude with `(Submodule.smul_mem_iff s hne).mp hmem`.

Establish `key : ∀ R : ℝ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 R) = 0`. Introduce `R`. Use `set A := (s : Set V) ∩ h ⁻¹' closedBall 0 R with hAdef`. Establish `hAc : IsCompact A`. Establish `hK : IsCompact (h ⁻¹' closedBall 0 R)`.

Rewrite using `[← h.image_symm]`. Conclude with `(isCompact_closedBall (0 : Fin (Module.finrank F V) → F) R).image h.symm.continuous`. Conclude with `hK.inter_left hcl`. Establish `hAm : MeasurableSet A` using `hcl.measurableSet.inter (isClosed_closedBall.preimage h.continuous).measurableSet`. Assume the negation of the conclusion as `hne`.

Apply `lt_irrefl (⊤ : ENNReal)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use `ext1 n`. Simplify using `only [image_add_left, measure_preimage_add, singleton_add]`.

Use `_ = μ (⋃ n, {u n} + A) := Eq.symm <| measure_iUnion (hdisj A inter_subset_left) fun n => by`. Simplify `(measurable_const_add (-u n)) hAm` using `only [image_add_left, singleton_add]`. Use `_ ≤ μ (insert 0 (range u) + A) := by`. Apply `measure_mono` to reduce the goal to its premises. Use `iUnion_subset fun n => add_subset_add ?_ Subset.rfl` and prove the remaining obligations.

Conclude with `singleton_subset_iff.mpr (mem_insert_of_mem _ (mem_range_self n))`. Use `_ < ⊤ := (hC.add hAc).measure_lt_top`. Rewrite using `[← nonpos_iff_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `measure_iUnion_le _`.

Use `_ = 0 := by simp only [key, tsum_zero]`.
-/
theorem addHaar_submodule_eq_zero (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V]
    [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    (hμ : μ.IsAddHaarMeasure) (s : Submodule F V) (hs : s ≠ ⊤) : μ (s : Set V) = 0 := by
  haveI := hμ
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousSMul F V := inferInstance

  let e₀ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e₀ := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
  have hc' : Continuous e₀.symm := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) :=
    { e₀.toEquiv with continuous_toFun := hc, continuous_invFun := hc' }

  have hcl : IsClosed (s : Set V) := by
    have h1 : IsClosed ((s.map e₀.toLinearMap : Submodule F _) : Set (Fin (Module.finrank F V) → F)) :=
      Submodule.closed_of_finiteDimensional _
    have h2 : (s : Set V) = h ⁻¹' ((s.map e₀.toLinearMap : Submodule F _) : Set _) := by
      ext v
      simp [h, Submodule.mem_map]
    rw [h2]; exact h1.preimage h.continuous

  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, c0, c1⟩ := NormedField.exists_norm_lt_one F
  let u : ℕ → V := fun n => c ^ n • x
  have hu : Tendsto u atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one c1
    simpa [u] using this.smul_const x
  have hC : IsCompact (insert 0 (range u)) := hu.isCompact_insert_range

  have hdisj : ∀ A ⊆ (s : Set V), Pairwise (Function.onFun Disjoint fun n => {u n} + A) := by
    intro A hA m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨_, rfl, a, ha, rfl⟩ ⟨_, rfl, b, hb, hab⟩
    apply hx
    have hne : c ^ m - c ^ n ≠ 0 := by
      intro h0
      apply hmn
      have : ‖c‖ ^ m = ‖c‖ ^ n := by rw [← norm_pow, ← norm_pow, sub_eq_zero.mp h0]
      exact pow_right_injective₀ c0 (ne_of_lt c1) this.symm |>.symm
    have hmem : (c ^ m - c ^ n) • x ∈ s := by
      have : (c ^ m - c ^ n) • x = b - a := by
        simp only [u] at hab
        rw [sub_smul, show c ^ m • x = c ^ n • x + b - a by rw [hab]; abel]; abel
      rw [this]; exact s.sub_mem (hA hb) (hA ha)
    exact (Submodule.smul_mem_iff s hne).mp hmem

  have key : ∀ R : ℝ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 R) = 0 := by
    intro R
    set A := (s : Set V) ∩ h ⁻¹' closedBall 0 R with hAdef
    have hAc : IsCompact A := by
      have hK : IsCompact (h ⁻¹' closedBall 0 R) := by
        rw [← h.image_symm]
        exact (isCompact_closedBall (0 : Fin (Module.finrank F V) → F) R).image h.symm.continuous
      exact hK.inter_left hcl
    have hAm : MeasurableSet A := hcl.measurableSet.inter (isClosed_closedBall.preimage h.continuous).measurableSet
    by_contra hne
    apply lt_irrefl (⊤ : ENNReal)
    calc
      (⊤ : ENNReal) = ∑' _ : ℕ, μ A := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
      _ = ∑' n : ℕ, μ ({u n} + A) := by
        congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
      _ = μ (⋃ n, {u n} + A) := Eq.symm <| measure_iUnion (hdisj A inter_subset_left) fun n => by
        simpa only [image_add_left, singleton_add] using (measurable_const_add (-u n)) hAm
      _ ≤ μ (insert 0 (range u) + A) := by
        apply measure_mono
        refine iUnion_subset fun n => add_subset_add ?_ Subset.rfl
        exact singleton_subset_iff.mpr (mem_insert_of_mem _ (mem_range_self n))
      _ < ⊤ := (hC.add hAc).measure_lt_top
  rw [← nonpos_iff_eq_zero]
  calc
    μ (s : Set V) ≤ ∑' n : ℕ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 n) := by
      conv_lhs => rw [← inter_univ (s : Set V), ← preimage_univ (f := h), ← iUnion_closedBall_nat 0,
        preimage_iUnion, inter_iUnion]
      exact measure_iUnion_le _
    _ = 0 := by simp only [key, tsum_zero]

end GlobalTheory.HaarNullSub
