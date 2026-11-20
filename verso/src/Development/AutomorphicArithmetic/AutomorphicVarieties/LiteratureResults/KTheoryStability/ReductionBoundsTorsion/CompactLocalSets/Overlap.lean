import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.KB.LocalOverlapAverage

/- English proof (translation)
Introduce `G _ _ _ _ _ _ Γ _ μ _ D hD hfin K hK`. Establish `hT : IsCompact (K * K⁻¹)` using `hK.mul hK.inv`. Establish `hF` using `hfin (K * K⁻¹) hT`. Use `⟨hF.toFinset.card, ?_⟩` and prove the remaining obligations. Introduce `f hf hinv`.

Establish `hKm : MeasurableSet K` using `hK.isClosed.measurableSet`. Establish `hsum : ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) ≤ (hF.toFinset.card : ℝ≥0∞)`. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (γ : G) ∈ K * K⁻¹`.

Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem (show (γ : G) ∈ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from ⟨γ.2, h⟩)]`. Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (show (γ : G) ∉ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from fun h' => h h'.2)]`. Use `_ ≤ ∑' g : G, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _`. Use `_ = ∑ g ∈ hF.toFinset, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g := by`. Use `tsum_eq_sum fun g hg => ?_` and prove the remaining obligations.

Rewrite `hg` using `[Set.Finite.mem_toFinset]`. Conclude with `Set.indicator_of_notMem hg _`. Use `_ ≤ ∑ _g ∈ hF.toFinset, (1 : ℝ≥0∞) := by`. Use `Finset.sum_le_sum fun g _ => ?_` and prove the remaining obligations. Unfold `Set.indicator`.

Apply the tactic sequence `split_ifs <;> simp`. Use `_ = (hF.toFinset.card : ℝ≥0∞) := by simp`. Establish `hcount : ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) ≤ (hF.toFinset.card : ℝ≥0∞)`. Introduce `x`. Distinguish the cases in `hS : ∃ γ₀ : Γ, γ₀ • x ∈ K`.

Take `⟨γ₀, h₀⟩` from `hS`. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.tsum_le_tsum fun γ => ?_` and prove the remaining obligations. Distinguish the cases in `hγ : γ • x ∈ K`. Establish `hmem : ((γ * γ₀⁻¹ : Γ) : G) ∈ K * K⁻¹`.

Use `⟨γ • x, hγ, (γ₀ • x)⁻¹, by rw [Set.mem_inv, inv_inv]; exact h₀, ?_⟩` and prove the remaining obligations. Simplify using `[Subgroup.smul_def, mul_assoc]`. Rewrite using `[Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]`. Rewrite using `[Set.indicator_of_notMem hγ]`. Simplify using the standard rewrite rules.

Use `_ = ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) := (Equiv.mulRight γ₀⁻¹).tsum_eq (fun γ : Γ => (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G))`. Use `_ ≤ _ := hsum`. Use `push_neg at hS`. Combine the equalities or inequalities in the displayed calculation. Establish `hpt : ∀ γ : Γ, ∀ x : G, K.indicator f (γ • x) = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x`.

Introduce `γ x`. Distinguish the cases in `hx : γ • x ∈ K`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]`. Simplify `hinv γ γ.2 x` using `[Subgroup.smul_def]`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]`.

Establish `hmeas : ∀ γ : Γ, Measurable fun x : G => K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x` using `fun γ => ((measurable_const.indicator hKm).comp (measurable_const_smul γ)).mul hf`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_indicator hKm]`. Conclude with `hD.lintegral_eq_tsum'' _`. Use `_ = ∑' γ : Γ, ∫⁻ x in D, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ := by`.

Repeatedly rewrite using `[hpt]`. Use `_ = ∫⁻ x in D, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ := (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm`. Use `_ = ∫⁻ x in D, (∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) * f x ∂μ := by`. Repeatedly rewrite using `[ENNReal.tsum_mul_right]`. Use `_ ≤ ∫⁻ x in D, (hF.toFinset.card : ℝ≥0∞) * f x ∂μ := lintegral_mono fun x => by gcongr; exact hcount x`.

Use `_ = (hF.toFinset.card : ℝ≥0∞) * ∫⁻ x in D, f x ∂μ := lintegral_const_mul _ hf`.
-/
theorem overlapG_holds : OverlapG := by
  intro G _ _ _ _ _ _ Γ _ μ _ D hD hfin K hK
  have hT : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hF := hfin (K * K⁻¹) hT
  refine ⟨hF.toFinset.card, ?_⟩
  intro f hf hinv
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsum : ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    calc ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G)
        = ∑' γ : Γ, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) := by
          refine tsum_congr fun γ => ?_
          by_cases h : (γ : G) ∈ K * K⁻¹
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (γ : G) ∈ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from ⟨γ.2, h⟩)]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (γ : G) ∉ {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹} from fun h' => h h'.2)]
      _ ≤ ∑' g : G, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ∑ g ∈ hF.toFinset, {g : G | g ∈ Γ ∧ g ∈ K * K⁻¹}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
          refine tsum_eq_sum fun g hg => ?_
          rw [Set.Finite.mem_toFinset] at hg
          exact Set.indicator_of_notMem hg _
      _ ≤ ∑ _g ∈ hF.toFinset, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun g _ => ?_
          unfold Set.indicator
          split_ifs <;> simp
      _ = (hF.toFinset.card : ℝ≥0∞) := by simp
  have hcount : ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
      ≤ (hF.toFinset.card : ℝ≥0∞) := by
    intro x
    by_cases hS : ∃ γ₀ : Γ, γ₀ • x ∈ K
    · obtain ⟨γ₀, h₀⟩ := hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)
          ≤ ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) ((γ * γ₀⁻¹ : Γ) : G) := by
            refine ENNReal.tsum_le_tsum fun γ => ?_
            by_cases hγ : γ • x ∈ K
            · have hmem : ((γ * γ₀⁻¹ : Γ) : G) ∈ K * K⁻¹ := by
                refine ⟨γ • x, hγ, (γ₀ • x)⁻¹, by rw [Set.mem_inv, inv_inv]; exact h₀, ?_⟩
                simp [Subgroup.smul_def, mul_assoc]
              rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hmem]
            · rw [Set.indicator_of_notMem hγ]
              simp
        _ = ∑' γ : Γ, (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G) :=
            (Equiv.mulRight γ₀⁻¹).tsum_eq (fun γ : Γ => (K * K⁻¹).indicator (fun _ => (1 : ℝ≥0∞)) (γ : G))
        _ ≤ _ := hsum
    · push_neg at hS
      calc ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) = ∑' _γ : Γ, (0 : ℝ≥0∞) :=
            tsum_congr fun γ => Set.indicator_of_notMem (hS γ) _
        _ ≤ _ := by simp
  have hpt : ∀ γ : Γ, ∀ x : G, K.indicator f (γ • x)
      = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x := by
    intro γ x
    by_cases hx : γ • x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      simpa [Subgroup.smul_def] using hinv γ γ.2 x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hmeas : ∀ γ : Γ, Measurable fun x : G => K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x :=
    fun γ => ((measurable_const.indicator hKm).comp (measurable_const_smul γ)).mul hf
  calc ∫⁻ x in K, f x ∂μ = ∑' γ : Γ, ∫⁻ x in D, K.indicator f (γ • x) ∂μ := by
        rw [← lintegral_indicator hKm]
        exact hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ := by
        simp_rw [hpt]
    _ = ∫⁻ x in D, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) * f x ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) * f x ∂μ := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ x in D, (hF.toFinset.card : ℝ≥0∞) * f x ∂μ :=
        lintegral_mono fun x => by gcongr; exact hcount x
    _ = (hF.toFinset.card : ℝ≥0∞) * ∫⁻ x in D, f x ∂μ := lintegral_const_mul _ hf

end PositivityTheory.KB.LocalOverlapAverage

end
