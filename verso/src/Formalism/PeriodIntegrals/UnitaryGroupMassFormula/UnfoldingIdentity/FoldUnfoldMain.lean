import Mathlib
import Formalism.PeriodIntegrals.FoldUnfold

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace PI.FoldUnfold.UnitaryGroupMassFormula

/- English proof (translation)
Establish `hcov` using `hF.ae_covers`. Establish `hnull : ∀ᵐ y ∂μ, ∀ s t : S, s ≠ t → ¬ ((s : G) * y ∈ F ∧ (t : G) * y ∈ F)`. Rewrite using `[ae_all_iff]`. Introduce `s`. Rewrite using `[ae_all_iff]`.

Introduce `t`. Distinguish the cases in `hst : s = t`. Conclude with `Filter.Eventually.of_forall fun y h => absurd hst h`. Establish `hd : AEDisjoint μ (s⁻¹ • F) (t⁻¹ • F)` using `hF.aedisjoint (inv_injective.ne hst)`. Establish `h0 : μ (s⁻¹ • F ∩ t⁻¹ • F) = 0` using `hd`.

Establish `h1 : ∀ᵐ y ∂μ, y ∉ s⁻¹ • F ∩ t⁻¹ • F` using `ae_iff.mpr (by simpa using h0)`. Use `filter_upwards [h1] with y hy _ hyy`. Apply `hy` to reduce the goal to its premises. Conclude with `⟨by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.1, by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.2⟩`. Use `filter_upwards [hcov, hnull] with y hy huniq`.

Take `⟨g, hg⟩` from `hy`. Rewrite `hg` using `[Subgroup.smul_def, smul_eq_mul]`. Rewrite using `[tsum_eq_single g]`. Simplify using `[Set.indicator_of_mem hg]`. Introduce `b hb`.

Establish `: (b : G) * y ∉ F` using `fun hb' => huniq b g hb ⟨hb', hg⟩`. Simplify using `[Set.indicator_of_notMem this]`.
-/
theorem count_ae_one {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    (S : Subgroup G) [Countable S] (F : Set G) (hF : IsFundamentalDomain S F μ) :
    ∀ᵐ y ∂μ, ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * y) = 1 := by

  have hcov := hF.ae_covers
  have hnull : ∀ᵐ y ∂μ, ∀ s t : S, s ≠ t → ¬ ((s : G) * y ∈ F ∧ (t : G) * y ∈ F) := by
    rw [ae_all_iff]
    intro s
    rw [ae_all_iff]
    intro t
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun y h => absurd hst h
    · have hd : AEDisjoint μ (s⁻¹ • F) (t⁻¹ • F) := hF.aedisjoint (inv_injective.ne hst)
      have h0 : μ (s⁻¹ • F ∩ t⁻¹ • F) = 0 := hd
      have h1 : ∀ᵐ y ∂μ, y ∉ s⁻¹ • F ∩ t⁻¹ • F := ae_iff.mpr (by simpa using h0)
      filter_upwards [h1] with y hy _ hyy
      apply hy
      exact ⟨by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.1,
        by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.2⟩
  filter_upwards [hcov, hnull] with y hy huniq
  obtain ⟨g, hg⟩ := hy
  rw [Subgroup.smul_def, smul_eq_mul] at hg
  rw [tsum_eq_single g]
  · simp [Set.indicator_of_mem hg]
  · intro b hb
    have : (b : G) * y ∉ F := fun hb' => huniq b g hb ⟨hb', hg⟩
    simp [Set.indicator_of_notMem this]

/- English proof (translation)
Introduce `G _ _ _ μ _ Γ S _ hSΓ F hF FΓ hFΓ D hD f hf hfS`. Use `haveI : Countable S := Function.Injective.countable (Subgroup.inclusion_injective hSΓ)`. Use `haveI : Countable D := Function.Injective.countable (f := fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ)) (fun a b h => Subtype.ext (congrArg (fun γ : Γ => (γ : G)) h))`. Establish `hpt : ∀ᵐ x ∂μ, ∑' γ : Γ, F.indicator f ((γ : G) * x) = ∑' δ : D, f ((δ : G) * x)`. Establish `hA : ∀ᵐ x ∂μ, ∀ δ : D, ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * ((δ : G) * x)) = 1`.

Rewrite using `[ae_all_iff]`. Introduce `δ`. Conclude with `(measurePreserving_mul_left μ (δ : G)).quasiMeasurePreserving.ae (count_ae_one μ S F hF)`. Use `filter_upwards [hA] with x hx`. Set `e : S × D → Γ` to `fun p => ⟨(p.1 : G) * p.2, Γ.mul_mem (hSΓ p.1.2) (hD.1 p.2.2)⟩`.

Establish `he : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, δ⟩ ⟨s', δ'⟩ h`. Establish `hγ : ((s : G) * δ) ∈ Γ` using `Γ.mul_mem (hSΓ s.2) (hD.1 δ.2)`. Take `⟨q, _, hq⟩` from `hD.2 _ hγ`.

Establish `h1` using `hq (s, δ) rfl`. Establish `h2` using `hq (s', δ') (congrArg Subtype.val h).symm`. Conclude with `h1.trans h2.symm`. Introduce `γ`. Take `⟨q, hq, _⟩` from `hD.2 γ γ.2`.

Conclude with `⟨q, Subtype.ext hq⟩`. Rewrite using `[← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]`. Use `tsum_congr fun δ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun s => ?_` and prove the remaining obligations.

Use `show F.indicator f ((s : G) * δ * x) = _`. Rewrite using `[mul_assoc, ← hfS s s.2 ((δ : G) * x)]`. Distinguish the cases in `hm : (s : G) * ((δ : G) * x) ∈ F`. Simplify using `[Set.indicator_of_mem hm]`. Simplify using `[Set.indicator_of_notMem hm]`.

Use `_ = f ((δ : G) * x) := by rw [ENNReal.tsum_mul_right, hx δ, one_mul]`. Rewrite using `[← lintegral_indicator₀ hF.nullMeasurableSet, hFΓ.lintegral_eq_tsum'' (F.indicator f), ← lintegral_tsum]`. Apply `lintegral_congr_ae filter_upwards [ae_restrict_of_ae hpt] with x hx` to reduce the goal to its premises. Conclude with `hx.symm`. Introduce `γ`.

Establish `h1 : AEMeasurable (F.indicator f) μ` using `hf.aemeasurable.indicator₀ hF.nullMeasurableSet`. Conclude with `(h1.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict`.
-/
theorem foldUnfold_main : PI.FoldUnfold.FoldUnfold := by
  intro G _ _ _ μ _ Γ S _ hSΓ F hF FΓ hFΓ D hD f hf hfS
  haveI : Countable S := Function.Injective.countable (Subgroup.inclusion_injective hSΓ)
  haveI : Countable D := Function.Injective.countable
    (f := fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ)) (fun a b h => Subtype.ext (congrArg (fun γ : Γ => (γ : G)) h))

  have hpt : ∀ᵐ x ∂μ, ∑' γ : Γ, F.indicator f ((γ : G) * x) = ∑' δ : D, f ((δ : G) * x) := by
    have hA : ∀ᵐ x ∂μ, ∀ δ : D,
        ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * ((δ : G) * x)) = 1 := by
      rw [ae_all_iff]
      intro δ
      exact (measurePreserving_mul_left μ (δ : G)).quasiMeasurePreserving.ae (count_ae_one μ S F hF)
    filter_upwards [hA] with x hx
    let e : S × D → Γ := fun p => ⟨(p.1 : G) * p.2, Γ.mul_mem (hSΓ p.1.2) (hD.1 p.2.2)⟩
    have he : Function.Bijective e := by
      constructor
      · rintro ⟨s, δ⟩ ⟨s', δ'⟩ h
        have hγ : ((s : G) * δ) ∈ Γ := Γ.mul_mem (hSΓ s.2) (hD.1 δ.2)
        obtain ⟨q, _, hq⟩ := hD.2 _ hγ
        have h1 := hq (s, δ) rfl
        have h2 := hq (s', δ') (congrArg Subtype.val h).symm
        exact h1.trans h2.symm
      · intro γ
        obtain ⟨q, hq, _⟩ := hD.2 γ γ.2
        exact ⟨q, Subtype.ext hq⟩
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    refine tsum_congr fun δ => ?_
    calc _ = ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * ((δ : G) * x)) * f ((δ : G) * x) := by
          refine tsum_congr fun s => ?_
          show F.indicator f ((s : G) * δ * x) = _
          rw [mul_assoc, ← hfS s s.2 ((δ : G) * x)]
          by_cases hm : (s : G) * ((δ : G) * x) ∈ F
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
      _ = f ((δ : G) * x) := by rw [ENNReal.tsum_mul_right, hx δ, one_mul]
  rw [← lintegral_indicator₀ hF.nullMeasurableSet, hFΓ.lintegral_eq_tsum'' (F.indicator f),
    ← lintegral_tsum]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hpt] with x hx
    exact hx.symm
  · intro γ
    have h1 : AEMeasurable (F.indicator f) μ := hf.aemeasurable.indicator₀ hF.nullMeasurableSet
    exact (h1.comp_quasiMeasurePreserving
      (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict

end PI.FoldUnfold.UnitaryGroupMassFormula
