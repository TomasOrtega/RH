import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FundFrames

open scoped Pointwise

/- English proof (translation)
Introduce `E _ _ _ r X c hH x0 ho FF hF Λ hΛ`. Use `FundSetPf.countable_GL (E := E) (r := r)` as an intermediate fact. Use `set S := GlobalTheory.Unfold.satFrames X x0 FF with hSdef`. Establish `hS : MeasurableSet S` using `GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1`. Establish `hmemT : ∀ (s : Λ) (g : RealGrp X) (γ : GL (Fin r) E), lact γ (baseFr X) = frameOf X s → (g ∈ s • (frameOf X ⁻¹' S) ↔ lact γ⁻¹ (frameOf X g) ∈ S)`.

Introduce `s g γ e`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]`. Establish `h1 : lact γ (frameOf X (s⁻¹ • g)) = frameOf X g`. Rewrite using `[GlobalTheory.PeterssonCompare.lact_frameOf X e, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv, mul_inv_cancel_left]`. Establish `h2 : frameOf X (s⁻¹ • g) = lact γ⁻¹ (frameOf X g)`.

Rewrite using `[← h1, FundSetPf.lact_inv]`. Rewrite using `[h2]`. Use `⟨(GlobalTheory.PeterssonCompare.measurable_frameOf X hS).nullMeasurableSet, ?_, ?_⟩` and prove the remaining obligations. Use `set G' : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun y => lact (γ.1)⁻¹ y) ⁻¹' S with hG'def`. Establish `hG' : MeasurableSet G'` using `MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable hS`.

Establish `hmemG : ∀ y, y ∈ G' ↔ ∃ γ ∈ X.Γ, lact γ⁻¹ y ∈ S`. Introduce `y`. Simplify using `only [G', Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, hy⟩`.

Conclude with `⟨γ.1, γ.2, hy⟩`. Introduce and unpack `⟨γ, hγ, hy⟩`. Conclude with `⟨⟨γ, hγ⟩, hy⟩`. Establish `hGB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ G' ↔ y ∈ G'`. Introduce `y b hb`.

Simplify using `only [hmemG, FundSetPf.lact_rmul, hSdef, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF _ hb]`. Use `set φ : Frame X.Ψ r → ℝ≥0∞ := G'ᶜ.indicator 1 with hφdef`. Establish `hφm : Measurable φ` using `measurable_const.indicator hG'.compl`. Establish `hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x`. Introduce `x _ b hb`.

Establish `hiff : rmul x b ∈ G'ᶜ ↔ x ∈ G'ᶜ`. Simplify using `only [Set.mem_compl_iff, hGB x b hb]`. Distinguish the cases in `hx : x ∈ G'ᶜ`. Rewrite using `[hφdef, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]`. Both sides reduce to the same expression.

Rewrite using `[hφdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hiff.1 h'))]`. Establish `hbo : IsOrth X (baseFr X)` using `fun τ => baseFr_mem X τ`. Establish `h1 : GlobalTheory.SubgroupUnfold.IsIsom X.Gm (1 : GL (Fin r) E)`. Introduce `v w`. Simplify using the standard rewrite rules.

Establish `hae` using `GlobalTheory.SubgroupUnfold.ae_mem_orbit_satFrames X ho hF hbo h1`. Establish `hz : ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) = 0`. Rewrite using `[← lintegral_zero (μ := muF X (baseFr X))]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with z hz`.

Take `⟨γ, hγ, hm⟩` from `hz`. Rewrite `hm` using `[mul_one]`. Establish `: cpt X (baseFr X) z ∉ G'ᶜ`. Rewrite using `[Set.mem_compl_iff, not_not, hmemG]`. Conclude with `⟨γ, hγ, hm⟩`.

Use `show φ _ = 0`. Rewrite using `[hφdef, Set.indicator_of_notMem this]`. Establish `hint` using `hH φ hφm hφB`. Rewrite `hint` using `[hz, mul_zero]`. Establish `hae2` using `(lintegral_eq_zero_iff (hφm.comp (GlobalTheory.PeterssonCompare.measurable_frameOf X))).1 hint`.

Use `filter_upwards [hae2] with g hg`. Establish `hg' : φ (frameOf X g) = 0` using `hg`. Establish `hn : frameOf X g ∉ G'ᶜ` using `fun hm => by`. Rewrite `hg'` using `[hφdef, Set.indicator_of_mem hm]`. Conclude with `one_ne_zero hg'`.

Rewrite `hn` using `[Set.mem_compl_iff, not_not, hmemG]`. Take `⟨γ, hγ, hm⟩` from `hn`. Take `⟨s, hs⟩` from `GlobalTheory.PeterssonCompare.exists_translation X (X.Γ.inv_mem hγ)`. Use `⟨⟨s, (hΛ s).2 ⟨γ⁻¹, X.Γ.inv_mem hγ, hs⟩⟩, ?_⟩` and prove the remaining obligations. Use `show frameOf X (s * g) ∈ S`.

Rewrite using `[← GlobalTheory.PeterssonCompare.lact_frameOf X hs]`. Conclude with `hm`. Introduce `s t hst`. Use `Disjoint.aedisjoint (Set.disjoint_left.2 fun g hgs hgt => hst ?_)` and prove the remaining obligations. Take `⟨γ, hγ, e⟩` from `(hΛ s).1 s.2`.

Take `⟨γ', hγ', e'⟩` from `(hΛ t).1 t.2`. Establish `h1` using `(hmemT s g γ e).1 hgs`. Establish `h2` using `(hmemT t g γ' e').1 hgt`. Take `rfl` from `GlobalTheory.Unfold.unique_translate X hF hγ hγ' h1 h2`. Conclude with `Subtype.ext (GlobalTheory.PeterssonCompare.frameOf_injective X (e.symm.trans e'))`.
-/
theorem isFundamentalDomain_satFrames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  intro E _ _ _ r X c hH x0 ho FF hF Λ hΛ
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  set S := GlobalTheory.Unfold.satFrames X x0 FF with hSdef
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1

  have hmemT : ∀ (s : Λ) (g : RealGrp X) (γ : GL (Fin r) E), lact γ (baseFr X) = frameOf X s →
      (g ∈ s • (frameOf X ⁻¹' S) ↔ lact γ⁻¹ (frameOf X g) ∈ S) := by
    intro s g γ e
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
    have h1 : lact γ (frameOf X (s⁻¹ • g)) = frameOf X g := by
      rw [GlobalTheory.PeterssonCompare.lact_frameOf X e, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv,
        mul_inv_cancel_left]
    have h2 : frameOf X (s⁻¹ • g) = lact γ⁻¹ (frameOf X g) := by
      rw [← h1, FundSetPf.lact_inv]
    rw [h2]
  refine ⟨(GlobalTheory.PeterssonCompare.measurable_frameOf X hS).nullMeasurableSet, ?_, ?_⟩
  ·
    set G' : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun y => lact (γ.1)⁻¹ y) ⁻¹' S with hG'def
    have hG' : MeasurableSet G' :=
      MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable hS
    have hmemG : ∀ y, y ∈ G' ↔ ∃ γ ∈ X.Γ, lact γ⁻¹ y ∈ S := by
      intro y
      simp only [G', Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨γ, hy⟩; exact ⟨γ.1, γ.2, hy⟩
      · rintro ⟨γ, hγ, hy⟩; exact ⟨⟨γ, hγ⟩, hy⟩
    have hGB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ G' ↔ y ∈ G' := by
      intro y b hb
      simp only [hmemG, FundSetPf.lact_rmul, hSdef, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF _ hb]
    set φ : Frame X.Ψ r → ℝ≥0∞ := G'ᶜ.indicator 1 with hφdef
    have hφm : Measurable φ := measurable_const.indicator hG'.compl
    have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := by
      intro x _ b hb
      have hiff : rmul x b ∈ G'ᶜ ↔ x ∈ G'ᶜ := by
        simp only [Set.mem_compl_iff, hGB x b hb]
      by_cases hx : x ∈ G'ᶜ
      · rw [hφdef, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]; rfl
      · rw [hφdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hiff.1 h'))]
    have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
    have h1 : GlobalTheory.SubgroupUnfold.IsIsom X.Gm (1 : GL (Fin r) E) := by
      intro v w; simp
    have hae := GlobalTheory.SubgroupUnfold.ae_mem_orbit_satFrames X ho hF hbo h1
    have hz : ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) = 0 := by
      rw [← lintegral_zero (μ := muF X (baseFr X))]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with z hz
      obtain ⟨γ, hγ, hm⟩ := hz
      rw [mul_one] at hm
      have : cpt X (baseFr X) z ∉ G'ᶜ := by
        rw [Set.mem_compl_iff, not_not, hmemG]; exact ⟨γ, hγ, hm⟩
      show φ _ = 0
      rw [hφdef, Set.indicator_of_notMem this]
    have hint := hH φ hφm hφB
    rw [hz, mul_zero] at hint
    have hae2 := (lintegral_eq_zero_iff (hφm.comp (GlobalTheory.PeterssonCompare.measurable_frameOf X))).1 hint
    filter_upwards [hae2] with g hg
    have hg' : φ (frameOf X g) = 0 := hg
    have hn : frameOf X g ∉ G'ᶜ := fun hm => by
      rw [hφdef, Set.indicator_of_mem hm] at hg'; exact one_ne_zero hg'
    rw [Set.mem_compl_iff, not_not, hmemG] at hn
    obtain ⟨γ, hγ, hm⟩ := hn
    obtain ⟨s, hs⟩ := GlobalTheory.PeterssonCompare.exists_translation X (X.Γ.inv_mem hγ)
    refine ⟨⟨s, (hΛ s).2 ⟨γ⁻¹, X.Γ.inv_mem hγ, hs⟩⟩, ?_⟩
    show frameOf X (s * g) ∈ S
    rw [← GlobalTheory.PeterssonCompare.lact_frameOf X hs]
    exact hm
  ·
    intro s t hst
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun g hgs hgt => hst ?_)
    obtain ⟨γ, hγ, e⟩ := (hΛ s).1 s.2
    obtain ⟨γ', hγ', e'⟩ := (hΛ t).1 t.2
    have h1 := (hmemT s g γ e).1 hgs
    have h2 := (hmemT t g γ' e').1 hgt
    obtain rfl := GlobalTheory.Unfold.unique_translate X hF hγ hγ' h1 h2
    exact Subtype.ext (GlobalTheory.PeterssonCompare.frameOf_injective X (e.symm.trans e'))

end GlobalTheory.FundFrames
