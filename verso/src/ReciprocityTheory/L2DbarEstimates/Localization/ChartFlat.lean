import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.Localization.ChartB

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Introduce `z hz e G D S he hGl hDl hSl hDiv hSw hGc hDc hSc hGs hDs hSs`. Establish `hTc : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S)` using `(hGc.union hDc).union hSc`. Establish `hTs : tsupport G ∪ tsupport D ∪ tsupport S ⊆ e.source` using `union_subset (union_subset hGs hDs) hSs`. Establish `hKc : IsCompact (e '' (tsupport G ∪ tsupport D ∪ tsupport S))` using `hTc.image_of_continuousOn (e.continuousOn.mono hTs)`. Establish `hKt : e '' (tsupport G ∪ tsupport D ∪ tsupport S) ⊆ e.target`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `e.map_source (hTs hx)`. Establish `hK : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport D ∪ tsupport S → y ∈ e '' (tsupport G ∪ tsupport D ∪ tsupport S)` using `fun y hy hT => ⟨e.symm y, hT, e.right_inv hy⟩`. Take `⟨ρ, hρd, hρc, hρt, O, hOo, hKO, h1⟩` from `chT_plateau _ _ hKc e.open_target hKt`. Apply the tactic sequence `have hdivT := chT_div hExt hz he G D hGl.1 hDl.1 hGs hDs hDiv ρ hρd hρc hρt O hOo h1 (fun y hy hT => hKO (hK y hy (by rcases hT with h | h <;> simp [h])))`.

Apply the tactic sequence `have hST := chT_S hExt hz he G S hGl.1 hSl.1 hGs hSs hSw ρ hρd hρc hρt O hOo h1 (fun y hy hT => hKO (hK y hy (by rcases hT with h | h <;> simp [h])))`. Establish `hvan : ∀ y, y ∉ e '' (tsupport G ∪ tsupport D ∪ tsupport S) → e.target.indicator (G ∘ e.symm) y = 0 ∧ e.target.indicator (D ∘ e.symm) y = 0 ∧ e.target.indicator (S ∘ e.symm) y = 0`. Introduce `y hy`. Distinguish the cases in `hyt : y ∈ e.target`. Establish `hn : e.symm y ∉ tsupport G ∪ tsupport D ∪ tsupport S` using `fun h => hy (hK y hyt h)`.

Simplify using `only [indicator_of_mem hyt, Function.comp_apply]`. Apply the tactic sequence `refine ⟨image_eq_zero_of_notMem_tsupport (fun h => hn ?_), image_eq_zero_of_notMem_tsupport (fun h => hn ?_), image_eq_zero_of_notMem_tsupport (fun h => hn ?_)⟩ <;> simp [h]`. Simplify using `[indicator_of_notMem hyt]`. Take `⟨K₀, hK₀c, hK₀t, happ⟩` from `hFlat e.target _ (e.target.indicator (G ∘ e.symm)) (e.target.indicator (D ∘ e.symm)) (e.target.indicator (S ∘ e.symm)) e.open_target hKc hKt hvan (chartTransport_indicator_memLp_two hz he G hGl hGc hGs) (chartTransport_indicator_memLp_two hz he D hDl hDc hDs) (chartTransport_indi …`. Use `⟨e.symm '' K₀, hK₀c.image_of_continuousOn (e.continuousOn_symm.mono hK₀t), fun δ hδ => ?_⟩` and prove the remaining obligations.

Take `⟨G', hG'd, hG'0, hε1, hε2, hε3⟩` from `happ δ hδ`. Conclude with `chT_back hExt hz he G D S hGl.1 hDl.1 hSl.1 hGs hDs hSs K₀ hK₀c hK₀t G' hG'd hG'0 δ hε1 hε2 hε3`.
-/
theorem chartFlat (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hExt : ExtendStatement n M)
    (hFlat : FlatGraphStatement n) :
    ChartFlatStatement n M := by
  intro z hz e G D S he hGl hDl hSl hDiv hSw hGc hDc hSc hGs hDs hSs
  have hTc : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S) := (hGc.union hDc).union hSc
  have hTs : tsupport G ∪ tsupport D ∪ tsupport S ⊆ e.source :=
    union_subset (union_subset hGs hDs) hSs
  have hKc : IsCompact (e '' (tsupport G ∪ tsupport D ∪ tsupport S)) :=
    hTc.image_of_continuousOn (e.continuousOn.mono hTs)
  have hKt : e '' (tsupport G ∪ tsupport D ∪ tsupport S) ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hTs hx)
  have hK : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport D ∪ tsupport S →
      y ∈ e '' (tsupport G ∪ tsupport D ∪ tsupport S) :=
    fun y hy hT => ⟨e.symm y, hT, e.right_inv hy⟩
  obtain ⟨ρ, hρd, hρc, hρt, O, hOo, hKO, h1⟩ := chT_plateau _ _ hKc e.open_target hKt
  have hdivT := chT_div hExt hz he G D hGl.1 hDl.1 hGs hDs hDiv ρ hρd hρc hρt O hOo h1
    (fun y hy hT => hKO (hK y hy (by rcases hT with h | h <;> simp [h])))
  have hST := chT_S hExt hz he G S hGl.1 hSl.1 hGs hSs hSw ρ hρd hρc hρt O hOo h1
    (fun y hy hT => hKO (hK y hy (by rcases hT with h | h <;> simp [h])))
  have hvan : ∀ y, y ∉ e '' (tsupport G ∪ tsupport D ∪ tsupport S) →
      e.target.indicator (G ∘ e.symm) y = 0 ∧ e.target.indicator (D ∘ e.symm) y = 0 ∧
        e.target.indicator (S ∘ e.symm) y = 0 := by
    intro y hy
    by_cases hyt : y ∈ e.target
    · have hn : e.symm y ∉ tsupport G ∪ tsupport D ∪ tsupport S := fun h => hy (hK y hyt h)
      simp only [indicator_of_mem hyt, Function.comp_apply]
      refine ⟨image_eq_zero_of_notMem_tsupport (fun h => hn ?_),
        image_eq_zero_of_notMem_tsupport (fun h => hn ?_),
        image_eq_zero_of_notMem_tsupport (fun h => hn ?_)⟩ <;> simp [h]
    · simp [indicator_of_notMem hyt]
  obtain ⟨K₀, hK₀c, hK₀t, happ⟩ := hFlat e.target _ (e.target.indicator (G ∘ e.symm))
    (e.target.indicator (D ∘ e.symm)) (e.target.indicator (S ∘ e.symm)) e.open_target hKc hKt
    hvan (chartTransport_indicator_memLp_two hz he G hGl hGc hGs) (chartTransport_indicator_memLp_two hz he D hDl hDc hDs)
    (chartTransport_indicator_memLp_two hz he S hSl hSc hSs) (fun φ hφd hφc => hdivT φ hφd hφc)
    (fun φ hφd hφc j k => hST φ hφd hφc j k)
  refine ⟨e.symm '' K₀, hK₀c.image_of_continuousOn (e.continuousOn_symm.mono hK₀t),
    fun δ hδ => ?_⟩
  obtain ⟨G', hG'd, hG'0, hε1, hε2, hε3⟩ := happ δ hδ
  exact chT_back hExt hz he G D S hGl.1 hDl.1 hSl.1 hGs hDs hSs K₀ hK₀c hK₀t G' hG'd hG'0 δ
    hε1 hε2 hε3

end

end ReciprocityTheory.L2DbarEstimates.F
