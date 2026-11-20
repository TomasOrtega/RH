import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem span_image_inf_span_image_of_linearIndependent {R V ι : Type} [CommRing R]
    [AddCommGroup V] [Module R V] {w : ι → V} (hw : LinearIndependent R w) (s t : Set ι) :
    Submodule.span R (w '' s) ⊓ Submodule.span R (w '' t) = Submodule.span R (w '' (s ∩ t)) := by
  apply le_antisymm
  · rintro x ⟨hs, ht⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hs
    obtain ⟨m, hm, hmx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 ht
    have hlm : l = m := hw (hlx.trans hmx.symm)
    subst hlm
    refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨l, ?_, hlx⟩
    rw [Finsupp.mem_supported] at hl hm ⊢
    exact Set.subset_inter hl hm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem span_inf_sup_overlapping_parts :
    ∀ (R V α β γ : Type) [CommRing R] [AddCommGroup V] [Module R V] (w : α ⊕ β ⊕ γ → V),
      LinearIndependent R w →
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊓
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range (w ∘ Sum.inl)) ∧
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊔
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range w) := by
  intro R V α β γ _ _ _ w hw
  constructor
  · rw [Set.range_comp, Set.range_comp, Set.range_comp,
      span_image_inf_span_image_of_linearIndependent hw]
    congr 2
    ext x
    rcases x with a | b | c <;> simp
  · rw [← Submodule.span_union, Set.range_comp, Set.range_comp, ← Set.image_union,
      show (Set.range (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) ∪
          Set.range (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) = Set.univ from by
        ext x
        rcases x with a | b | c <;> simp, Set.image_univ]

end GlobalTheory
