import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedProductNonneg

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem le_of_mem_support_ratDiv {V : Ideal (MRingOver F ι)} {f g : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (hW : W ∈ (ratDiv V f g).support) : V ≤ W := by
  have key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W := by
    intro s hs
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs
    rw [Finsupp.ofSupportFinite_coe] at hs
    split_ifs at hs with h
    · exact le_sup_left.trans h.1.1.2
    · exact absurd rfl hs
  rw [Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g fun h => hW ?_
    rw [hf, h]
    simp
  · exact key f hf

end GeneratedProductNonneg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem GeneratedProductNonneg.proof (hR : GeneratedRestrict.Statement)
    (hE : GeneratedEffectiveSection.Statement) : GeneratedProductNonneg.Statement := by
  classical
  intro F _ K _ _ ι _ _ I V m β hI hV hgen
  induction m generalizing V with
  | zero =>
    choose i hi using hV.1.2.2
    rw [hI.1 V β i hV hi]
    exact Int.natCast_nonneg _
  | succ m ih =>
    obtain ⟨f, g, hs, heff⟩ := hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))
    have e := hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs
    rw [Fin.snoc_init_self] at e
    rw [e, cycEval]
    refine Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_
    obtain ⟨α, γ, hf, hg, hfV, hgV, -⟩ := hs
    have hWm : IsProjVarF W m := KleimanNefF.isProjVarF_of_mem_support hV
      ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg)
      hfV hgV hW
    have hle : V ≤ W := GeneratedProductNonneg.le_of_mem_support_ratDiv hW
    exact ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
