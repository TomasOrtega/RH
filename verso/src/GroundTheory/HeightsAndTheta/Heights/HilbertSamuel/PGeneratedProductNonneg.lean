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
Establish `key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W`. Introduce `s hs`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs`. Rewrite `hs` using `[Finsupp.ofSupportFinite_coe]`. Use `split_ifs at hs with h`.

Conclude with `le_sup_left.trans h.1.1.2`. Conclude with `absurd rfl hs`. Rewrite `hW` using `[Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply, Finsupp.mapRange_apply]`. Distinguish the cases in `hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0`. Use `key g fun h => hW ?_` and prove the remaining obligations.

Rewrite using `[hf, h]`. Simplify using the standard rewrite rules. Conclude with `key f hf`.
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
Introduce `F _ K _ _ ι _ _ I V m β hI hV hgen`. Proceed by induction on `m generalizing V with`. Consider the case `zero => choose i hi using hV.1.2.2`. Rewrite using `[hI.1 V β i hV hi]`. Conclude with `Int.natCast_nonneg _`.

Consider the case `succ m ih`. Take `⟨f, g, hs, heff⟩` from `hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))`. Establish `e` using `hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs`. Rewrite `e` using `[Fin.snoc_init_self]`. Rewrite using `[e, cycEval]`.

Use `Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_` and prove the remaining obligations. Take `⟨α, γ, hf, hg, hfV, hgV, -⟩` from `hs`. Establish `hWm : IsProjVarF W m` using `KleimanNefF.isProjVarF_of_mem_support hV ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg) hfV hgV hW`. Establish `hle : V ≤ W` using `GeneratedProductNonneg.le_of_mem_support_ratDiv hW`. Conclude with `ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)`.
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
