import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j hj hG Z w g`. Take `⟨hL, -, -, hA⟩` from `evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c`. Establish `hg : (g : T.R j) ∈ T.C j w` using `cutR_le T.C j w g.2`. Take `⟨g', hg', h1, h0⟩` from `exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _ (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg`. Establish `hm : g' ∈ cutR T.C j w`.

Rewrite using `[cutR_eq T.C hj]`. Conclude with `hg'`. Conclude with `⟨⟨g', hm⟩, h1, h0⟩`.
-/
theorem compSplit_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c), CompSplitSt h j hG := by
  intro D T h j hj hG Z w g
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hg : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  obtain ⟨g', hg', h1, h0⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg
  have hm : g' ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact hg'
  exact ⟨⟨g', hm⟩, h1, h0⟩

end GlobalTheory.Reg
