import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.Geo.levD :
    LevD := by
  intro E _ _ _ a U Ξ q α hα
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, hc, hg⟩ := (levGood E a ho U Ξ q).1 α hα
  have hom := omGood _ _ _ _ (geo ho U Ξ) 0 (isFlow_zero _) q
  refine ⟨?_, fun β hβ => ?_⟩
  · obtain ⟨α', hc', hl⟩ := (levGood E a ho U Ξ (q + 1)).2 _ (hom.1 w hg).2
    rw [(corrUniq E a ho U Ξ (q + 1)).1 _ _ _ (corrD E a ho U Ξ q α w hc) hc']
    exact hl
  · obtain ⟨w', hc', hg'⟩ := (levGood E a ho U Ξ q).1 β hβ
    obtain ⟨γ, hc'', hl⟩ := (levGood E a ho U Ξ q).2 _ (hom.2.1 w w' hg hg')
    have hs : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
      rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← hc g x X, ← hc' g x X]
      rfl
    rw [(corrUniq E a ho U Ξ q).1 _ _ _ hs hc'']
    exact hl
