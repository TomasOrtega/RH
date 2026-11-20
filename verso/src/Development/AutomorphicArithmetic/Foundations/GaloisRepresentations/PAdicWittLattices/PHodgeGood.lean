import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G3.pHodgeGood :
    HodgeTr → HodgeInj → HodgeGood := by
  intro hT hI k _ _ i j
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a h
    obtain ⟨h1, h2, h3, -⟩ := h
    haveI := h1
    haveI := h2
    haveI := h3
    exact hI k i j p r c hc
  · intro Z Y p q s _ _ hs
    exact ⟨hodgeTrace hs i j, hT k i j p q s hs⟩
