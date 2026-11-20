import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hT hI k _ _ i j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `Z W p r c hc G _ _ a h`. Take `⟨h1, h2, h3, -⟩` from `h`. Use `haveI := h1`.

Use `haveI := h2`. Use `haveI := h3`. Conclude with `hI k i j p r c hc`. Introduce `Z Y p q s _ _ hs`. Conclude with `⟨hodgeTrace hs i j, hT k i j p q s hs⟩`.
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
