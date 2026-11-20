import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hD Z Y s _ _ d h`. Take `⟨W, c, G, iG, fG, a, σ, hg, hs⟩` from `hD s d ⟨inferInstance, inferInstance, h⟩`. Conclude with `⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hg, hs⟩`.
-/
theorem UpperTheory.Gal.G3.pGalClos :
    GalClosD → GalClos := by
  intro hD Z Y s _ _ d h
  obtain ⟨W, c, G, iG, fG, a, σ, hg, hs⟩ := hD s d ⟨inferInstance, inferInstance, h⟩
  exact ⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hg, hs⟩
