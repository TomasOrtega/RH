import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `l _ B Z Y Z' p p' s t hst A`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨W, c, G, i1, hG, a, J, i2, σ, _hh, hrest⟩`. Conclude with `⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩`. Introduce and unpack `⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩`.

Conclude with `⟨W, c, G, i1, hG, a, J, i2, σ, fun j => by rw [Category.assoc, hst, ← Category.assoc, hrest.2.1.1 j], hrest⟩`.
-/
theorem UpperTheory.Gal.G3.pOpEt :
    OpEt := by
  intro l _ B Z Y Z' p p' s t hst A
  constructor
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, _hh, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ,
      fun j => by rw [Category.assoc, hst, ← Category.assoc, hrest.2.1.1 j], hrest⟩
