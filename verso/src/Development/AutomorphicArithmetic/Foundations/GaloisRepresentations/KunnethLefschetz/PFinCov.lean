import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FinLCover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Unfold `UpperTheory.Gal.KunnethLefschetz.FinCov`. Introduce `k _ _ d X p h1 h2 h3`. Take `⟨π, t, e1, e2, e3, -⟩` from `LateralTheory.Fin.LCover.intersectionNumber_baseChange k d p h1 h2 h3`. Conclude with `⟨π, e1, e2, e3⟩`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.finCov_holds :
    UpperTheory.Gal.KunnethLefschetz.FinCov := by
  unfold UpperTheory.Gal.KunnethLefschetz.FinCov
  intro k _ _ d X p h1 h2 h3
  obtain ⟨π, t, e1, e2, e3, -⟩ := LateralTheory.Fin.LCover.intersectionNumber_baseChange k d p h1 h2 h3
  exact ⟨π, e1, e2, e3⟩
