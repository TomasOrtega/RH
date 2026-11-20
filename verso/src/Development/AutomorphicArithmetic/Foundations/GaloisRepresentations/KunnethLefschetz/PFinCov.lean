import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FinLCover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.Gal.KunnethLefschetz.finCov_holds :
    UpperTheory.Gal.KunnethLefschetz.FinCov := by
  unfold UpperTheory.Gal.KunnethLefschetz.FinCov
  intro k _ _ d X p h1 h2 h3
  obtain ⟨π, t, e1, e2, e3, -⟩ := LateralTheory.Fin.LCover.intersectionNumber_baseChange k d p h1 h2 h3
  exact ⟨π, e1, e2, e3⟩
