import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts

open CategoryTheory Limits AlgebraicGeometry

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.integralGeometricGalois_splitting : UpperTheory.Gal.Int.Geo.SplitOf := by
  intro W X c _ _ Δ _ a ha h
  refine UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts c c Δ a ha ?_
  intro Ω _ _ x y hy
  obtain ⟨δ, hδ, hu⟩ := h Ω x y hy.symm
  exact ⟨δ, hδ.symm, fun δ' hδ' => hu δ' hδ'.symm⟩
