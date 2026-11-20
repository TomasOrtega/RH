import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem unrPol_neg_one (S : Multiset ℂ) : unrPol S (-1) = rootPol S := by
  simp [unrPol, rootPol]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Int.Geo.phiOf :
    UpperTheory.Gal.Int.Geo.PhiOf := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ w a B _ hK P AI hT A h O _ _ _ Bw hj
  obtain ⟨hc, g, hg, m, hd⟩ := hK P AI hT A h O Bw hj
  refine ⟨hc, g, hg, m, ?_⟩
  rw [UpperTheory.Gal.TP.Sub.satPol_holds E Ω A w h a B g, hg, unrPol_neg_one]
  exact hd
