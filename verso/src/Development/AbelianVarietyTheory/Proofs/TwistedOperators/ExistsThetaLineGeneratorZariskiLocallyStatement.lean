import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocally
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeEx.exists_secGen_away` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsThetaLineGeneratorZariskiLocally.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_thetaLine_generator_zariski_locally : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  first | exact @GlobalTheory.HeckeEx.exists_secGen_away | exact GlobalTheory.HeckeEx.exists_secGen_away | (intros; apply GlobalTheory.HeckeEx.exists_secGen_away <;> assumption)
