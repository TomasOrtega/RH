import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleTauBimultExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RescaleBimult.exists_rescale_tauBimult` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDegenerationRescaleTauBimultExists.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.degeneration_rescale_tau_bimult_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  first | exact @GlobalTheory.RescaleBimult.exists_rescale_tauBimult | exact GlobalTheory.RescaleBimult.exists_rescale_tauBimult | (intros; apply GlobalTheory.RescaleBimult.exists_rescale_tauBimult <;> assumption)
