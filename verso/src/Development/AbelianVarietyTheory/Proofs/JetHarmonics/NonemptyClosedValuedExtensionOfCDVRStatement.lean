import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharDepth.nonempty_valExt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FNonemptyClosedValuedExtensionOfCDVR.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.nonempty_closedValuedExtensionOfCDVR : ∀ (T : CDVR) (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : T.V) → Nonempty (ValExt T p) := by
  first | exact @GlobalTheory.CharDepth.nonempty_valExt | exact GlobalTheory.CharDepth.nonempty_valExt | (intros; apply GlobalTheory.CharDepth.nonempty_valExt <;> assumption)
