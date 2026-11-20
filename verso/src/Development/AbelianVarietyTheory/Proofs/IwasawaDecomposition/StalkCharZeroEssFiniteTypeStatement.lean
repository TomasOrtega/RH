import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteType
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStalkCharZeroEssFiniteType.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.stalk_charZero_essFiniteType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X), CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  first | exact @GlobalTheory.GModStalk.charZero_essFiniteType_stalk | exact GlobalTheory.GModStalk.charZero_essFiniteType_stalk | (intros; apply GlobalTheory.GModStalk.charZero_essFiniteType_stalk <;> assumption)
