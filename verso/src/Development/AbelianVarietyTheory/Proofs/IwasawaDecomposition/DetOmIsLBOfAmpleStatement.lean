import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOmIsLBOfAmple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolDet.isLB_detOm_of_ample` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDetOmIsLBOfAmple.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.detOm_isLB_of_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (m : ℕ) (BD : GlobalTheory.EffCartierData Y.X), GlobalTheory.IsAmpleLB (polOf Y m BD) → (GlobalTheory.FlagMod.detOm Y).IsLB := by
  first | exact @GlobalTheory.PolDet.isLB_detOm_of_ample | exact GlobalTheory.PolDet.isLB_detOm_of_ample | (intros; apply GlobalTheory.PolDet.isLB_detOm_of_ample <;> assumption)
