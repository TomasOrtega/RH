import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPolarizationPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurveRootGeometry.polPart_closedFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsReductionPolarizationPart.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.exists_reduction_polarization_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Formalism.L2.Pj.CDVR) (t : SAB H (Sp W.V)) (P : PELUnif (IsLocalRing.maximalIdeal W.V) t), ∃ (G₀ : Over (Sp (IsLocalRing.ResidueField W.V))) (_ : GrpObj G₀) (i₀ : OAct (𝓞 E) G₀) (φ₀ : G₀.left ⟶ t.G.left), IsActPull i₀ t.act (spMap (IsLocalRing.residue W.V)) φ₀ ∧ PolPart (H.bar : 𝓞 E →+* 𝓞 E) i₀ := by
  first | exact @GlobalTheory.CurveRootGeometry.polPart_closedFibre | exact GlobalTheory.CurveRootGeometry.polPart_closedFibre | (intros; apply GlobalTheory.CurveRootGeometry.polPart_closedFibre <;> assumption)
