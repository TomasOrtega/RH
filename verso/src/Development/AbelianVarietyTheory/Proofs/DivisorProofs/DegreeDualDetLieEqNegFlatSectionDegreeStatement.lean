import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefPt.degLie_eq_neg_deg_flat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDegreeDualDetLieEqNegFlatSectionDegree.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ (τ : Psi H) (s : FlatSec U ξ Z τ), P.degLie τ.1 = -s.deg) ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 → Dw.mult τ = 0 := by
  first | exact @GlobalTheory.DefPt.degLie_eq_neg_deg_flat | exact GlobalTheory.DefPt.degLie_eq_neg_deg_flat | (intros; apply GlobalTheory.DefPt.degLie_eq_neg_deg_flat <;> assumption)
