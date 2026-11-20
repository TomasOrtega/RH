import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagTop.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagVarietyArithDimension.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.flag_variety_arith_dimension : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ), VB.IsVB E r → Nonempty (FlagSp E r) ∧ ∀ F : FlagSp E r, IsArithVar (F.π ≫ p) (d + r.choose 2) ∧ Smooth F.π ∧ ∀ z : X, ∃ y, F.IsTop z y ∧ closure {y} = F.π ⁻¹' closure {z} ∧ ∀ n : ℕ, topologicalKrullDim (closure ({z} : Set X)) = (n : ℕ) → topologicalKrullDim (closure ({y} : Set F.Y)) = (n + r.choose 2 : ℕ) := by
  first | exact @GlobalTheory.FlagTop.main | exact GlobalTheory.FlagTop.main | (intros; apply GlobalTheory.FlagTop.main <;> assumption)
