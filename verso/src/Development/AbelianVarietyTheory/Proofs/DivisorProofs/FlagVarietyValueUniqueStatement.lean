import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUnique
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagVarietyValueUnique.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.flag_variety_value_unique : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p), ∀ (z : X) (e : ℕ), (topologicalKrullDim (closure ({z} : Set X)) = (e + 2 : ℕ) → ∃! a, F.IsVal H N z e a) ∧ (topologicalKrullDim (closure ({z} : Set X)) = (e + 3 : ℕ) → ∀ (M : HermLB p) (s : M.B.Sec), z ∈ Out.nonzeroLocus s → ∃! a, F.IsArch H N M s z e a) := by
  first | exact @GlobalTheory.VdmWd.existsUnique_val_arch | exact GlobalTheory.VdmWd.existsUnique_val_arch | (intros; apply GlobalTheory.VdmWd.existsUnique_val_arch <;> assumption)
