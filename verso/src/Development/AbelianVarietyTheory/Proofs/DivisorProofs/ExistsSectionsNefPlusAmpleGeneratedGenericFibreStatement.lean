import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionsNefPlusAmpleGeneratedGenericFibre.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  first | exact @GlobalTheory.GenFibreGen.exists_secs_generic | exact GlobalTheory.GenFibreGen.exists_secs_generic | (intros; apply GlobalTheory.GenFibreGen.exists_secs_generic <;> assumption)
