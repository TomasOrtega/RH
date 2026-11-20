import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrders
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDiscrepancyEqFormOrderSubWeightedCoordOrders.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum | exact GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum | (intros; apply GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum <;> assumption)
