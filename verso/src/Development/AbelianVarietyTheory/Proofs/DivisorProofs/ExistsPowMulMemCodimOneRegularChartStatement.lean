import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChart
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPowMulMemCodimOneRegularChart.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  first | exact @GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart | exact GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart | (intros; apply GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart <;> assumption)
