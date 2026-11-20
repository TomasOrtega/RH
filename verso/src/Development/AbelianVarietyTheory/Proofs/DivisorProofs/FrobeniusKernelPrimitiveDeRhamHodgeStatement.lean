import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodge
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.frobDR_eq_zero_mem_F1prim` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusKernelPrimitiveDeRhamHodge.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.frobenius_kernel_primitive_de_rham_hodge : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ c : primDR A, frobDR p k hk A c = 0 → c ∈ PrimitiveSubmodule A := by
  first | exact @GlobalTheory.frobDR_eq_zero_mem_F1prim | exact GlobalTheory.frobDR_eq_zero_mem_F1prim | (intros; apply GlobalTheory.frobDR_eq_zero_mem_F1prim <;> assumption)
