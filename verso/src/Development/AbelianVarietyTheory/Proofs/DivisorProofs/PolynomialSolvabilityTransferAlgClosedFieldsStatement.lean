import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFields
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PointTransfer.solvable_transfer` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialSolvabilityTransferAlgClosedFields.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields : ∀ (F σ τ : Type) [Field F] [Finite σ] [Finite τ] (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F)), (∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω), (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  first | exact @GlobalTheory.PointTransfer.solvable_transfer | exact GlobalTheory.PointTransfer.solvable_transfer | (intros; apply GlobalTheory.PointTransfer.solvable_transfer <;> assumption)
