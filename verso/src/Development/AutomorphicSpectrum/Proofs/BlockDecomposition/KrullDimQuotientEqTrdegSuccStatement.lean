import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSucc
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKrullDimQuotientEqTrdegSucc.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ : ∀ (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B] [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B), CharZero (Y.residueField (j q)) → ringKrullDim (B ⧸ q.asIdeal) = (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | exact GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | (intros; apply GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq <;> assumption)
