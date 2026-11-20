import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVariety
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FFlagChainArithVariety.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.flag_chain_arith_variety : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K] (j : K → FlBlock Ψ N), IsChain j → IsArithVar (PPart j) (cellDim j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart <;> assumption)
