import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLastSideLogBound.lean&line=280#L280)
-/
theorem _root_.GlobalTheory.T.last_side_log_bound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound → ∀ (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R 25 (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide | exact GlobalTheory.ColRows.LastSideProof.lastSide | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide <;> assumption)
