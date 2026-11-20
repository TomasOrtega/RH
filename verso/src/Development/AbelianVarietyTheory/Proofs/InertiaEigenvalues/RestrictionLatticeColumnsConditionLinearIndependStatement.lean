import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndepend
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRestrictionLatticeColumnsConditionLinearIndepend.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  first | exact @GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | exact GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | (intros; apply GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent <;> assumption)
