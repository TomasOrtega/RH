import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.SubstDeg

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem totalDegree_aeval_le {σ κ : Type*} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (MvPolynomial.coeff s P)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem totalDegree_subst_le : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P).totalDegree ≤ P.totalDegree := by
  intro D a b τ ε ε' g k P
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs with h
  · refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
    refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le
  all_goals first
    | exact (MvPolynomial.totalDegree_X _).le
    | (refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
       refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
       exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le)

end GlobalTheory.Chain.RealIt.SubstDeg
