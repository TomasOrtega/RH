import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.SubstDeg

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Use `MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_monomial]`. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Establish `h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (MvPolynomial.coeff s P)).totalDegree = 0` using `MvPolynomial.totalDegree_C _`. Rewrite using `[h0, zero_add]`. Use `le_trans ?_ (MvPolynomial.le_totalDegree hs)` and prove the remaining obligations. Unfold `Finsupp.prod Finsupp.sum`. Use `(MvPolynomial.totalDegree_finsetProd _ _).trans ?_` and prove the remaining obligations.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_pow _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
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
Introduce `D a b τ ε ε' g k P`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst`. Use `totalDegree_aeval_le _ (fun v => ?_) P` and prove the remaining obligations. Use `split_ifs with h`. Use `MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_` and prove the remaining obligations.

Use `MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le`. Apply the tactic sequence `all_goals first`. Consider the case `exact (MvPolynomial.totalDegree_X _).le`. Consider the case `(refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_`.

Use `MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le)`.
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
