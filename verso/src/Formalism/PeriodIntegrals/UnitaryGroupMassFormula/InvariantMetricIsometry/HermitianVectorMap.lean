import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.MetricConstantBound

noncomputable section

open Matrix Finset PI.IsoInvMetric

namespace PI.IsoInvMetricW

/- English proof (translation)
Repeatedly rewrite using `[Fintype.prod_sum]`. Both sides reduce to the same expression.
-/
theorem sum_prod_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
    (F : ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), (Fin ((nu s).colLen c) ↪o Fin N) → ℂ) :
    ∑ J : ColChoice N nu, ∏ s, ∏ c, F s c (J s c) = ∏ s, ∏ c, ∑ K, F s c K := by
  simp_rw [Fintype.prod_sum]
  rfl

/- English proof (translation)
Introduce `Lt _ _ N nu f x`. Use function extensionality and compare the values at `I`. Simplify using `only [VnuMap, hvC, minY, fr]`. Rewrite using `[finsum_eq_sum_of_fintype]`. Repeatedly rewrite using `[← Finset.prod_mul_distrib]`.

Use `(sum_prod_cc (fun s c K => (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (K k)).det * (Matrix.of fun i j : Fin ((nu s).colLen c) => x s (K i) (j : ℕ)).det)).trans ?_` and prove the remaining obligations. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hcb` using `metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b) (Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ))`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.
-/
theorem hermitian_vector_map : HvMap := by
  intro Lt _ _ N nu f x
  funext I
  simp only [VnuMap, hvC, minY, fr]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c K =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (K k)).det *
      (Matrix.of fun i j : Fin ((nu s).colLen c) => x s (K i) (j : ℕ)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ))
  calc _ = ∑ K : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id K).det *
        ((Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ)).submatrix K id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1

/- English proof (translation)
Introduce `Lt _ _ N nu f g I K`. Simplify using `only [E]`. Repeatedly rewrite using `[← Finset.prod_mul_distrib]`. Use `(sum_prod_cc (fun s c J => (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J k)).det * (Matrix.of fun i k : Fin ((nu s).colLen c) => g s (J i) (K s c k)).det)).trans ?_` and prove the remaining obligations. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations.

Establish `hcb` using `metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b) (Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k))`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.
-/
theorem metric_mul : EMul := by
  intro Lt _ _ N nu f g I K
  simp only [E]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c J =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J k)).det *
      (Matrix.of fun i k : Fin ((nu s).colLen c) => g s (J i) (K s c k)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k))
  calc _ = ∑ J : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id J).det *
        ((Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k)).submatrix J id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1

end PI.IsoInvMetricW
