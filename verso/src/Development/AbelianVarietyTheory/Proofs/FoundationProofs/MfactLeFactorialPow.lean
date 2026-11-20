import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

/- English proof (translation)
Introduce `n ν R hR mo hmo`. Establish `h : mfact mo = ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial`. Express the relevant statement in the definitionally equal form `(mo.prod fun _ k => k.factorial) = _`. Rewrite using `[Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type_right]`. Rewrite using `[h]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod' fun t _ => ?_` and prove the remaining obligations. Use `le_trans (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ fun a => mo (a, t))) ?_` and prove the remaining obligations. Rewrite using `[hmo t]`. Conclude with `Nat.factorial_le (hR t)`.

Use `_ = R.factorial ^ n := by simp`.
-/
theorem mfact_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), (∀ i, ν i ≤ R) → ∀ mo : Fin n × Fin n →₀ ℕ, (∀ t, ∑ a, mo (a, t) = ν t) → mfact mo ≤ (R.factorial) ^ n := by
  intro n ν R hR mo hmo
  have h : mfact mo = ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial := by
    change (mo.prod fun _ k => k.factorial) = _
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type_right]
  rw [h]
  calc ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial ≤ ∏ _t : Fin n, R.factorial := by
        refine Finset.prod_le_prod' fun t _ => ?_
        refine le_trans (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ fun a => mo (a, t))) ?_
        rw [hmo t]
        exact Nat.factorial_le (hR t)
    _ = R.factorial ^ n := by simp

end GlobalTheory.TestLat
