import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem extract : Extract := by
  classical
  intro K σ A M _ _ _ x hx e he w
  set v : A → M → K := fun a m => ∏ p, x a p ^ e m p with hvdef
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    have hφv : ∀ u : M → K, φ u = ∑ m, u m * φ (Pi.single m 1) := by
      intro u
      rw [LinearMap.pi_apply_eq_sum_univ φ u]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_mul]
      congr 2
      ext s
      simp [Pi.single_apply, eq_comm]
    let E : M → σ →₀ ℕ := fun m => Finsupp.equivFunOnFinite.symm (e m)
    have hE : Function.Injective E := fun a b h => he (by simpa [E] using h)
    let Q : MvPolynomial σ K := ∑ m, monomial (E m) (φ (Pi.single m 1))
    have hQ : Q = 0 := by
      refine hx Q ?_
      rintro _ ⟨a, rfl⟩
      have h1 : φ (v a) = 0 := by
        have h2 := Submodule.mem_map_of_mem (f := φ) (Submodule.subset_span ⟨a, rfl⟩ : v a ∈ Submodule.span K (Set.range v))
        rw [hmap, Submodule.mem_bot] at h2
        exact h2
      rw [hφv] at h1
      rw [← h1]
      simp only [Q, map_sum, eval_monomial]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), mul_comm]
      rfl
    apply hφ
    refine LinearMap.ext fun u => ?_
    rw [hφv, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hc := congrArg (coeff (E m)) hQ
    simp only [Q, coeff_sum, coeff_monomial, coeff_zero, hE.eq_iff] at hc
    simp at hc
    rw [hc, mul_zero]
  have hw : w ∈ Submodule.span K (Set.range v) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hw
  refine ⟨c, fun m => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvdef]

end UpperTheory.Gal.Schur
