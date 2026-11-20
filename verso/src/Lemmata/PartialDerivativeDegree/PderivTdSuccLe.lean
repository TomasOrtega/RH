import Mathlib

universe u_1

namespace Bl.PartialDerivativeDegree

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private lemma pderiv_td_succ_le {σ : Type u_1} (i : σ) (q : MvPolynomial σ Complex)
    (h : MvPolynomial.pderiv i q ≠ 0) :
    (MvPolynomial.pderiv i q).totalDegree + 1 ≤ q.totalDegree := by
  classical
  have hne : (MvPolynomial.pderiv i q).support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  have hc : MvPolynomial.coeff (m + Finsupp.single i 1) q ≠ 0 := by
    intro h0
    have h1 := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv, h0, zero_mul] at h1
    exact h1 rfl
  have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl] at hle
  rw [MvPolynomial.totalDegree, hmax]
  exact hle

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {σ : Type u_1} (i : σ) (q L : MvPolynomial.{u_1, 0} σ Complex),
  LE.le.{0} (MvPolynomial.totalDegree.{0, u_1} L) 1 →
    LE.le.{0}
      (MvPolynomial.totalDegree.{0, u_1}
        (HMul.hMul.{u_1, u_1, u_1}
          (DFunLike.coe.{max (u_1 + 1) 1, max (u_1 + 1) 1, max (u_1 + 1) 1} (MvPolynomial.pderiv.{0, u_1} i) q) L))
      (MvPolynomial.totalDegree.{0, u_1} q) := by
  intro σ i q L hL
  by_cases h : MvPolynomial.pderiv i q = 0
  · rw [h, zero_mul, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · have hk := pderiv_td_succ_le i q h
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    omega

end Bl.PartialDerivativeDegree
