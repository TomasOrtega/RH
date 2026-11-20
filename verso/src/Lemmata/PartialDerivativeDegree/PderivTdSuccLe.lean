import Mathlib

universe u_1

namespace Bl.PartialDerivativeDegree

/- English proof (translation)
Establish `hne : (MvPolynomial.pderiv i q).support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]` and apply the resulting hypothesis. Take `⟨m, hm, hmax⟩` from `Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ e => e)`. Establish `hc : MvPolynomial.coeff (m + Finsupp.single i 1) q ≠ 0`. Introduce `h0`.

Establish `h1` using `MvPolynomial.mem_support_iff.mp hm`. Rewrite `h1` using `[MvPolynomial.coeff_pderiv, h0, zero_mul]`. Conclude with `h1 rfl`. Establish `hle` using `MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)`. Rewrite `hle` using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]`.

Rewrite using `[MvPolynomial.totalDegree, hmax]`. Conclude with `hle`.
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
Introduce `σ i q L hL`. Distinguish the cases in `h : MvPolynomial.pderiv i q = 0`. Rewrite using `[h, zero_mul, MvPolynomial.totalDegree_zero]`. Conclude with `Nat.zero_le _`. Establish `hk` using `pderiv_td_succ_le i q h`.

Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
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
