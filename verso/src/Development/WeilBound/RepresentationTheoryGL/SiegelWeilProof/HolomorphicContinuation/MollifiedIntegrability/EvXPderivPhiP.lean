import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickB

noncomputable section

open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `hA : Amat ε c t b a *ᵥ v = (c : ℂ) • v - (Complex.I * t * sgn ε a) • (bᵀ *ᵥ v)`. Rewrite using `[Amat, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec]`. Establish `key : (c : ℂ) * (star v ⬝ᵥ v) - (Complex.I * t * sgn ε a) * (star v ⬝ᵥ (bᵀ *ᵥ v)) = 0`.

Establish `h1 : star v ⬝ᵥ (Amat ε c t b a *ᵥ v) = 0` using `by rw [hv, dotProduct_zero]`. Rewrite `h1` using `[hA, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]`. Conclude with `h1`. Establish `hq : (star v ⬝ᵥ (bᵀ *ᵥ v)).im = 0` using `hb.transpose.im_star_dotProduct_mulVec_self v`. Establish `hd : (star v ⬝ᵥ v).im = 0`.

Use `Matrix.isHermitian_one.im_star_dotProduct_mulVec_self (𝕜 := ℂ) v` as an intermediate fact. Rewrite `this` using `[one_mulVec]`. Then use the resulting hypothesis. Establish `hq' : star v ⬝ᵥ (bᵀ *ᵥ v) = ((star v ⬝ᵥ (bᵀ *ᵥ v)).re : ℂ)` using `Complex.ext (by simp) (by simp [hq])`. Apply the tactic sequence `have hs' : sgn ε a = ((if ε a then 1 else -1 : ℝ) : ℂ) := by unfold sgn; split_ifs <;> simp`. Establish `h0re : (Complex.I * t * sgn ε a * (star v ⬝ᵥ (bᵀ *ᵥ v))).re = 0`.

Rewrite using `[hq', hs']`. Simplify using `[Complex.mul_re]`. Establish `hre` using `congrArg Complex.re key`. Rewrite `hre` using `[Complex.sub_re, h0re, Complex.re_ofReal_mul, Complex.zero_re, sub_zero]`. Establish `hdre : (star v ⬝ᵥ v).re = 0`.

Break down `mul_eq_zero.mp hre with h | h` into its components or cases. Conclude with `absurd h hc.ne'`. Conclude with `h`. Establish `hd0 : star v ⬝ᵥ v = 0` using `Complex.ext hdre hd`. Conclude with `hv0 (dotProduct_star_self_eq_zero.mp hd0)`.
-/
theorem amat_det_ne (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) : (Amat ε c t b a).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hA : Amat ε c t b a *ᵥ v = (c : ℂ) • v - (Complex.I * t * sgn ε a) • (bᵀ *ᵥ v) := by
    rw [Amat, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec]
  have key : (c : ℂ) * (star v ⬝ᵥ v) - (Complex.I * t * sgn ε a) * (star v ⬝ᵥ (bᵀ *ᵥ v)) = 0 := by
    have h1 : star v ⬝ᵥ (Amat ε c t b a *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
    rw [hA, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have hq : (star v ⬝ᵥ (bᵀ *ᵥ v)).im = 0 := hb.transpose.im_star_dotProduct_mulVec_self v
  have hd : (star v ⬝ᵥ v).im = 0 := by
    have := Matrix.isHermitian_one.im_star_dotProduct_mulVec_self (𝕜 := ℂ) v
    rwa [one_mulVec] at this
  have hq' : star v ⬝ᵥ (bᵀ *ᵥ v) = ((star v ⬝ᵥ (bᵀ *ᵥ v)).re : ℂ) := Complex.ext (by simp) (by simp [hq])
  have hs' : sgn ε a = ((if ε a then 1 else -1 : ℝ) : ℂ) := by unfold sgn; split_ifs <;> simp
  have h0re : (Complex.I * t * sgn ε a * (star v ⬝ᵥ (bᵀ *ᵥ v))).re = 0 := by
    rw [hq', hs']; simp [Complex.mul_re]
  have hre := congrArg Complex.re key
  rw [Complex.sub_re, h0re, Complex.re_ofReal_mul, Complex.zero_re, sub_zero] at hre
  have hdre : (star v ⬝ᵥ v).re = 0 := by
    rcases mul_eq_zero.mp hre with h | h
    · exact absurd h hc.ne'
    · exact h
  have hd0 : star v ⬝ᵥ v = 0 := Complex.ext hdre hd
  exact hv0 (dotProduct_star_self_eq_zero.mp hd0)

/- English proof (translation)
Simplify using `[dEv, evX_eq, mul_comm]`.
-/
theorem dEv_apply (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    dEv P x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
  simp [dEv, evX_eq, mul_comm]

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt`.
-/
theorem evX_continuous (P : PX m n) : Continuous (evX P) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

/- English proof (translation)
Take `⟨a', i', bb⟩` from `k`. Rewrite using `[crd_apply, crd_apply]`. Distinguish the cases in `h : a' = a ∧ i' = j`. Take `⟨rfl, rfl⟩` from `h`. Apply the tactic sequence `cases bb <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring`.

Establish `h' : ¬ ((a', i', bb) = (a, j, false))` using `by intro e; simp at e; exact h ⟨e.1, e.2.1⟩`. Simplify using `[h, h']`.
-/
theorem crd_wirt (a : Fin m) (j : Fin n) (k : Fin m × Fin n × Bool) :
    crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      if k = (a, j, false) then 2 else 0 := by
  obtain ⟨a', i', bb⟩ := k
  rw [crd_apply, crd_apply]
  by_cases h : a' = a ∧ i' = j
  · obtain ⟨rfl, rfl⟩ := h
    cases bb <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · have h' : ¬ ((a', i', bb) = (a, j, false)) := by intro e; simp at e; exact h ⟨e.1, e.2.1⟩
    simp [h, h']

/- English proof (translation)
Simplify using `only [dEv, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_eq_single (a, j, false)]`. Use `crd_wirt a j (a, j, false)` as an intermediate fact. Simplify using `only [if_true] at this`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `k _ hk`. Use `crd_wirt a j k` as an intermediate fact. Rewrite `this` using `[if_neg hk]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using the standard rewrite rules.
-/
theorem dEv_wirt (P : PX m n) (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    dEv P x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * dEv P x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      2 * evX (pderiv (a, j, false) P) x := by
  simp only [dEv, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (a, j, false)]
  · have := crd_wirt a j (a, j, false); simp only [if_true] at this
    rw [← this]; ring
  · intro k _ hk
    have := crd_wirt a j k; rw [if_neg hk] at this
    calc _ = evX (pderiv k P) x * (crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0)) := by ring
      _ = 0 := by rw [this, mul_zero]
  · simp

/- English proof (translation)
Simplify using `only [phiP, map_neg, map_sum, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]`. Simplify using `only [evX, map_neg, map_sum, map_mul, Prod.ext_iff]`. Simplify using `only [mul_zero, mul_one, zero_mul, Pi.single_apply, Prod.mk.injEq, and_true, Bool.false_eq_true, and_false, if_false, map_zero, add_zero, zero_add]`. Rewrite using `[neg_inj, Finset.sum_eq_single a]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `j' _ hj`. Simplify using `[hj]`. Simplify using the standard rewrite rules.

Introduce `a' _ ha`. Simplify using `[ha]`. Simplify using the standard rewrite rules.
-/
theorem evX_pderiv_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ)
    (a : Fin m) (j : Fin n) :
    evX (pderiv (a, j, false) (phiP ε c t b)) x = -∑ k, (Amat ε c t b a) k j * star (x a k) := by
  simp only [phiP, map_neg, map_sum, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]
  simp only [evX, map_neg, map_sum, map_mul, Prod.ext_iff]
  simp only [mul_zero, mul_one, zero_mul, Pi.single_apply, Prod.mk.injEq, and_true, Bool.false_eq_true, and_false,
    if_false, map_zero, add_zero, zero_add]
  rw [neg_inj, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro a' _ ha; simp [ha]
  · simp

end PositivityTheory.Rg.Sw.WR.G
