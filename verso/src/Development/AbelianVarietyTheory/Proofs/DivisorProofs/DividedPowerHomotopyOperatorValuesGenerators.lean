import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRules

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Gen

variable {R B P : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing P] [Algebra R P]
  (v : Derivation R P P) {α : B →+* P} (h : SemiHom (RingHom.id R) α)

/- English proof (translation)
Proceed by induction on `x using indDR with`. Consider the case `h b => rw [h.mDR_algebraMap, ctr_algebraMap]`. Consider the case `hd b => rw [h.mDR_ι, h.m1_D, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, hv, map_zero]`. Consider the case `hm x y hx hy => rw [map_mul, ctr_mul, hx, hy, zero_mul, mul_zero, add_zero]`. Consider the case `ha x y hx hy => rw [map_add, map_add, hx, hy, add_zero]`.
-/
theorem ctr_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : ctr v (h.mDR x) = 0 := by
  induction x using indDR with
  | h b => rw [h.mDR_algebraMap, ctr_algebraMap]
  | hd b => rw [h.mDR_ι, h.m1_D, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, hv, map_zero]
  | hm x y hx hy => rw [map_mul, ctr_mul, hx, hy, zero_mul, mul_zero, add_zero]
  | ha x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/- English proof (translation)
Rewrite using `[lie_apply, ctr_mDR_of_kill v h hv, map_zero, zero_add, ← h.mDR_dDR, ctr_mDR_of_kill v h hv]`.
-/
theorem lie_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : lie v (h.mDR x) = 0 := by
  rw [lie_apply, ctr_mDR_of_kill v h hv, map_zero, zero_add, ← h.mDR_dDR, ctr_mDR_of_kill v h hv]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, lie_mul, lie_algebraMap, lie_mDR_of_kill v h hv, mul_zero, add_zero, ← Algebra.smul_def]`.
-/
theorem lie_smul_mDR (hv : ∀ b, v (α b) = 0) (p : P) (x : DR R B) :
    lie v (p • h.mDR x) = v p • h.mDR x := by
  rw [Algebra.smul_def, lie_mul, lie_algebraMap, lie_mDR_of_kill v h hv, mul_zero, add_zero, ← Algebra.smul_def]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih]`. Distinguish the cases in `hk : k ≤ n`.

Rewrite using `[if_pos hk, lie_smul_mDR v h hv]`. Distinguish the cases in `hk' : k + 1 ≤ n`. Rewrite using `[if_pos hk', show n - k = (n - (k + 1)) + 1 by omega, hs]`. Rewrite using `[if_neg hk', show n - k = 0 by omega, he0]`. Rewrite using `[if_neg hk, if_neg (by omega), zero_smul, map_zero]`.
-/
theorem lie_pow_smul_mDR (hv : ∀ b, v (α b) = 0) (e : ℕ → P) (he0 : v (e 0) = 0)
    (hs : ∀ n, v (e (n + 1)) = e n) (x : DR R B) (n k : ℕ) :
    (lie v ^ k) (e n • h.mDR x) = (if k ≤ n then e (n - k) else 0) • h.mDR x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hk : k ≤ n
    · rw [if_pos hk, lie_smul_mDR v h hv]
      by_cases hk' : k + 1 ≤ n
      · rw [if_pos hk', show n - k = (n - (k + 1)) + 1 by omega, hs]
      · rw [if_neg hk', show n - k = 0 by omega, he0]
    · rw [if_neg hk, if_neg (by omega), zero_smul, map_zero]

end Gen

/- English proof (translation)
Establish `h0` using `Int.alternating_sum_range_choose (n := n + 1)`. Rewrite `h0` using `[Finset.sum_range_succ']`. Simplify using `only [pow_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, if_neg (Nat.succ_ne_zero n)] at h0`. Establish `: ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * -1 * ((n + 1).choose (k + 1) : ℤ) = -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ)`. Rewrite using `[← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alt_sum_choose_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) = 1 := by
  have h0 := Int.alternating_sum_range_choose (n := n + 1)
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, if_neg (Nat.succ_ne_zero n)] at h0
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * -1 * ((n + 1).choose (k + 1) : ℤ) =
      -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

/- English proof (translation)
Simplify using `only [mul_ite, mul_zero]`. Rewrite using `[← Finset.sum_filter, show (Finset.range N).filter (· ≤ n) = Finset.range (n + 1) by`. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use the proof step `omega]`.

Establish `key : ∀ k ∈ Finset.range (n + 1), (-1 : Q.P) ^ k * Q.e (k + 1) * Q.e (n - k) = (((-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) : ℤ) : Q.P) * Q.e (n + 1)`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range]`. Rewrite using `[mul_assoc, Q.e_mul, show k + 1 + (n - k) = n + 1 by omega]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl key, ← Finset.sum_mul, ← Int.cast_sum, alt_sum_choose_succ, Int.cast_one, one_mul]`.
-/
theorem sum_e_mul {B : Type} [CommRing B] (Q : PDPoly B) (N n : ℕ) (hn : n < N) :
    ∑ k ∈ Finset.range N, ((-1) ^ k * Q.e (k + 1)) * (if k ≤ n then Q.e (n - k) else 0) = Q.e (n + 1) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, show (Finset.range N).filter (· ≤ n) = Finset.range (n + 1) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  have key : ∀ k ∈ Finset.range (n + 1), (-1 : Q.P) ^ k * Q.e (k + 1) * Q.e (n - k) =
      (((-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) : ℤ) : Q.P) * Q.e (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_assoc, Q.e_mul, show k + 1 + (n - k) = n + 1 by omega]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, ← Int.cast_sum, alt_sum_choose_succ, Int.cast_one, one_mul]

/- English proof (translation)
Introduce `R B _ _ _ J δ Q _ _ η v h _ hB hs _ N n α`. Establish `he0 : v (Q.e 0) = 0` using `by rw [Q.e_zero]; exact v.map_one_eq_zero`. Use `⟨?_, fun hn ↦ ?_⟩` and prove the remaining obligations. Unfold `hot`. Use `Finset.sum_eq_zero fun k _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ctr_mDR_of_kill v h hB, smul_zero, map_zero, smul_zero]`. Establish `hc : ctr v (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e n • h.mDR α`. Rewrite using `[map_smul, ctr_ι_mul, Derivation.liftKaehlerDifferential_comp_D, hs 0, Q.e_zero, one_smul, ctr_mDR_of_kill v h hB, mul_zero, sub_zero]`. Unfold `hot`. Simplify using `only [hc, lie_pow_smul_mDR v h hB Q.e he0 hs, smul_smul]`.

Rewrite using `[← Finset.sum_smul, sum_e_mul Q N n hn]`.
-/
theorem hot_values : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  intro R B _ _ _ J δ Q _ _ η v h _ hB hs _ N n α
  have he0 : v (Q.e 0) = 0 := by rw [Q.e_zero]; exact v.map_one_eq_zero
  refine ⟨?_, fun hn ↦ ?_⟩
  · unfold hot
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [map_smul, ctr_mDR_of_kill v h hB, smul_zero, map_zero, smul_zero]
  · have hc : ctr v (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e n • h.mDR α := by
      rw [map_smul, ctr_ι_mul, Derivation.liftKaehlerDifferential_comp_D, hs 0, Q.e_zero, one_smul,
        ctr_mDR_of_kill v h hB, mul_zero, sub_zero]
    unfold hot
    simp only [hc, lie_pow_smul_mDR v h hB Q.e he0 hs, smul_smul]
    rw [← Finset.sum_smul, sum_e_mul Q N n hn]

end GlobalTheory.PDForm
