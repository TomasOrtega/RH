import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.FlagHookShift

def shiftE {N : ℕ} (n : Fin N → ℕ) : Polynomial (MvPolynomial (Fin N) ℝ) :=
  Matrix.det (Matrix.of fun i c : Fin N =>
    Polynomial.C (C (((n c).factorial : ℝ)⁻¹)) * (Polynomial.X + Polynomial.C (X i)) ^ n c)

/- English proof (translation)
Unfold `shiftE`. Apply `Matrix.det_zero_of_column_eq h` to reduce the goal to its premises. Introduce `k`. Simplify using `[hn]`.
-/
theorem shiftE_eq_zero {N : ℕ} (n : Fin N → ℕ) {c d : Fin N} (h : c ≠ d) (hn : n c = n d) :
    shiftE n = 0 := by
  unfold shiftE
  apply Matrix.det_zero_of_column_eq h
  intro k
  simp [hn]

/- English proof (translation)
Unfold `shiftE detE`. Rewrite using `[← Polynomial.coe_evalRingHom, RingHom.map_det, AlgHom.map_det]`. Use `congr 1`. Use `ext1 i c`. Simplify using `[add_comm]`.
-/
theorem eval_shiftE {N : ℕ} (n : Fin N → ℕ) (a : ℝ) :
    (shiftE n).eval (C a) =
      aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (detE n) := by
  unfold shiftE detE
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext1 i c
  simp [add_comm]

/- English proof (translation)
Use `eval_shiftE n 0` as an intermediate fact. Simplify using `using this`.
-/
theorem eval_zero_shiftE {N : ℕ} (n : Fin N → ℕ) : (shiftE n).eval 0 = detE n := by
  have := eval_shiftE n 0
  simpa using this

/- English proof (translation)
Rewrite using `[Polynomial.derivative_C_mul, Polynomial.derivative_X_add_C_pow, ← mul_assoc, ← map_mul]`. Use `congr 2`. Rewrite using `[← map_natCast (C : ℝ →+* MvPolynomial (Fin N) ℝ), ← map_mul]`. Use `congr 1`. Rewrite using `[Nat.factorial_succ]`.

Establish `: (m.factorial : ℝ) ≠ 0` using `by exact_mod_cast m.factorial_ne_zero`. Establish `h2 : ((m : ℝ) + 1) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem derivative_entry {N : ℕ} (m : ℕ) (i : Fin N) :
    Polynomial.derivative (Polynomial.C (C (((m + 1).factorial : ℝ)⁻¹)) *
      (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin N) ℝ)) ^ (m + 1)) =
    Polynomial.C (C ((m.factorial : ℝ)⁻¹)) * (Polynomial.X + Polynomial.C (X i)) ^ m := by
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_add_C_pow, ← mul_assoc, ← map_mul]
  congr 2
  rw [← map_natCast (C : ℝ →+* MvPolynomial (Fin N) ℝ), ← map_mul]
  congr 1
  rw [Nat.factorial_succ]
  have : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/- English proof (translation)
Unfold `shiftE`. Simplify using `only [Matrix.det_apply', Matrix.of_apply]`. Rewrite using `[Polynomial.derivative_sum]`. Simplify using `only [Polynomial.derivative_intCast_mul, Polynomial.derivative_prod_finset, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `[h]`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero h`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[← Finset.prod_erase_mul univ _ (mem_univ c)]`. Use `congr 1`. Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hb)]`.

Rewrite using `[Function.update_self, hm, derivative_entry]`. Simplify using the standard rewrite rules.
-/
theorem derivative_shiftE {N : ℕ} (n : Fin N → ℕ) :
    Polynomial.derivative (shiftE n) =
      ∑ c, if n c = 0 then 0 else shiftE (Function.update n c (n c - 1)) := by
  unfold shiftE
  simp only [Matrix.det_apply', Matrix.of_apply]
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_intCast_mul, Polynomial.derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · simp [h]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.prod_erase_mul univ _ (mem_univ c)]
    congr 1
    · refine Finset.prod_congr rfl fun b hb => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
    · rw [Function.update_self, hm, derivative_entry]
      simp

/- English proof (translation)
Rewrite using `[derivative_shiftE]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `only [rho] at h`.

Establish `hc : (c : ℕ) + 1 < N` using `by omega`. Establish `hne : (⟨c + 1, hc⟩ : Fin N) ≠ c`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`.

Apply `shiftE_eq_zero _ hne` to reduce the goal to its premises. Rewrite using `[Function.update_self, Function.update_of_ne hne]`. Simplify using `only [rho]`. Use linear arithmetic over natural numbers and integers.
-/
theorem derivative_shiftE_rho (N : ℕ) : Polynomial.derivative (shiftE (rho N)) = 0 := by
  rw [derivative_shiftE]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h
  · rfl
  · simp only [rho] at h
    have hc : (c : ℕ) + 1 < N := by omega
    have hne : (⟨c + 1, hc⟩ : Fin N) ≠ c := by
      intro e; have := congrArg Fin.val e; simp at this
    apply shiftE_eq_zero _ hne
    rw [Function.update_self, Function.update_of_ne hne]
    simp only [rho]
    omega

/- English proof (translation)
Distinguish the cases in `hc : (c : ℕ) + 1 < N`. Use `left split_ifs with h`. Both sides reduce to the same expression. Establish `hne : (⟨c + 1, hc⟩ : Fin N) ≠ c`. Introduce `e`.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Apply `shiftE_eq_zero _ hne` to reduce the goal to its premises. Rewrite using `[Function.update_self, Function.update_of_ne hne]`. Simplify using `only [hookRho]`.

Apply the tactic sequence `split_ifs <;> first | contradiction | omega`. Use `c.2` as an intermediate fact. Distinguish the cases in `h2 : (c : ℕ) < r`. Use `right`. Use linear arithmetic over natural numbers and integers.

Use `left`. Rewrite using `[if_pos]`. Simplify using `only [hookRho]`. Apply the tactic sequence `split_ifs <;> first | contradiction | omega`.
-/
theorem lower_hook_zero {N k r : ℕ} (c : Fin N) (h0 : (c : ℕ) ≠ 0) (hr : (c : ℕ) ≠ r) :
    (if hookRho N k r c = 0 then 0
      else shiftE (Function.update (hookRho N k r) c (hookRho N k r c - 1))) = 0 ∨
    ((c : ℕ) + 1 = N ∧ (c : ℕ) < r) := by
  by_cases hc : (c : ℕ) + 1 < N
  · left
    split_ifs with h
    · rfl
    · have hne : (⟨c + 1, hc⟩ : Fin N) ≠ c := by
        intro e; have := congrArg Fin.val e; simp at this
      apply shiftE_eq_zero _ hne
      rw [Function.update_self, Function.update_of_ne hne]
      simp only [hookRho]
      split_ifs <;> first | contradiction | omega
  · have := c.2
    by_cases h2 : (c : ℕ) < r
    · right; omega
    · left
      rw [if_pos]
      simp only [hookRho]
      split_ifs <;> first | contradiction | omega

/- English proof (translation)
Rewrite using `[derivative_shiftE]`. Establish `hN : 0 < N` using `by omega`. Establish `hrN : r < N` using `by omega`. Establish `e0 : (if hookRho N k r ⟨0, hN⟩ = 0 then 0 else shiftE (Function.update (hookRho N k r) ⟨0, hN⟩ (hookRho N k r ⟨0, hN⟩ - 1))) = shiftE (hookRho N (k - 1) r)`. Rewrite using `[if_neg (by simp only [hookRho]; simp; omega)]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Distinguish the cases in `hc : c = ⟨0, hN⟩`. Substitute `hc` using the available equality. Rewrite using `[Function.update_self]`.

Simplify using `only [hookRho, if_true]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Function.update_of_ne hc]`. Establish `: (c : ℕ) ≠ 0` using `fun e => hc (Fin.ext e)`. Simplify using `[hookRho, this]`.

Establish `hz : ∀ c : Fin N, c ≠ ⟨0, hN⟩ → c ≠ ⟨r, hrN⟩ → (if hookRho N k r c = 0 then 0 else shiftE (Function.update (hookRho N k r) c (hookRho N k r c - 1))) = 0`. Introduce `c h0 h1`. Use `c.2` as an intermediate fact. Break down `lower_hook_zero (k := k) (r := r) c (fun e => h0 (Fin.ext e)) (fun e => h1 (Fin.ext e)) with h | h` into its components or cases. Conclude with `h`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : r = 0`. Rewrite using `[if_pos h, add_zero, Finset.sum_eq_single ⟨0, hN⟩, e0]`. Introduce `c _ hc`. Conclude with `hz c hc (by subst h; exact hc)`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h, Finset.sum_eq_add (⟨0, hN⟩ : Fin N) ⟨r, hrN⟩, e0]`. Use `congr 1`. Rewrite using `[if_neg (by simp [hookRho, h])]`. Use `congr 1`.

Use function extensionality and compare the values at `c`. Distinguish the cases in `hc : c = ⟨r, hrN⟩`. Substitute `hc` using the available equality. Rewrite using `[Function.update_self]`. Simplify using `only [hookRho]`.

Apply the tactic sequence `split_ifs <;> first | contradiction | omega`. Rewrite using `[Function.update_of_ne hc]`. Establish `: (c : ℕ) ≠ r` using `fun e => hc (Fin.ext e)`. Simplify using `only [hookRho]`. Apply the tactic sequence `split_ifs <;> first | contradiction | omega`.

Introduce `e`. Conclude with `h (congrArg Fin.val e).symm`. Introduce `c _ hc`. Conclude with `hz c hc.1 hc.2`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem derivative_shiftE_hook {N k r : ℕ} (hr : r < k) (hk : k ≤ N) :
    Polynomial.derivative (shiftE (hookRho N k r)) =
      shiftE (hookRho N (k - 1) r) + if r = 0 then 0 else shiftE (hookRho N (k - 1) (r - 1)) := by
  rw [derivative_shiftE]
  have hN : 0 < N := by omega
  have hrN : r < N := by omega
  have e0 : (if hookRho N k r ⟨0, hN⟩ = 0 then 0
      else shiftE (Function.update (hookRho N k r) ⟨0, hN⟩ (hookRho N k r ⟨0, hN⟩ - 1))) =
      shiftE (hookRho N (k - 1) r) := by
    rw [if_neg (by simp only [hookRho]; simp; omega)]
    congr 1
    funext c
    by_cases hc : c = ⟨0, hN⟩
    · subst hc
      rw [Function.update_self]
      simp only [hookRho, if_true]
      omega
    · rw [Function.update_of_ne hc]
      have : (c : ℕ) ≠ 0 := fun e => hc (Fin.ext e)
      simp [hookRho, this]
  have hz : ∀ c : Fin N, c ≠ ⟨0, hN⟩ → c ≠ ⟨r, hrN⟩ → (if hookRho N k r c = 0 then 0
      else shiftE (Function.update (hookRho N k r) c (hookRho N k r c - 1))) = 0 := by
    intro c h0 h1
    have := c.2
    rcases lower_hook_zero (k := k) (r := r) c (fun e => h0 (Fin.ext e))
      (fun e => h1 (Fin.ext e)) with h | h
    · exact h
    · omega
  by_cases h : r = 0
  · rw [if_pos h, add_zero, Finset.sum_eq_single ⟨0, hN⟩, e0]
    · intro c _ hc
      exact hz c hc (by subst h; exact hc)
    · simp
  · rw [if_neg h, Finset.sum_eq_add (⟨0, hN⟩ : Fin N) ⟨r, hrN⟩, e0]
    · congr 1
      rw [if_neg (by simp [hookRho, h])]
      congr 1
      funext c
      by_cases hc : c = ⟨r, hrN⟩
      · subst hc
        rw [Function.update_self]
        simp only [hookRho]
        split_ifs <;> first | contradiction | omega
      · rw [Function.update_of_ne hc]
        have : (c : ℕ) ≠ r := fun e => hc (Fin.ext e)
        simp only [hookRho]
        split_ifs <;> first | contradiction | omega
    · intro e; exact h (congrArg Fin.val e).symm
    · intro c _ hc
      exact hz c hc.1 hc.2
    · simp
    · simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Finset.sum_range_succ, ih]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem telescope {R : Type} [CommRing R] (T : ℕ → R) (m : ℕ) :
    ∑ r ∈ range (m + 1), (-1 : R) ^ r * (T r + if r = 0 then 0 else T (r - 1)) =
      (-1) ^ m * T m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp; ring

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Polynomial.derivative_sum]`. Establish `: ∀ r ∈ range (m + 1), Polynomial.derivative ((-1) ^ r * shiftE (hookRho N (m + 1) r)) = (-1) ^ r * (shiftE (hookRho N m r) + if r = 0 then 0 else shiftE (hookRho N m (r - 1)))`. Introduce `r hr`. Rewrite using `[Polynomial.derivative_mul, derivative_shiftE_hook (mem_range.1 hr) hk]`.

Simplify using `[Polynomial.derivative_pow]`. Rewrite using `[Finset.sum_congr rfl this, telescope (fun r => shiftE (hookRho N m r)) m]`. Establish `h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩` using `by simp`. Rewrite using `[shiftE_eq_zero _ h01, mul_zero]`. Simplify using `only [hookRho]`.

Apply the tactic sequence `split_ifs <;> first | contradiction | omega`.
-/
theorem derivative_shiftR {N k : ℕ} (h2 : 2 ≤ k) (hk : k ≤ N) :
    Polynomial.derivative (∑ r ∈ range k, (-1) ^ r * shiftE (hookRho N k r)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Polynomial.derivative_sum]
  have : ∀ r ∈ range (m + 1), Polynomial.derivative ((-1) ^ r * shiftE (hookRho N (m + 1) r)) =
      (-1) ^ r * (shiftE (hookRho N m r) + if r = 0 then 0 else shiftE (hookRho N m (r - 1))) := by
    intro r hr
    rw [Polynomial.derivative_mul, derivative_shiftE_hook (mem_range.1 hr) hk]
    simp [Polynomial.derivative_pow]
  rw [Finset.sum_congr rfl this, telescope (fun r => shiftE (hookRho N m r)) m]
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  rw [shiftE_eq_zero _ h01, mul_zero]
  simp only [hookRho]
  split_ifs <;> first | contradiction | omega

/- English proof (translation)
Rewrite using `[Polynomial.eq_C_of_derivative_eq_zero h]`. Simplify using the standard rewrite rules.
-/
theorem eval_eq_of_derivative {N : ℕ} (P : Polynomial (MvPolynomial (Fin N) ℝ))
    (h : Polynomial.derivative P = 0) (b : MvPolynomial (Fin N) ℝ) : P.eval b = P.eval 0 := by
  rw [Polynomial.eq_C_of_derivative_eq_zero h]
  simp

/- English proof (translation)
Introduce `N k a h2 hk`. Prove the components needed by the constructor for the conclusion. Use `eval_eq_of_derivative _ (derivative_shiftR h2 hk) (C a)` as an intermediate fact. Simplify using `only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, eval_shiftE, eval_zero_shiftE] at this`. Simplify `this` using `[hookR, map_sum]`.

Rewrite using `[← eval_shiftE, eval_eq_of_derivative _ (derivative_shiftE_rho N), eval_zero_shiftE]`.
-/
theorem shift_invariant : ∀ (N k : ℕ) (a : ℝ), 2 ≤ k → k ≤ N →
    aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (hookR N k) = hookR N k ∧
    aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (detE (rho N)) = detE (rho N) := by
  intro N k a h2 hk
  constructor
  · have := eval_eq_of_derivative _ (derivative_shiftR h2 hk) (C a)
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one, eval_shiftE, eval_zero_shiftE] at this
    simpa [hookR, map_sum] using this
  · rw [← eval_shiftE, eval_eq_of_derivative _ (derivative_shiftE_rho N), eval_zero_shiftE]

end GlobalTheory.FlagHookShift
