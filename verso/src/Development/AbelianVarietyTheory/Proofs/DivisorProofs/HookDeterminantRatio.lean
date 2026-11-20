import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho

noncomputable section
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.HookSchur

def hs {R : Type} [CommRing R] (x : ℕ → R) (N : ℕ) : ℕ → ℕ → R :=
  Nat.rec (motive := fun _ => ℕ → ℕ → R)
    (fun a => Nat.rec (motive := fun _ => ℕ → R) (fun r => if r = 0 then 1 else 0)
      (fun _ _ _ => 0) a)
    (fun N prev a => Nat.rec (motive := fun _ => ℕ → R) (fun r => if r = 0 then 1 else 0)
      (fun a cur r => x N * cur r + prev (a + 1) r +
        (if r = 0 then 0 else x N * prev (a + 1) (r - 1))) a) N

section
variable {R : Type} [CommRing R] (x : ℕ → R)

/- English proof (translation)
Apply the tactic sequence `cases N <;> rfl`.
-/
theorem hs_zero_length (N r : ℕ) : hs x N 0 r = if r = 0 then 1 else 0 := by
  cases N <;> rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hs_zero_variables (a r : ℕ) : hs x 0 (a + 1) r = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hs_succ (N a r : ℕ) : hs x (N + 1) (a + 1) r =
    x N * hs x (N + 1) a r + hs x N (a + 1) r +
      (if r = 0 then 0 else x N * hs x N (a + 1) (r - 1)) := rfl

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro a r _`. Conclude with `hs_zero_variables x a r`. Consider the case `succ N ih`. Introduce `a r hr`.

Establish `hr0 : r ≠ 0` using `by omega`. Proceed by induction on `a with`. Consider the case `zero => rw [hs_succ, hs_zero_length, ih _ _ (by omega), ih _ (r - 1) (by omega)]; simp [hr0]`. Consider the case `succ a iha => rw [hs_succ, iha, ih _ _ (by omega), ih _ (r - 1) (by omega)]; simp`.
-/
theorem hs_eq_zero (N : ℕ) : ∀ a r, N ≤ r → hs x N (a + 1) r = 0 := by
  induction N with
  | zero => intro a r _; exact hs_zero_variables x a r
  | succ N ih =>
    intro a r hr
    have hr0 : r ≠ 0 := by omega
    induction a with
    | zero => rw [hs_succ, hs_zero_length, ih _ _ (by omega), ih _ (r - 1) (by omega)]; simp [hr0]
    | succ a iha => rw [hs_succ, iha, ih _ _ (by omega), ih _ (r - 1) (by omega)]; simp

def rem (N a : ℕ) (y : R) : R := ∑ r ∈ range N, (-1) ^ r * hs x N a r * y ^ (N - 1 - r)

/- English proof (translation)
Establish `h1 : y * rem x N (a + 1) y = ∑ r ∈ range (N + 1), (-1) ^ r * hs x N (a + 1) r * y ^ (N + 1 - 1 - r)`. Rewrite using `[sum_range_succ, hs_eq_zero x N a N le_rfl, rem, mul_sum]`. Simplify using `only [mul_zero, zero_mul, add_zero]`. Use `sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Establish `: N + 1 - 1 - r = (N - 1 - r) + 1` using `by have := mem_range.1 hr; omega`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : -(x N * rem x N (a + 1) y) = ∑ r ∈ range (N + 1), (-1) ^ r * (if r = 0 then 0 else x N * hs x N (a + 1) (r - 1)) * y ^ (N + 1 - 1 - r)`. Rewrite using `[sum_range_succ', rem, mul_sum, ← sum_neg_distrib]`. Simplify using `only [if_true, mul_zero, zero_mul, add_zero]`.

Use `sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Establish `: N + 1 - 1 - (r + 1) = (N - 1 - r)` using `by omega`. Rewrite using `[this, if_neg (Nat.succ_ne_zero r), Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sub_mul, sub_eq_add_neg, h1, h2, rem, rem, mul_sum, ← sum_add_distrib, ← sum_add_distrib]`.

Use `sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hs_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rem_succ (N a : ℕ) (y : R) :
    rem x (N + 1) (a + 1) y = x N * rem x (N + 1) a y + (y - x N) * rem x N (a + 1) y := by
  have h1 : y * rem x N (a + 1) y =
      ∑ r ∈ range (N + 1), (-1) ^ r * hs x N (a + 1) r * y ^ (N + 1 - 1 - r) := by
    rw [sum_range_succ, hs_eq_zero x N a N le_rfl, rem, mul_sum]
    simp only [mul_zero, zero_mul, add_zero]
    refine sum_congr rfl fun r hr => ?_
    have : N + 1 - 1 - r = (N - 1 - r) + 1 := by have := mem_range.1 hr; omega
    rw [this]; ring
  have h2 : -(x N * rem x N (a + 1) y) = ∑ r ∈ range (N + 1),
      (-1) ^ r * (if r = 0 then 0 else x N * hs x N (a + 1) (r - 1)) * y ^ (N + 1 - 1 - r) := by
    rw [sum_range_succ', rem, mul_sum, ← sum_neg_distrib]
    simp only [if_true, mul_zero, zero_mul, add_zero]
    refine sum_congr rfl fun r hr => ?_
    have : N + 1 - 1 - (r + 1) = (N - 1 - r) := by omega
    rw [this, if_neg (Nat.succ_ne_zero r), Nat.add_sub_cancel]; ring
  rw [sub_mul, sub_eq_add_neg, h1, h2, rem, rem, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [hs_succ]; ring

/- English proof (translation)
Rewrite using `[rem, sum_range_succ']`. Simplify using `[hs_zero_length]`.
-/
theorem rem_zero (N : ℕ) (y : R) : rem x (N + 1) 0 y = y ^ N := by
  rw [rem, sum_range_succ']
  simp [hs_zero_length]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro a i hi`. Use linear arithmetic over natural numbers and integers. Consider the case `succ N ih`. Introduce `a i hi`.

Proceed by induction on `a with`. Consider the case `zero => rw [rem_zero]`. Simplify using the standard rewrite rules. Consider the case `succ a iha`. Rewrite using `[rem_succ, iha]`.

Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with h | h` into its components or cases. Rewrite using `[ih _ _ h]`. Establish `e1 : N - 1 + (a + 1) = N + a` using `by omega`. Establish `e2 : N + 1 - 1 + a = N + a` using `by omega`. Establish `e3 : N + 1 - 1 + (a + 1) = N + a + 1` using `by omega`.

Rewrite using `[e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree. Substitute `h` using the available equality. Rewrite using `[sub_self, zero_mul, add_zero, ← add_assoc, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rem_eq (N : ℕ) : ∀ a i, i < N → rem x N a (x i) = x i ^ (N - 1 + a) := by
  induction N with
  | zero => intro a i hi; omega
  | succ N ih =>
    intro a i hi
    induction a with
    | zero => rw [rem_zero]; simp
    | succ a iha =>
      rw [rem_succ, iha]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · rw [ih _ _ h]
        have e1 : N - 1 + (a + 1) = N + a := by omega
        have e2 : N + 1 - 1 + a = N + a := by omega
        have e3 : N + 1 - 1 + (a + 1) = N + a + 1 := by omega
        rw [e1, e2, e3]; ring
      · subst h
        rw [sub_self, zero_mul, add_zero, ← add_assoc, pow_succ]; ring

/- English proof (translation)
Establish `base : ∀ N r, P (0 + r) (hs x N 0 r)`. Introduce `N r`. Rewrite using `[hs_zero_length]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `h1`. Conclude with `h0 _`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `a r`.

Consider the cases of `a with`. Consider the case `zero => exact base _ _`. Consider the case `succ a => rw [hs_zero_variables]`. Conclude with `h0 _`. Consider the case `succ N ih`.

Introduce `a r`. Proceed by induction on `a with`. Consider the case `zero => exact base _ _`. Consider the case `succ a iha`. Rewrite using `[hs_succ]`.

Use `hadd _ _ _ (hadd _ _ _ ?_ (ih _ _)) ?_` and prove the remaining obligations. Establish `e : a + 1 + r = a + r + 1` using `by omega`. Rewrite using `[e]`. Conclude with `hmul _ _ _ iha`. Use `split_ifs with h`.

Conclude with `h0 _`. Establish `e : a + 1 + r = a + 1 + (r - 1) + 1` using `by omega`. Rewrite using `[e]`. Conclude with `hmul _ _ _ (ih _ _)`.
-/
theorem hs_induct (P : ℕ → R → Prop) (h0 : ∀ d, P d 0) (h1 : P 0 1)
    (hadd : ∀ d p q, P d p → P d q → P d (p + q)) (hmul : ∀ d i p, P d p → P (d + 1) (x i * p))
    (N : ℕ) : ∀ a r, P (a + r) (hs x N a r) := by
  have base : ∀ N r, P (0 + r) (hs x N 0 r) := by
    intro N r
    rw [hs_zero_length]
    split_ifs with h
    · subst h; exact h1
    · exact h0 _
  induction N with
  | zero =>
    intro a r
    cases a with
    | zero => exact base _ _
    | succ a => rw [hs_zero_variables]; exact h0 _
  | succ N ih =>
    intro a r
    induction a with
    | zero => exact base _ _
    | succ a iha =>
      rw [hs_succ]
      refine hadd _ _ _ (hadd _ _ _ ?_ (ih _ _)) ?_
      · have e : a + 1 + r = a + r + 1 := by omega
        rw [e]; exact hmul _ _ _ iha
      · split_ifs with h
        · exact h0 _
        · have e : a + 1 + r = a + 1 + (r - 1) + 1 := by omega
          rw [e]; exact hmul _ _ _ (ih _ _)

/- English proof (translation)
Establish `base : ∀ N r, f (hs x N 0 r) = (((N + 0 - 1).choose (0 + r) * (0 + r - 1).choose r : ℕ) : T)`. Introduce `N r`. Rewrite using `[hs_zero_length]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Nat.choose_eq_zero_of_lt (n := 0 + r - 1) (by omega)]; simp`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `a r`.

Consider the cases of `a with`. Consider the case `zero => exact base _ _`. Consider the case `succ a => rw [hs_zero_variables, Nat.choose_eq_zero_of_lt (n := 0 + (a + 1) - 1) (by omega)]; simp`. Consider the case `succ N ih`. Introduce `a r`.

Establish `ih'` using `ih fun i hi => hx i (by omega)`. Establish `hN` using `hx N (by omega)`. Proceed by induction on `a with`. Consider the case `zero => exact base _ _`. Consider the case `succ a iha`.

Rewrite using `[hs_succ, map_add, map_add, map_mul, iha, ih', hN]`. Establish `e1 : N + 1 + a - 1 = N + a` using `by omega`. Establish `e2 : N + (a + 1) - 1 = N + a` using `by omega`. Establish `e3 : N + 1 + (a + 1) - 1 = N + a + 1` using `by omega`. Establish `e4 : a + 1 + r = a + r + 1` using `by omega`.

Rewrite using `[e1, e2, e3, e4, Nat.choose_succ_succ' (N + a) (a + r), Nat.add_sub_cancel]`. Consider the cases of `r with`. Consider the case `zero => simp`. Consider the case `succ r`. Rewrite using `[if_neg (Nat.succ_ne_zero r), map_mul, ih', hN, e2]`.

Establish `e5 : a + 1 + (r + 1 - 1) = a + (r + 1)` using `by omega`. Establish `e6 : a + (r + 1) - 1 = a + r` using `by omega`. Establish `e7 : (a + (r + 1)).choose (r + 1) = (a + r).choose r + (a + r).choose (r + 1)` using `Nat.choose_succ_succ' (a + r) r`. Rewrite using `[e5, e6, e7, Nat.add_sub_cancel]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_hs {T : Type} [CommRing T] (f : R →+* T) (N : ℕ) (hx : ∀ i < N, f (x i) = 1) :
    ∀ a r, f (hs x N a r) = (((N + a - 1).choose (a + r) * (a + r - 1).choose r : ℕ) : T) := by
  have base : ∀ N r, f (hs x N 0 r) =
      (((N + 0 - 1).choose (0 + r) * (0 + r - 1).choose r : ℕ) : T) := by
    intro N r
    rw [hs_zero_length]
    split_ifs with h
    · subst h; simp
    · rw [Nat.choose_eq_zero_of_lt (n := 0 + r - 1) (by omega)]; simp
  induction N with
  | zero =>
    intro a r
    cases a with
    | zero => exact base _ _
    | succ a => rw [hs_zero_variables, Nat.choose_eq_zero_of_lt (n := 0 + (a + 1) - 1) (by omega)]; simp
  | succ N ih =>
    intro a r
    have ih' := ih fun i hi => hx i (by omega)
    have hN := hx N (by omega)
    induction a with
    | zero => exact base _ _
    | succ a iha =>
      rw [hs_succ, map_add, map_add, map_mul, iha, ih', hN]
      have e1 : N + 1 + a - 1 = N + a := by omega
      have e2 : N + (a + 1) - 1 = N + a := by omega
      have e3 : N + 1 + (a + 1) - 1 = N + a + 1 := by omega
      have e4 : a + 1 + r = a + r + 1 := by omega
      rw [e1, e2, e3, e4, Nat.choose_succ_succ' (N + a) (a + r), Nat.add_sub_cancel]
      cases r with
      | zero => simp
      | succ r =>
        rw [if_neg (Nat.succ_ne_zero r), map_mul, ih', hN, e2]
        have e5 : a + 1 + (r + 1 - 1) = a + (r + 1) := by omega
        have e6 : a + (r + 1) - 1 = a + r := by omega
        have e7 : (a + (r + 1)).choose (r + 1) = (a + r).choose r + (a + r).choose (r + 1) :=
          Nat.choose_succ_succ' (a + r) r
        rw [e5, e6, e7, Nat.add_sub_cancel]
        push_cast; ring

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Use `set V : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i c => x i ^ rho (n + 1) c with hV`. Use `set M : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i c => x i ^ hookRho (n + 1) k r c with hM`. Set `j : Fin (n + 1)` to `⟨r, by omega⟩`. Establish `h1` using `Matrix.det_updateCol_sum V j (fun c => (-1) ^ (c : ℕ) * hs x (n + 1) (k - r) c)`.

Establish `h2 : V.updateCol j (fun i => ∑ c : Fin (n + 1), ((-1) ^ (c : ℕ) * hs x (n + 1) (k - r) c) • V i c) = M.submatrix id j.cycleRange`. Use extensionality with `i c`. Rewrite using `[Matrix.submatrix_apply, Matrix.updateCol_apply]`. Break down `lt_trichotomy c j with h | h | h` into its components or cases. Rewrite using `[if_neg h.ne]`.

Establish `hc : ((j.cycleRange c : Fin (n + 1)) : ℕ) = c + 1` using `Fin.coe_cycleRange_of_lt h`. Establish `h' : (c : ℕ) < r` using `h`. Simplify using `only [hV, hM, Matrix.of_apply, id, hookRho, rho, hc]`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, Fin.cycleRange_self]`. Use `rem_eq x (n + 1) (k - r) i i.2` as an intermediate fact. Rewrite `this` using `[rem, ← Fin.sum_univ_eq_sum_range (fun c => (-1) ^ c * hs x (n + 1) (k - r) c * x i ^ (n + 1 - 1 - c))]`.

Simplify using `only [hV, hM, Matrix.of_apply, id, hookRho, rho, smul_eq_mul]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h.ne', Fin.cycleRange_of_gt h]`. Establish `h' : r < (c : ℕ)` using `h`.

Simplify using `only [hV, hM, Matrix.of_apply, id, hookRho, rho]`. Rewrite using `[if_neg (by omega), if_neg (by omega), add_zero]`. Rewrite `h1` using `[h2, Matrix.det_permute', Fin.sign_cycleRange, smul_eq_mul]`. Establish `h3 : ((-1 : R) ^ r) * M.det = (-1) ^ r * (hs x (n + 1) (k - r) r * V.det)`. Rewrite using `[← mul_assoc]`.

Simplify `h1` using `[j]`. Establish `hu : IsUnit ((-1 : R) ^ r)` using `(isUnit_one.neg).pow r`. Conclude with `hu.mul_left_cancel h3`.
-/
theorem det_hook (N k r : ℕ) (hr : r < k) (hk : k ≤ N) :
    Matrix.det (Matrix.of fun i c : Fin N => x i ^ hookRho N k r c) =
      hs x N (k - r) r * Matrix.det (Matrix.of fun i c : Fin N => x i ^ rho N c) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i c => x i ^ rho (n + 1) c with hV
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun i c => x i ^ hookRho (n + 1) k r c with hM
  let j : Fin (n + 1) := ⟨r, by omega⟩
  have h1 := Matrix.det_updateCol_sum V j (fun c => (-1) ^ (c : ℕ) * hs x (n + 1) (k - r) c)
  have h2 : V.updateCol j (fun i => ∑ c : Fin (n + 1),
      ((-1) ^ (c : ℕ) * hs x (n + 1) (k - r) c) • V i c) = M.submatrix id j.cycleRange := by
    ext i c
    rw [Matrix.submatrix_apply, Matrix.updateCol_apply]
    rcases lt_trichotomy c j with h | h | h
    · rw [if_neg h.ne]
      have hc : ((j.cycleRange c : Fin (n + 1)) : ℕ) = c + 1 := Fin.coe_cycleRange_of_lt h
      have h' : (c : ℕ) < r := h
      simp only [hV, hM, Matrix.of_apply, id, hookRho, rho, hc]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    · subst h
      rw [if_pos rfl, Fin.cycleRange_self]
      have := rem_eq x (n + 1) (k - r) i i.2
      rw [rem, ← Fin.sum_univ_eq_sum_range
        (fun c => (-1) ^ c * hs x (n + 1) (k - r) c * x i ^ (n + 1 - 1 - c))] at this
      simp only [hV, hM, Matrix.of_apply, id, hookRho, rho, smul_eq_mul]
      rw [this]; simp
    · rw [if_neg h.ne', Fin.cycleRange_of_gt h]
      have h' : r < (c : ℕ) := h
      simp only [hV, hM, Matrix.of_apply, id, hookRho, rho]
      rw [if_neg (by omega), if_neg (by omega), add_zero]
  rw [h2, Matrix.det_permute', Fin.sign_cycleRange, smul_eq_mul] at h1
  have h3 : ((-1 : R) ^ r) * M.det = (-1) ^ r * (hs x (n + 1) (k - r) r * V.det) := by
    rw [← mul_assoc]
    simpa [j] using h1
  have hu : IsUnit ((-1 : R) ^ r) := (isUnit_one.neg).pow r
  exact hu.mul_left_cancel h3

end

/- English proof (translation)
Introduce `N k r hr hk`. Set `x : ℕ → MvPolynomial (Fin N) ℝ` to `fun i => if h : i < N then X ⟨i, h⟩ else 0`. Establish `hx : ∀ i : Fin N, x i = X i` using `fun i => by simp [x]`. Establish `ek : k - r + r = k` using `by omega`. Use `⟨hs x N (k - r) r, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `hs_induct x (fun d p => p.IsHomogeneous d) (fun d => isHomogeneous_zero _ _ d) (isHomogeneous_one _ _) (fun d p q hp hq => hp.add hq) (fun d i p hp => by` as an intermediate fact. Establish `h1 : (x i).IsHomogeneous 1`. Simplify using `only [x]`. Use `split_ifs`. Conclude with `isHomogeneous_X _ _`.

Conclude with `isHomogeneous_zero _ _ _`. Rewrite using `[add_comm]`. Conclude with `h1.mul hp) N (k - r) r`. Rewrite `this` using `[ek]`. Then use the resulting hypothesis. Use `hs_induct x (fun _ p => ∀ m, 0 ≤ p.coeff m) (fun d m => by simp) (fun m => ?_) (fun d p q hp hq m => ?_) (fun d i p hp m => ?_) N (k - r) r` and prove the remaining obligations.

Apply the tactic sequence `rw [coeff_one]; split_ifs <;> norm_num`. Rewrite using `[coeff_add]`. Conclude with `add_nonneg (hp m) (hq m)`. Simplify using `only [x] split_ifs`. Rewrite using `[coeff_X_mul'] split_ifs`.

Conclude with `hp _`. Conclude with `le_rfl`. Simplify using the standard rewrite rules. Rewrite using `[map_hs x (eval fun _ => (1 : ℝ)) N (fun i hi => by simp [x, hi]) (k - r) r, ek]`. Establish `: N + (k - r) - 1 = N + k - r - 1` using `by omega`.

Rewrite using `[this]`. Use `det_hook x N k r hr hk` as an intermediate fact. Simplify `this` using `only [hx]`.
-/
theorem exists_hookSchur : ∀ (N k r : ℕ), r < k → k ≤ N → ∃ S : MvPolynomial (Fin N) ℝ, S.IsHomogeneous k ∧ (∀ m, 0 ≤ S.coeff m) ∧ eval (fun _ => 1) S = ((N + k - r - 1).choose k * (k - 1).choose r : ℕ) ∧ Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ hookRho N k r c) = S * Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ rho N c) := by
  intro N k r hr hk
  let x : ℕ → MvPolynomial (Fin N) ℝ := fun i => if h : i < N then X ⟨i, h⟩ else 0
  have hx : ∀ i : Fin N, x i = X i := fun i => by simp [x]
  have ek : k - r + r = k := by omega
  refine ⟨hs x N (k - r) r, ?_, ?_, ?_, ?_⟩
  · have := hs_induct x (fun d p => p.IsHomogeneous d) (fun d => isHomogeneous_zero _ _ d)
      (isHomogeneous_one _ _) (fun d p q hp hq => hp.add hq) (fun d i p hp => by
        have h1 : (x i).IsHomogeneous 1 := by
          simp only [x]
          split_ifs
          · exact isHomogeneous_X _ _
          · exact isHomogeneous_zero _ _ _
        rw [add_comm]
        exact h1.mul hp) N (k - r) r
    rwa [ek] at this
  · refine hs_induct x (fun _ p => ∀ m, 0 ≤ p.coeff m) (fun d m => by simp) (fun m => ?_)
      (fun d p q hp hq m => ?_) (fun d i p hp m => ?_) N (k - r) r
    · rw [coeff_one]; split_ifs <;> norm_num
    · rw [coeff_add]; exact add_nonneg (hp m) (hq m)
    · simp only [x]
      split_ifs
      · rw [coeff_X_mul']
        split_ifs
        · exact hp _
        · exact le_rfl
      · simp
  · rw [map_hs x (eval fun _ => (1 : ℝ)) N (fun i hi => by simp [x, hi]) (k - r) r, ek]
    have : N + (k - r) - 1 = N + k - r - 1 := by omega
    rw [this]
  · have := det_hook x N k r hr hk
    simpa only [hx] using this

end GlobalTheory.HookSchur
