import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

structure nm_Hyp {K : Type*} [Field K] (R : Subring K) (p : ℕ) : Prop where
  one_lt : 1 < p
  val : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R
  rk : ∀ x : K, x ≠ 0 → (∃ n : ℕ, (p : K) ^ n / x ∈ R) ∧ (x⁻¹ ∉ R → ∃ n : ℕ, x ^ n / (p : K) ∈ R)
  pinv : (p : K)⁻¹ ∉ R

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}

/- English proof (translation)
Introduce `h0`. Apply `h.pinv` to reduce the goal to its premises. Rewrite using `[h0, inv_zero]`. Conclude with `R.zero_mem`.
-/
theorem nm_p_ne (h : nm_Hyp R p) : (p : K) ≠ 0 := by
  intro h0
  apply h.pinv
  rw [h0, inv_zero]
  exact R.zero_mem

/- English proof (translation)
Assume the negation of the conclusion as `hyR`. Establish `hy0 : y ≠ 0` using `fun h0 => hyR (h0 ▸ R.zero_mem)`. Establish `hinv : y⁻¹ ∈ R` using `(h.val y).resolve_left hyR`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Establish `e : y ^ (m + 1) * y⁻¹ ^ m = y`.

Rewrite using `[pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hy0, one_pow, mul_one]`. Conclude with `hyR (e ▸ R.mul_mem hy (R.pow_mem hinv _))`.
-/
theorem nm_root (h : nm_Hyp R p) {y : K} {k : ℕ} (hk : 0 < k) (hy : y ^ k ∈ R) : y ∈ R := by
  by_contra hyR
  have hy0 : y ≠ 0 := fun h0 => hyR (h0 ▸ R.zero_mem)
  have hinv : y⁻¹ ∈ R := (h.val y).resolve_left hyR
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : y ^ (m + 1) * y⁻¹ ^ m = y := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hy0, one_pow, mul_one]
  exact hyR (e ▸ R.mul_mem hy (R.pow_mem hinv _))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hk`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Apply `h.pinv` to reduce the goal to its premises.

Take `⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1)` from `⟨(-k - 1).toNat, by omega⟩`. Substitute `hn` using the available equality. Establish `e : (p : K) ^ (-((n : ℤ) + 1)) = ((p : K)⁻¹) ^ (n + 1)`. Rewrite using `[zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, inv_pow]`. Conclude with `nm_root h (Nat.succ_pos n) (e ▸ hk)`.

Introduce `hk lift k to ℕ using hk`. Rewrite using `[zpow_natCast]`. Conclude with `R.pow_mem (natCast_mem R p) k`.
-/
theorem nm_zpow_mem_iff (h : nm_Hyp R p) (k : ℤ) : (p : K) ^ k ∈ R ↔ 0 ≤ k := by
  constructor
  · intro hk
    by_contra hneg
    push_neg at hneg
    apply h.pinv
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hn
    have e : (p : K) ^ (-((n : ℤ) + 1)) = ((p : K)⁻¹) ^ (n + 1) := by
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, inv_pow]
    exact nm_root h (Nat.succ_pos n) (e ▸ hk)
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact R.pow_mem (natCast_mem R p) k

variable (R p)

def nm_P (x : K) (a : ℤ) (b : ℕ) : Prop := x ^ b * (p : K) ^ (-a) ∈ R

def rationalLowerBounds (x : K) : Set ℝ := {q | ∃ (a : ℤ) (b : ℕ), 0 < b ∧ q = (a : ℝ) / b ∧ nm_P R p x a b}

def nm_v (x : K) : ℝ := sSup (rationalLowerBounds R p x)

variable {R p}

/- English proof (translation)
Take `⟨n, hn⟩` from `(h.rk x⁻¹ (inv_ne_zero hx)).1`. Use `⟨_, -(n : ℤ), 1, one_pos, rfl, ?_⟩` and prove the remaining obligations. Unfold `nm_P`. Rewrite using `[pow_one, neg_neg, zpow_natCast, mul_comm]`. Rewrite `hn` using `[div_inv_eq_mul]`. Then use the resulting hypothesis.
-/
theorem nm_T_nonempty (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : (rationalLowerBounds R p x).Nonempty := by
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).1
  refine ⟨_, -(n : ℤ), 1, one_pos, rfl, ?_⟩
  unfold nm_P
  rw [pow_one, neg_neg, zpow_natCast, mul_comm]
  rwa [div_inv_eq_mul] at hn

/- English proof (translation)
Establish `hp0` using `nm_p_ne h`. Take `⟨n, hn⟩` from `(h.rk x hx).1`. Use `⟨n, ?_⟩` and prove the remaining obligations. Introduce and unpack `q ⟨a, b, hb, rfl, hP⟩`. Establish `hxb : x ^ b ≠ 0` using `pow_ne_zero _ hx`.

Establish `e : (p : K) ^ ((n : ℤ) * b - a) = ((p : K) ^ n / x) ^ b * (x ^ b * (p : K) ^ (-a))`. Rewrite using `[sub_eq_add_neg, zpow_add₀ hp0, ← Nat.cast_mul, zpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv, mul_assoc, inv_mul_cancel_left₀ hxb]`. Establish `hmem : (p : K) ^ ((n : ℤ) * b - a) ∈ R` using `e ▸ R.mul_mem (R.pow_mem hn b) hP`. Establish `h0` using `(nm_zpow_mem_iff h _).1 hmem`. Establish `hbR : (0 : ℝ) < b` using `by exact_mod_cast hb`.

Rewrite using `[div_le_iff₀ hbR]`. Establish `: (a : ℤ) ≤ (n : ℤ) * b` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem nm_T_bdd (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : BddAbove (rationalLowerBounds R p x) := by
  have hp0 := nm_p_ne h
  obtain ⟨n, hn⟩ := (h.rk x hx).1
  refine ⟨n, ?_⟩
  rintro q ⟨a, b, hb, rfl, hP⟩
  have hxb : x ^ b ≠ 0 := pow_ne_zero _ hx
  have e : (p : K) ^ ((n : ℤ) * b - a) = ((p : K) ^ n / x) ^ b * (x ^ b * (p : K) ^ (-a)) := by
    rw [sub_eq_add_neg, zpow_add₀ hp0, ← Nat.cast_mul, zpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv,
      mul_assoc, inv_mul_cancel_left₀ hxb]
  have hmem : (p : K) ^ ((n : ℤ) * b - a) ∈ R := e ▸ R.mul_mem (R.pow_mem hn b) hP
  have h0 := (nm_zpow_mem_iff h _).1 hmem
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have : (a : ℤ) ≤ (n : ℤ) * b := by linarith
  exact_mod_cast this

/- English proof (translation)
Unfold `nm_v`. Conclude with `le_csSup (nm_T_bdd h hx) ⟨a, b, hb, rfl, hP⟩`.
-/
theorem nm_le_v (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) {a : ℤ} {b : ℕ} (hb : 0 < b) (hP : nm_P R p x a b) :
    (a : ℝ) / b ≤ nm_v R p x := by
  unfold nm_v
  exact le_csSup (nm_T_bdd h hx) ⟨a, b, hb, rfl, hP⟩

/- English proof (translation)
Break down `h.val (x ^ b * (p : K) ^ (-a)) with h1 | h1` into its components or cases. Conclude with `Or.inl h1`. Use `right`. Unfold `nm_P`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[mul_inv, inv_pow, neg_neg, zpow_neg, inv_inv]`.
-/
theorem nm_dich (h : nm_Hyp R p) (x : K) (a : ℤ) (b : ℕ) : nm_P R p x a b ∨ nm_P R p x⁻¹ (-a) b := by
  rcases h.val (x ^ b * (p : K) ^ (-a)) with h1 | h1
  · exact Or.inl h1
  · right
    unfold nm_P
    convert h1 using 1
    rw [mul_inv, inv_pow, neg_neg, zpow_neg, inv_inv]

/- English proof (translation)
Unfold `nm_P at *`. Establish `e : (x * y) ^ (b * b') * (p : K) ^ (-(a * b' + a' * b)) = (x ^ b * (p : K) ^ (-a)) ^ b' * (y ^ b' * (p : K) ^ (-a')) ^ b`. Rewrite using `[mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← zpow_natCast ((p : K) ^ (-a)) b', ← zpow_natCast ((p : K) ^ (-a')) b, ← zpow_mul, ← zpow_mul, mul_comm b' b]`. Establish `: (p : K) ^ (-(a * b' + a' * b)) = (p : K) ^ (-a * b') * (p : K) ^ (-a' * b)`. Rewrite using `[← zpow_add₀ (nm_p_ne h)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `R.mul_mem (R.pow_mem hx _) (R.pow_mem hy _)`.
-/
theorem nm_P_mul (h : nm_Hyp R p) {x y : K} {a a' : ℤ} {b b' : ℕ} (hx : nm_P R p x a b) (hy : nm_P R p y a' b') :
    nm_P R p (x * y) (a * b' + a' * b) (b * b') := by
  unfold nm_P at *
  have e : (x * y) ^ (b * b') * (p : K) ^ (-(a * b' + a' * b)) =
      (x ^ b * (p : K) ^ (-a)) ^ b' * (y ^ b' * (p : K) ^ (-a')) ^ b := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← zpow_natCast ((p : K) ^ (-a)) b',
      ← zpow_natCast ((p : K) ^ (-a')) b, ← zpow_mul, ← zpow_mul, mul_comm b' b]
    have : (p : K) ^ (-(a * b' + a' * b)) = (p : K) ^ (-a * b') * (p : K) ^ (-a' * b) := by
      rw [← zpow_add₀ (nm_p_ne h)]; congr 1; ring
    rw [this]
    ring
  rw [e]
  exact R.mul_mem (R.pow_mem hx _) (R.pow_mem hy _)

/- English proof (translation)
Establish `hxy : x * y ≠ 0` using `mul_ne_zero hx hy`. Establish `h1 : ∀ q' ∈ rationalLowerBounds R p y, nm_v R p x ≤ nm_v R p (x * y) - q'`. Introduce and unpack `q' ⟨a', b', hb', rfl, hP'⟩`. Apply `csSup_le (nm_T_nonempty h hx)` to reduce the goal to its premises. Introduce and unpack `q ⟨a, b, hb, rfl, hP⟩`.

Establish `h2` using `nm_le_v h hxy (Nat.mul_pos hb hb') (nm_P_mul h hP hP')`. Establish `hbR : (b : ℝ) ≠ 0` using `by exact_mod_cast hb.ne'`. Establish `hbR' : (b' : ℝ) ≠ 0` using `by exact_mod_cast hb'.ne'`. Establish `e : (((a * b' + a' * b : ℤ) : ℝ)) / ((b * b' : ℕ) : ℝ) = (a : ℝ) / b + (a' : ℝ) / b'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite `h2` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : nm_v R p y ≤ nm_v R p (x * y) - nm_v R p x`. Apply `csSup_le (nm_T_nonempty h hy)` to reduce the goal to its premises.

Introduce `q' hq'`. Use `h1 q' hq'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nm_v_mul_ge (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p x + nm_v R p y ≤ nm_v R p (x * y) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have h1 : ∀ q' ∈ rationalLowerBounds R p y, nm_v R p x ≤ nm_v R p (x * y) - q' := by
    rintro q' ⟨a', b', hb', rfl, hP'⟩
    apply csSup_le (nm_T_nonempty h hx)
    rintro q ⟨a, b, hb, rfl, hP⟩
    have h2 := nm_le_v h hxy (Nat.mul_pos hb hb') (nm_P_mul h hP hP')
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbR' : (b' : ℝ) ≠ 0 := by exact_mod_cast hb'.ne'
    have e : (((a * b' + a' * b : ℤ) : ℝ)) / ((b * b' : ℕ) : ℝ) = (a : ℝ) / b + (a' : ℝ) / b' := by
      push_cast
      field_simp
    rw [e] at h2
    linarith
  have h3 : nm_v R p y ≤ nm_v R p (x * y) - nm_v R p x := by
    apply csSup_le (nm_T_nonempty h hy)
    intro q' hq'
    have := h1 q' hq'
    linarith
  linarith

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `csSup_le (nm_T_nonempty h one_ne_zero)` to reduce the goal to its premises. Introduce and unpack `q ⟨a, b, hb, rfl, hP⟩`. Unfold `nm_P at hP`. Rewrite `hP` using `[one_pow, one_mul]`.

Use `(nm_zpow_mem_iff h _).1 hP` as an intermediate fact. Establish `ha : (a : ℝ) ≤ 0`. Establish `: a ≤ 0` using `by linarith`. Conclude with `this` after adjusting the coercions. Conclude with `div_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)`.

Use `nm_le_v h (one_ne_zero (α := K)) (a := 0) (b := 1) Nat.one_pos (by` as an intermediate fact. Unfold `nm_P`. Simplify using `only [pow_one, neg_zero, zpow_zero, mul_one]`. Conclude with `R.one_mem)`. Simplify using `using this`.
-/
theorem nm_v_one (h : nm_Hyp R p) : nm_v R p (1 : K) = 0 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h one_ne_zero)
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [one_pow, one_mul] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have ha : (a : ℝ) ≤ 0 := by
      have : a ≤ 0 := by linarith
      exact_mod_cast this
    exact div_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)
  · have := nm_le_v h (one_ne_zero (α := K)) (a := 0) (b := 1) Nat.one_pos (by
      unfold nm_P
      simp only [pow_one, neg_zero, zpow_zero, mul_one]
      exact R.one_mem)
    simpa using this

/- English proof (translation)
Establish `hx'` using `inv_ne_zero hx`. Establish `h1 : nm_v R p x + nm_v R p x⁻¹ ≤ 0`. Use `nm_v_mul_ge h hx hx'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hx, nm_v_one h]`. Then use the resulting hypothesis. Establish `h2 : 0 ≤ nm_v R p x + nm_v R p x⁻¹`.

Assume the negation of the conclusion as `hneg`. Establish `hlt : nm_v R p x < -nm_v R p x⁻¹` using `by linarith`. Take `⟨q, hq1, hq2⟩` from `exists_rat_btwn hlt`. Establish `hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ)`. Conclude with `(Rat.num_div_den q).symm` after adjusting the coercions.

Break down `nm_dich h x q.num q.den with h3 | h3` into its components or cases. Use `nm_le_v h hx q.den_pos h3` as an intermediate fact. Rewrite `this` using `[← hq]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `nm_le_v h hx' q.den_pos h3` as an intermediate fact.

Establish `e : (((-q.num : ℤ)) : ℝ) / (q.den : ℝ) = -(q : ℝ)`. Rewrite using `[hq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nm_v_inv (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : nm_v R p x⁻¹ = -nm_v R p x := by
  have hx' := inv_ne_zero hx
  have h1 : nm_v R p x + nm_v R p x⁻¹ ≤ 0 := by
    have := nm_v_mul_ge h hx hx'
    rwa [mul_inv_cancel₀ hx, nm_v_one h] at this
  have h2 : 0 ≤ nm_v R p x + nm_v R p x⁻¹ := by
    by_contra hneg
    have hlt : nm_v R p x < -nm_v R p x⁻¹ := by linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rcases nm_dich h x q.num q.den with h3 | h3
    · have := nm_le_v h hx q.den_pos h3
      rw [← hq] at this
      linarith
    · have := nm_le_v h hx' q.den_pos h3
      have e : (((-q.num : ℤ)) : ℝ) / (q.den : ℝ) = -(q : ℝ) := by
        rw [hq]; push_cast; ring
      rw [e] at this
      linarith
  linarith

/- English proof (translation)
Apply `le_antisymm _ (nm_v_mul_ge h hx hy)` to reduce the goal to its premises. Establish `h1` using `nm_v_mul_ge h (mul_ne_zero hx hy) (inv_ne_zero hy)`. Rewrite `h1` using `[mul_assoc, mul_inv_cancel₀ hy, mul_one, nm_v_inv h hy]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nm_v_mul (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p (x * y) = nm_v R p x + nm_v R p y := by
  apply le_antisymm _ (nm_v_mul_ge h hx hy)
  have h1 := nm_v_mul_ge h (mul_ne_zero hx hy) (inv_ne_zero hy)
  rw [mul_assoc, mul_inv_cancel₀ hy, mul_one, nm_v_inv h hy] at h1
  linarith

/- English proof (translation)
Use `nm_le_v h hx (a := 0) (b := 1) Nat.one_pos (by` as an intermediate fact. Unfold `nm_P`. Simplify using `only [pow_one, neg_zero, zpow_zero, mul_one]`. Conclude with `hxR)`. Simplify using `using this`.
-/
theorem nm_v_nonneg (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) (hxR : x ∈ R) : 0 ≤ nm_v R p x := by
  have := nm_le_v h hx (a := 0) (b := 1) Nat.one_pos (by
    unfold nm_P
    simp only [pow_one, neg_zero, zpow_zero, mul_one]
    exact hxR)
  simpa using this

/- English proof (translation)
Establish `hx : x ≠ 0` using `fun h0 => hxR (h0 ▸ R.zero_mem)`. Take `⟨n, hn⟩` from `(h.rk x⁻¹ (inv_ne_zero hx)).2 (by rwa [inv_inv])`. Establish `hn0 : 0 < n`. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. It suffices to derive a contradiction.

Rewrite `hn` using `[h0, pow_zero, one_div]`. Conclude with `h.pinv hn`. Conclude with `h0`. Establish `h1` using `nm_le_v h (inv_ne_zero hx) (a := 1) (b := n) hn0 (by`. Unfold `nm_P`.

Rewrite using `[zpow_neg_one, ← div_eq_mul_inv]`. Conclude with `hn)`. Rewrite `h1` using `[nm_v_inv h hx]`. Establish `: (0 : ℝ) < ((1 : ℤ) : ℝ) / (n : ℝ)`. Establish `: (0 : ℝ) < n` using `by exact_mod_cast hn0`.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nm_v_neg (h : nm_Hyp R p) {x : K} (hxR : x ∉ R) : nm_v R p x < 0 := by
  have hx : x ≠ 0 := fun h0 => hxR (h0 ▸ R.zero_mem)
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).2 (by rwa [inv_inv])
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_div] at hn
      exact h.pinv hn
    · exact h0
  have h1 := nm_le_v h (inv_ne_zero hx) (a := 1) (b := n) hn0 (by
    unfold nm_P
    rw [zpow_neg_one, ← div_eq_mul_inv]
    exact hn)
  rw [nm_v_inv h hx] at h1
  have : (0 : ℝ) < ((1 : ℤ) : ℝ) / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h0 => by by_contra hxR exact absurd (nm_v_neg h hxR) (not_lt.2 h0), nm_v_nonneg h hx⟩`.
-/
theorem nm_v_nonneg_iff (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : 0 ≤ nm_v R p x ↔ x ∈ R :=
  ⟨fun h0 => by
    by_contra hxR
    exact absurd (nm_v_neg h hxR) (not_lt.2 h0), nm_v_nonneg h hx⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `csSup_le (nm_T_nonempty h (nm_p_ne h))` to reduce the goal to its premises. Introduce and unpack `q ⟨a, b, hb, rfl, hP⟩`. Unfold `nm_P at hP`. Rewrite `hP` using `[← zpow_natCast, ← zpow_add₀ (nm_p_ne h)]`.

Use `(nm_zpow_mem_iff h _).1 hP` as an intermediate fact. Establish `hb' : (0 : ℝ) < b` using `by exact_mod_cast hb`. Rewrite using `[div_le_one hb']`. Establish `: a ≤ b` using `by linarith`. Conclude with `this` after adjusting the coercions.

Use `nm_le_v h (nm_p_ne h) (a := 1) (b := 1) Nat.one_pos (by` as an intermediate fact. Unfold `nm_P`. Rewrite using `[pow_one, zpow_neg_one, mul_inv_cancel₀ (nm_p_ne h)]`. Conclude with `R.one_mem)`. Simplify using `using this`.
-/
theorem nm_v_p (h : nm_Hyp R p) : nm_v R p (p : K) = 1 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h (nm_p_ne h))
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [← zpow_natCast, ← zpow_add₀ (nm_p_ne h)] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [div_le_one hb']
    have : a ≤ b := by linarith
    exact_mod_cast this
  · have := nm_le_v h (nm_p_ne h) (a := 1) (b := 1) Nat.one_pos (by
      unfold nm_P
      rw [pow_one, zpow_neg_one, mul_inv_cancel₀ (nm_p_ne h)]
      exact R.one_mem)
    simpa using this

/- English proof (translation)
Establish `key : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → x / y ∈ R → nm_v R p y ≤ nm_v R p (x + y)`. Introduce `x y _ hy hxy hR`. Establish `e : x + y = y * (1 + x / y)` using `by field_simp; ring`. Establish `h1 : 1 + x / y ≠ 0`. Introduce `h0`.

Apply `hxy` to reduce the goal to its premises. Rewrite using `[e, h0, mul_zero]`. Rewrite using `[e, nm_v_mul h hy h1]`. Use `nm_v_nonneg h h1 (R.add_mem R.one_mem hR)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Break down `h.val (x / y) with h1 | h1` into its components or cases. Conclude with `le_trans (min_le_right _ _) (key hx hy hxy h1)`. Rewrite `h1` using `[inv_div]`. Rewrite `hxy`, the goal using `[add_comm]`. Conclude with `le_trans (min_le_left _ _) (key hy hx hxy h1)`.
-/
theorem nm_v_add (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (nm_v R p x) (nm_v R p y) ≤ nm_v R p (x + y) := by
  have key : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → x / y ∈ R → nm_v R p y ≤ nm_v R p (x + y) := by
    intro x y _ hy hxy hR
    have e : x + y = y * (1 + x / y) := by field_simp; ring
    have h1 : 1 + x / y ≠ 0 := by
      intro h0
      apply hxy
      rw [e, h0, mul_zero]
    rw [e, nm_v_mul h hy h1]
    have := nm_v_nonneg h h1 (R.add_mem R.one_mem hR)
    linarith
  rcases h.val (x / y) with h1 | h1
  · exact le_trans (min_le_right _ _) (key hx hy hxy h1)
  · rw [inv_div] at h1
    rw [add_comm] at hxy ⊢
    exact le_trans (min_le_left _ _) (key hy hx hxy h1)

end Formalism.MainNotions.FormalGroupSystem.Pf
