import Mathlib

open Polynomial

/- English proof (translation)
Establish `hint : IsIntegral ℚ s`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hs]`. Conclude with `(isIntegral_natCast d).neg`. Establish `hz' : z ∈ Algebra.adjoin ℚ ({s} : Set E)`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hz`. Use `clear hz`. Proceed by induction on `hz' using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Rewrite `hx` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by simp [hx]⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`.

Take `⟨c, e, rfl⟩` from `hy`. Conclude with `⟨a + c, b + e, by push_cast; ring⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, e, rfl⟩` from `hy`.

Use `⟨a * c - d * b * e, a * e + b * c, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(b : E) * e * hs`.
-/
private lemma coords {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (z : E) (hz : z ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, z = (a : E) + (b : E) * s := by
  have hint : IsIntegral ℚ s := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hs]
    exact (isIntegral_natCast d).neg
  have hz' : z ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * e * hs

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C c => exact ⟨c, 0, by simp, by simp⟩`. Consider the case `add p q hp hq`. Take `⟨u, v, h1, h2⟩` from `hp`. Take `⟨u', v', h1', h2'⟩` from `hq`.

Use `⟨u + u', v + v', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, h1, h1']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, h2, h2']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `monomial n c h`. Take `⟨u, v, h1, h2⟩` from `h`. Use `⟨u * a - d * v * b, u * b + v * a, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, ← mul_assoc, map_mul, h1, aeval_X]`. Use `push_cast`. Take the linear combination `(v : E) * b * hs`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, h2, aeval_X]`. Use `push_cast`.

Take the linear combination `(v : E) * b * hs`.
-/
private lemma aeval_pair {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (a b : ℚ) (p : ℤ[X]) :
    ∃ u v : ℚ, aeval ((a : E) + (b : E) * s) p = (u : E) + (v : E) * s ∧
      aeval ((a : E) - (b : E) * s) p = (u : E) - (v : E) * s := by
  induction p using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, v, h1, h2⟩ := hp
    obtain ⟨u', v', h1', h2'⟩ := hq
    refine ⟨u + u', v + v', ?_, ?_⟩
    · rw [map_add, h1, h1']; push_cast; ring
    · rw [map_add, h2, h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨u, v, h1, h2⟩ := h
    refine ⟨u * a - d * v * b, u * b + v * a, ?_, ?_⟩
    · rw [pow_succ, ← mul_assoc, map_mul, h1, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs
    · rw [pow_succ, ← mul_assoc, map_mul, h2, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs

/- English proof (translation)
Take `⟨p, hp, h0⟩` from `h`. Take `⟨u, v, h1, h2⟩` from `aeval_pair d s hs a b p`. Rewrite `h0` using `[← aeval_def, h1]`. Establish `hn : u ^ 2 + d * v ^ 2 = 0`. Establish `: (u : E) ^ 2 + d * (v : E) ^ 2 = 0`.

Take the linear combination `((u : E) - v * s) * h0 + (v : E) ^ 2 * hs`. Conclude with `this` after adjusting the coercions. Establish `hd' : (0 : ℚ) < d` using `by exact_mod_cast hd`. Establish `hv2 : 0 ≤ (d : ℚ) * v ^ 2` using `by positivity`. Establish `hu : u = 0` using `by nlinarith [sq_nonneg u]`.

Establish `hv : v = 0`. Rewrite `hn` using `[hu]`. Establish `: (d : ℚ) * v ^ 2 = 0` using `by simpa using hn`. Simplify `this` using `[hd'.ne']`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Rewrite using `[← aeval_def, h2, hu, hv]`. Simplify using the standard rewrite rules.
-/
private lemma conj_integral {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hd : 0 < d)
    (hs : s ^ 2 = -(d : E)) (a b : ℚ) (h : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    IsIntegral ℤ ((a : E) - (b : E) * s) := by
  obtain ⟨p, hp, h0⟩ := h
  obtain ⟨u, v, h1, h2⟩ := aeval_pair d s hs a b p
  rw [← aeval_def, h1] at h0
  have hn : u ^ 2 + d * v ^ 2 = 0 := by
    have : (u : E) ^ 2 + d * (v : E) ^ 2 = 0 := by
      linear_combination ((u : E) - v * s) * h0 + (v : E) ^ 2 * hs
    exact_mod_cast this
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hv2 : 0 ≤ (d : ℚ) * v ^ 2 := by positivity
  have hu : u = 0 := by nlinarith [sq_nonneg u]
  have hv : v = 0 := by
    rw [hu] at hn
    have : (d : ℚ) * v ^ 2 = 0 := by simpa using hn
    simpa [hd'.ne'] using this
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, h2, hu, hv]
  simp

/- English proof (translation)
Establish `h' : IsIntegral ℤ q`. Use `(isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := E) (x := q) (algebraMap ℚ E).injective).1 (by simpa using h)` as an intermediate fact. Conclude with `this`. Simplify using `using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 h'`.
-/
private lemma rat_int {E : Type} [Field E] [CharZero E] (q : ℚ) (h : IsIntegral ℤ (q : E)) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have h' : IsIntegral ℤ q := by
    have := (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := E) (x := q)
      (algebraMap ℚ E).injective).1 (by simpa using h)
    exact this
  simpa using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 h'

/- English proof (translation)
Establish `h1 : q * q.den = q.num` using `Rat.mul_den_eq_num q`. Establish `h2 : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * m`. Establish `: (d : ℚ) * (q.num : ℚ) ^ 2 = (q.den : ℚ) ^ 2 * m`. Rewrite using `[← h1, h]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `this` after adjusting the coercions. Establish `hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2)` using `(Rat.isCoprime_num_den q).symm.pow`. Establish `h3 : (q.den : ℤ) ^ 2 ∣ d` using `hc.dvd_of_dvd_mul_right ⟨m, h2⟩`. Establish `h4 : q.den * q.den ∣ d`. Rewrite using `[← sq]`.

Conclude with `h3` after adjusting the coercions. Establish `h5 : q.den = 1` using `Nat.isUnit_iff.1 (hd _ h4)`. Conclude with `⟨q.num, by rw [← h1, h5]; simp⟩`.
-/
private lemma int_of_sqfree_mul_sq (d : ℕ) (hd : Squarefree d) (q : ℚ) (m : ℤ)
    (h : (m : ℚ) = d * q ^ 2) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
  have h2 : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * m := by
    have : (d : ℚ) * (q.num : ℚ) ^ 2 = (q.den : ℚ) ^ 2 * m := by
      rw [← h1, h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    (Rat.isCoprime_num_den q).symm.pow
  have h3 : (q.den : ℤ) ^ 2 ∣ d := hc.dvd_of_dvd_mul_right ⟨m, h2⟩
  have h4 : q.den * q.den ∣ d := by
    rw [← sq]; exact_mod_cast h3
  have h5 : q.den = 1 := Nat.isUnit_iff.1 (hd _ h4)
  exact ⟨q.num, by rw [← h1, h5]; simp⟩

/- English proof (translation)
Introduce `E _ _ d s hd hs z hz hi`. Take `⟨a, b, rfl⟩` from `coords d s hs z hz`. Establish `hc` using `conj_integral d s (Nat.pos_of_ne_zero hd.ne_zero) hs a b hi`. Take `⟨x, hx⟩` from `rat_int (E := E) (2 * a) (by`. Establish `e : ((2 * a : ℚ) : E) = (a : E) + (b : E) * s + ((a : E) - (b : E) * s)` using `by push_cast; ring`.

Rewrite using `[e]`. Conclude with `hi.add hc)`. Take `⟨n, hn⟩` from `rat_int (E := E) (a ^ 2 + d * b ^ 2) (by`. Establish `e : ((a ^ 2 + d * b ^ 2 : ℚ) : E) = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s)`. Use `push_cast`.

Take the linear combination `(b : E) ^ 2 * hs`. Rewrite using `[e]`. Conclude with `hi.mul hc)`. Take `⟨y, hy⟩` from `int_of_sqfree_mul_sq d hd (2 * b) (4 * n - x ^ 2) (by`. Use `push_cast`.

Rewrite using `[hx, hn]`. Use the proof step `ring)`. Establish `key : x ^ 2 + d * y ^ 2 = 4 * n`. Establish `: (x : ℚ) ^ 2 + d * (y : ℚ) ^ 2 = 4 * n`. Rewrite using `[hx, hy, hn]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Use `⟨x, y, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>`. Break down `Int.even_or_odd' y with ⟨l, rfl | rfl⟩` into its components or cases.

Conclude with `⟨k - l, by ring⟩`. It suffices to derive a contradiction. Establish `h4 : (4 : ℤ) ∣ d` using `⟨n - k ^ 2 - d * (l ^ 2 + l), by linear_combination key⟩`. Establish `h5 : 2 * 2 ∣ d` using `by exact_mod_cast h4`. Simplify using `using hd 2 h5`.

It suffices to derive a contradiction. Establish `h4 : 4 * (n - k ^ 2 - k - d * l ^ 2) = 1` using `by linear_combination -key`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨k - l, by ring⟩`. Establish `hx' : (x : E) = 2 * (a : E)` using `by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hx`.

Establish `hy' : (y : E) = 2 * (b : E)` using `by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hy`. Rewrite using `[hx', hy']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.integral_imag_quadratic_half_int :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), Squarefree d → s ^ 2 = -(d : E) → ∀ z : E, z ∈ IntermediateField.adjoin ℚ ({s} : Set E) → IsIntegral ℤ z → ∃ x y : ℤ, Even (x - y) ∧ z = ((x : E) + (y : E) * s) / 2 := by
  intro E _ _ d s hd hs z hz hi
  obtain ⟨a, b, rfl⟩ := coords d s hs z hz
  have hc := conj_integral d s (Nat.pos_of_ne_zero hd.ne_zero) hs a b hi
  obtain ⟨x, hx⟩ := rat_int (E := E) (2 * a) (by
    have e : ((2 * a : ℚ) : E) = (a : E) + (b : E) * s + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]
    exact hi.add hc)
  obtain ⟨n, hn⟩ := rat_int (E := E) (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E)
        = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast
      linear_combination (b : E) ^ 2 * hs
    rw [e]
    exact hi.mul hc)
  obtain ⟨y, hy⟩ := int_of_sqfree_mul_sq d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hx, hn]; ring)
  have key : x ^ 2 + d * y ^ 2 = 4 * n := by
    have : (x : ℚ) ^ 2 + d * (y : ℚ) ^ 2 = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  refine ⟨x, y, ?_, ?_⟩
  · rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>
      rcases Int.even_or_odd' y with ⟨l, rfl | rfl⟩
    · exact ⟨k - l, by ring⟩
    · exfalso
      have h4 : (4 : ℤ) ∣ d := ⟨n - k ^ 2 - d * (l ^ 2 + l), by linear_combination key⟩
      have h5 : 2 * 2 ∣ d := by exact_mod_cast h4
      simpa using hd 2 h5
    · exfalso
      have h4 : 4 * (n - k ^ 2 - k - d * l ^ 2) = 1 := by linear_combination -key
      omega
    · exact ⟨k - l, by ring⟩
  · have hx' : (x : E) = 2 * (a : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hx
    have hy' : (y : E) = 2 * (b : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hy
    rw [hx', hy']; ring
