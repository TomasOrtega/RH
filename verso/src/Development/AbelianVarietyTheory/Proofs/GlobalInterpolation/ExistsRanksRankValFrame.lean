import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Use `⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩` and prove the remaining obligations. Use `Nat.le_ceil (A / 2) push_cast` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Nat.ceil_lt_add_one (a := A / 2) (by linarith) push_cast; linarith` as an intermediate fact.
-/
theorem exists_even_between (A : ℝ) (hA : 2 ≤ A) : ∃ m : ℕ, Even m ∧ A ≤ m ∧ (m : ℝ) ≤ 2 * A := by
  refine ⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩
  · have := Nat.le_ceil (A / 2)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (a := A / 2) (by linarith)
    push_cast; linarith

/- English proof (translation)
Take `⟨n, h1, h2⟩` from `exists_nat_pow_near hA (by norm_num : (1 : ℝ) < 2)`. Use `⟨n + 1, ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`. Conclude with `h2.le`. Use `push_cast`.

Rewrite using `[pow_succ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_two_pow_between (A : ℝ) (hA : 1 ≤ A) :
    ∃ e : ℕ, A ≤ ((2 ^ e : ℕ) : ℝ) ∧ ((2 ^ e : ℕ) : ℝ) ≤ 2 * A := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hA (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, ?_, ?_⟩
  · push_cast; exact h2.le
  · push_cast; rw [pow_succ]; linarith

/- English proof (translation)
Take `⟨r, hr⟩ : ∃ r, r = k + m - 1` from `⟨_, rfl⟩`. Take `⟨f, hf⟩ : ∃ f, f = 2 * φ.ord` from `⟨_, rfl⟩`. Take `⟨p, hp⟩ : ∃ p, p = f * r` from `⟨_, rfl⟩`. Take `⟨q, hq⟩ : ∃ q, q = T * W` from `⟨_, rfl⟩`. Establish `hpr : r ≤ p`.

Rewrite using `[hp]; exact Nat.le_mul_of_pos_left _ (by omega)`. Take `⟨k', hk'⟩` from `hk`. Take `⟨m', hm'⟩` from `hm`. Establish `hmt : m ≤ 8 * p + 4 + 8 * q - r + 1` using `by omega`. Use `⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩, rfl, rfl, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.odd_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[sq]`. Conclude with `(Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)`. Use `show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)`.

Rewrite using `[← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_ranks_of_frame (φ : Formalism.HC.Frame) (k m T W : ℕ) (hk : Even k) (hm : Even m) (h2 : 2 ≤ m) (h3 : m + 3 ≤ k)
    (hmf : m ≤ 2 * φ.ord) (hfk : 2 * φ.ord ≤ k) :
    ∃ R : Ranks, R.toFrame = φ ∧ R.k = k ∧ R.m = m ∧ R.r + R.t = 8 * R.f * R.r + 4 + T * (8 * W) := by
  obtain ⟨r, hr⟩ : ∃ r, r = k + m - 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = 2 * φ.ord := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = f * r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = T * W := ⟨_, rfl⟩
  have hpr : r ≤ p := by
    rw [hp]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hmt : m ≤ 8 * p + 4 + 8 * q - r + 1 := by omega
  refine ⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · rw [Nat.odd_iff]; omega
  · rw [sq]
    exact (Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)
  · show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)
    rw [← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]
    omega

/- English proof (translation)
Introduce `eps h0 h1`. Use `⟨16, fun s hs hx φ he1 hp2 => ?_⟩` and prove the remaining obligations. Substitute `hs` using the available equality. Establish `hx1 : (1 : ℝ) ≤ s.x` using `by linarith`. Establish `hx0 : (0 : ℝ) < s.x` using `by linarith`.

Establish `hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps)`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)`. Establish `hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3`. Rewrite using `[← Real.rpow_natCast]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)`. Establish `he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3` using `by linarith`. Establish `hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps)`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)`.

Establish `hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8)`. Unfold `Scale.delta1`. Rewrite using `[sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]`. Establish `hA1 : 2 ≤ Real.sqrt (s.x * s.delta1)`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises.

Rewrite using `[hd]`. Establish `h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ)`. Rewrite using `[← Real.sqrt_eq_rpow]`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x`. Rewrite using `[Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)`.

Establish `p2 : 16 * s.x ≤ s.x ^ 2` using `by nlinarith`. Establish `p3 : 16 * s.x ^ 2 ≤ s.x ^ 3` using `by nlinarith`. Establish `p4 : 16 * s.x ^ 3 ≤ s.x ^ 4` using `by nlinarith`. Take `⟨m, hm, hm1, hm2⟩` from `exists_even_between _ hA1`. Take `⟨k, hk, hk1, hk2⟩` from `exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)`.

Establish `a1 : 2 ≤ m`. Establish `: ((2 : ℕ) : ℝ) ≤ m` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `a2 : m + 3 ≤ k`. Establish `: (m : ℝ) + 3 ≤ k` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `a3 : m ≤ 2 * φ.ord`. Establish `: (m : ℝ) ≤ 2 * (φ.ord : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `a4 : 2 * φ.ord ≤ k`.

Establish `: 2 * (φ.ord : ℝ) ≤ k` using `by linarith`. Conclude with `this` after adjusting the coercions. Take `⟨R, rfl, rfl, rfl, hR⟩` from `exists_ranks_of_frame φ k m (TOv s) ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) + ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4`. Conclude with `⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩`.
-/
theorem exists_ranks_rankVal_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∀ φ : Formalism.HC.Frame, s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
      ∃ R : Ranks, R.toFrame = φ ∧ RankVal s R := by
  intro eps h0 h1
  refine ⟨16, fun s hs hx φ he1 hp2 => ?_⟩
  subst hs
  have hx1 : (1 : ℝ) ≤ s.x := by linarith
  have hx0 : (0 : ℝ) < s.x := by linarith
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3 := by linarith
  have hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hA1 : 2 ≤ Real.sqrt (s.x * s.delta1) := by
    apply Real.le_sqrt_of_sq_le
    rw [hd]
    have h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
    rw [Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have p2 : 16 * s.x ≤ s.x ^ 2 := by nlinarith
  have p3 : 16 * s.x ^ 2 ≤ s.x ^ 3 := by nlinarith
  have p4 : 16 * s.x ^ 3 ≤ s.x ^ 4 := by nlinarith
  obtain ⟨m, hm, hm1, hm2⟩ := exists_even_between _ hA1
  obtain ⟨k, hk, hk1, hk2⟩ := exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)
  have a1 : 2 ≤ m := by
    have : ((2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m + 3 ≤ k := by
    have : (m : ℝ) + 3 ≤ k := by linarith
    exact_mod_cast this
  have a3 : m ≤ 2 * φ.ord := by
    have : (m : ℝ) ≤ 2 * (φ.ord : ℝ) := by linarith
    exact_mod_cast this
  have a4 : 2 * φ.ord ≤ k := by
    have : 2 * (φ.ord : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨R, rfl, rfl, rfl, hR⟩ := exists_ranks_of_frame φ k m (TOv s)
    ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) +
      ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4
  exact ⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩

/- English proof (translation)
Introduce `eps h0 h1`. Take `⟨x0, h⟩` from `exists_ranks_rankVal_frame eps h0 h1`. Use `⟨max x0 2, fun s hs hx => ?_⟩` and prove the remaining obligations. Establish `hx2 : (2 : ℝ) ≤ s.x` using `(le_max_right _ _).trans hx`. Establish `hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps)`.

Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)`. Establish `p2 : 4 ≤ s.x ^ 2` using `by nlinarith`. Take `⟨e, he1, he2⟩` from `exists_two_pow_between (s.x ^ (2 + 8 * s.eps)) (by linarith)`. Establish `a5 : 2 ≤ e`.

Establish `: ((4 : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ)`. Establish `: ((4 : ℕ) : ℝ) = 4` using `by norm_num`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 2 ^ 2 ≤ 2 ^ e` using `by exact_mod_cast this`. Conclude with `(Nat.pow_le_pow_iff_right (by norm_num)).1 h4`.

Take `⟨R, hφ, hR⟩` from `h s hs ((le_max_left _ _).trans hx) (Formalism.HC.cyclicFrame e) he1 he2`. Establish `hRe : R.e = e` using `congrArg Formalism.HC.Frame.e hφ`. Conclude with `⟨R, hR, hRe ▸ a5, hRe ▸ hφ⟩`.
-/
theorem exists_ranks_cyclic_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∃ R : Ranks, RankVal s R ∧ 2 ≤ R.e ∧ R.toFrame = Formalism.HC.cyclicFrame R.e := by
  intro eps h0 h1
  obtain ⟨x0, h⟩ := exists_ranks_rankVal_frame eps h0 h1
  refine ⟨max x0 2, fun s hs hx => ?_⟩
  have hx2 : (2 : ℝ) ≤ s.x := (le_max_right _ _).trans hx
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have p2 : 4 ≤ s.x ^ 2 := by nlinarith
  obtain ⟨e, he1, he2⟩ := exists_two_pow_between (s.x ^ (2 + 8 * s.eps)) (by linarith)
  have a5 : 2 ≤ e := by
    have : ((4 : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := by
      have : ((4 : ℕ) : ℝ) = 4 := by norm_num
      linarith
    have h4 : 2 ^ 2 ≤ 2 ^ e := by exact_mod_cast this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
  obtain ⟨R, hφ, hR⟩ := h s hs ((le_max_left _ _).trans hx) (Formalism.HC.cyclicFrame e)
    he1 he2
  have hRe : R.e = e := congrArg Formalism.HC.Frame.e hφ
  exact ⟨R, hR, hRe ▸ a5, hRe ▸ hφ⟩

end GlobalTheory.EX
