import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
namespace GlobalTheory.CompanionTheory.TruncLog

variable {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J)

/- English proof (translation)
Establish `h` using `δ.mul_dpow (m := 1) (n := a) hx`. Rewrite `h` using `[δ.dpow_one hx]`. Rewrite using `[h, Nat.choose_one_right, add_comm 1 a]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_dpow_eq_succ {x : A} (hx : x ∈ J) (a : ℕ) :
    x * δ.dpow a x = ((a : A) + 1) * δ.dpow (a + 1) x := by
  have h := δ.mul_dpow (m := 1) (n := a) hx
  rw [δ.dpow_one hx] at h
  rw [h, Nat.choose_one_right, add_comm 1 a]
  push_cast
  ring

/- English proof (translation)
Take `⟨c, rfl⟩ : ∃ c, a = c + 1` from `⟨a - 1, by omega⟩`. Take `⟨d, hd⟩` from `Nat.factorial_dvd_factorial (show c ≤ k by omega)`. Rewrite using `[hd]`. Use `push_cast`. Rewrite using `[mul_comm (c.factorial : A), mul_assoc, hN c (by omega), mul_zero]`.
-/
theorem factorial_mul_dpow_eq_zero {N : ℕ} {x : A}
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) {a k : ℕ} (ha : N < a)
    (hk : a ≤ k + 1) : (k.factorial : A) * δ.dpow a x = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial (show c ≤ k by omega)
  rw [hd]
  push_cast
  rw [mul_comm (c.factorial : A), mul_assoc, hN c (by omega), mul_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `e : (((m + 1).factorial : ℕ) : A) = ((m : A) + 1) * (m.factorial : A)`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx, mul_one, e, Nat.cast_zero]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ n ih`. Establish `e1 : ((n + 1 + (m + 1)).factorial : A) = ((n : A) + m + 2) * ((n + (m + 1)).factorial : A)`.

Rewrite using `[show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((n + 1 + m).factorial : A) = ((n + (m + 1)).factorial : A)`. Rewrite using `[show n + 1 + m = n + (m + 1) by omega]`.

Establish `hxp` using `mul_dpow_eq_succ δ hx (n + 1)`. Rewrite using `[Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (n + 1), e1, e2]`. Move the coercions through the operations in `at hxp ⊢`. Take the linear combination `(-1 : A) ^ (n + 1) * ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) * hxp`.
-/
theorem one_add_mul_sum_succ {x : A} (hx : x ∈ J) (m n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + (m + 1)).factorial : A) * δ.dpow a x =
      ((m : A) + 1) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x
      + (-1) ^ n * ((n + (m + 1)).factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    have e : (((m + 1).factorial : ℕ) : A) = ((m : A) + 1) * (m.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, e, Nat.cast_zero]
    ring
  | succ n ih =>
    have e1 : ((n + 1 + (m + 1)).factorial : A)
        = ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have e2 : ((n + 1 + m).factorial : A) = ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + m = n + (m + 1) by omega]
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (n + 1), e1, e2]
    push_cast at hxp ⊢
    linear_combination
      (-1 : A) ^ (n + 1) * ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) * hxp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]`. Consider the case `succ n ih`. Establish `e1 : ((n + 1).factorial : A) = ((n : A) + 1) * (n.factorial : A)`.

Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hxp` using `mul_dpow_eq_succ δ hx (n + 1)`. Rewrite using `[Finset.sum_range_succ, mul_add, ih, e1]`.

Move the coercions through the operations in `at hxp ⊢`. Take the linear combination `(-1 : A) ^ (n + 1) * ((n : A) + 1) * (n.factorial : A) * hxp`.
-/
theorem one_add_mul_sum_zero {x : A} (hx : x ∈ J) (n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1), (-1 : A) ^ a * (a.factorial : A) * δ.dpow a x =
      1 + (-1) ^ n * (n.factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]
  | succ n ih =>
    have e1 : ((n + 1).factorial : A) = ((n : A) + 1) * (n.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, e1]
    push_cast at hxp ⊢
    linear_combination (-1 : A) ^ (n + 1) * ((n : A) + 1) * (n.factorial : A) * hxp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Simplify using `only [zero_add, pow_one, add_zero, Nat.factorial_zero, Nat.cast_one]`. Rewrite using `[one_add_mul_sum_zero δ hx N]`. Use `hN N le_rfl` as an intermediate fact.

Take the linear combination `((-1 : A) ^ N * ((N : A) + 1)) * this`. Consider the case `succ m ih`. Establish `z` using `factorial_mul_dpow_eq_zero δ hN (a := N + 1) (k := N + (m + 1)) (by omega) (by omega)`. Rewrite using `[pow_succ, mul_assoc, one_add_mul_sum_succ δ hx m N, Nat.factorial_succ]`. Use `push_cast`.

Take the linear combination `((m : A) + 1) * ih + (1 + x) ^ (m + 1) * (-1 : A) ^ N * ((N : A) + 1) * z`.
-/
theorem one_add_pow_mul_sum {N : ℕ} {x : A} (hx : x ∈ J)
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) (m : ℕ) :
    (1 + x) ^ (m + 1) * ∑ a ∈ Finset.range (N + 1),
      (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x = (m.factorial : A) := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [one_add_mul_sum_zero δ hx N]
    have := hN N le_rfl
    linear_combination ((-1 : A) ^ N * ((N : A) + 1)) * this
  | succ m ih =>
    have z := factorial_mul_dpow_eq_zero δ hN (a := N + 1) (k := N + (m + 1)) (by omega) (by omega)
    rw [pow_succ, mul_assoc, one_add_mul_sum_succ δ hx m N, Nat.factorial_succ]
    push_cast
    linear_combination ((m : A) + 1) * ih
      + (1 + x) ^ (m + 1) * (-1 : A) ^ N * ((N : A) + 1) * z

/- English proof (translation)
Rewrite using `[← Finset.sum_product' (f := g), ← Finset.sum_fiberwise_of_maps_to (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (t := Finset.range (M + 1)) (g := fun p => p.1 + p.2) (by intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `symm`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `p hp`.

Simplify using `only [Finset.mem_filter] at hp`. Simplify using `using hp.2`. Introduce `p hp hp'`. Simplify using `only [Finset.HasAntidiagonal.mem_antidiagonal] at hp`. Simplify using `only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hp'`.

Apply `hg` to reduce the goal to its premises. Assume the negation of the conclusion as `hc`. Conclude with `hp' (by omega) hp`.
-/
theorem sum_antidiagonal_eq_sum_box (g : ℕ → ℕ → A) {N M : ℕ} (hM : 2 * N ≤ M)
    (hg : ∀ a b, N < a ∨ N < b → g a b = 0) :
    ∑ k ∈ Finset.range (M + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, g p.1 p.2 =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b := by
  rw [← Finset.sum_product' (f := g),
    ← Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (t := Finset.range (M + 1))
      (g := fun p => p.1 + p.2)
      (by intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  · intro p hp hp'
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hp'
    apply hg
    by_contra hc
    exact hp' (by omega) hp

/- English proof (translation)
Take `⟨x, rfl⟩ : ∃ x, v = 1 + x` from `⟨v - 1, by ring⟩`. Take `⟨y, rfl⟩ : ∃ y, w = 1 + y` from `⟨w - 1, by ring⟩`. Establish `hx : x ∈ J` using `by simpa using hv`. Establish `hy : y ∈ J` using `by simpa using hw`. Establish `hvy : (1 + x) * y ∈ J` using `J.mul_mem_left _ hy`.

Establish `hz : x + (1 + x) * y ∈ J` using `J.add_mem hx hvy`. Establish `dl : ∀ t : A, B.dlog δ N (1 + t) = ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) t`. Introduce `t`. Simplify using `[B.dlog]`. Establish `dz : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y)`.

Establish `: (1 + x) * (1 + y) = 1 + (x + (1 + x) * y)` using `by ring`. Rewrite using `[this, dl]`. Set `g : ℕ → ℕ → A` to `fun a b => (-1 : A) ^ (a + b + 1) * ((a + b - 1).factorial : A) * δ.dpow a x * ((1 + x) ^ b * δ.dpow b y)`. Establish `hg : ∀ a b, N < a ∨ N < b → g a b = 0`. Introduce `a b hab`.

Break down `hab with hab | hab` into its components or cases. Use `factorial_mul_dpow_eq_zero δ (fun k hk => h k hk x hx) (a := a) (k := a + b - 1) hab (by omega)` as an intermediate fact. Simplify using `only [g]`. Rewrite using `[mul_assoc ((-1 : A) ^ (a + b + 1)), this]`. Expand and normalize the polynomial expressions, which then agree.

Use `factorial_mul_dpow_eq_zero δ (fun k hk => h k hk y hy) (a := b) (k := a + b - 1) hab (by omega)` as an intermediate fact. Simplify using `only [g]`. Take the linear combination `((-1 : A) ^ (a + b + 1) * δ.dpow a x * (1 + x) ^ b) * this`. Establish `s1 : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range (2 * N), (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y)`. Rewrite using `[dz]`.

Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `k hk`. Simplify using `only [Finset.mem_range] at hk ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `k _ hk`.

Simplify using `only [Finset.mem_range, not_lt] at hk`. Rewrite using `[mul_assoc, h k hk _ hz, mul_zero]`. Establish `s2 : ∀ k, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), g p.1 p.2`. Introduce `k`. Rewrite using `[δ.dpow_add hx hvy, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p.1 + p.2 = k + 1` using `by simpa using hp`. Simplify using `only [g]`. Rewrite using `[hp', δ.dpow_mul hy, show k + 1 - 1 = k by omega]`. Expand and normalize the polynomial expressions, which then agree.

Establish `s3` using `sum_antidiagonal_eq_sum_box g (N := N) (M := 2 * N) le_rfl hg`. Rewrite `s3` using `[Finset.sum_range_succ']`. Establish `s4 : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b = g 0 0 + (B.dlog δ N (1 + x) + B.dlog δ N (1 + y))`. Rewrite using `[Finset.sum_comm, Finset.sum_range_succ', Finset.sum_range_succ' (fun a => g a 0), dl, dl]`. Establish `t1 : ∀ k, g (k + 1) 0 = (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) x`.

Introduce `k`. Simplify using `only [g, add_zero, pow_zero, δ.dpow_zero hy, show k + 1 - 1 = k by omega]`. Expand and normalize the polynomial expressions, which then agree. Establish `t2 : ∀ b, ∑ a ∈ Finset.range (N + 1), g a (b + 1) = (-1 : A) ^ b * (b.factorial : A) * δ.dpow (b + 1) y`. Introduce `b`.

Rewrite using `[← one_add_pow_mul_sum δ hx (fun k hk => h k hk x hx) b]`. Simplify using `only [g]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[show a + (b + 1) - 1 = a + b by omega]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [t1, t2]`. Expand and normalize the polynomial expressions, which then agree. Establish `s5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, g p.1 p.2 = g 0 0` using `by simp`. Rewrite `s3` using `[s5, s4]`.

Simplify using `only [← s2] at s3`. Rewrite using `[s1]`. Take the linear combination `s3`.
-/
theorem dlog_mul {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ)
    (h : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) (v w : A)
    (hv : v - 1 ∈ J) (hw : w - 1 ∈ J) :
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  obtain ⟨x, rfl⟩ : ∃ x, v = 1 + x := ⟨v - 1, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, w = 1 + y := ⟨w - 1, by ring⟩
  have hx : x ∈ J := by simpa using hv
  have hy : y ∈ J := by simpa using hw
  have hvy : (1 + x) * y ∈ J := J.mul_mem_left _ hy
  have hz : x + (1 + x) * y ∈ J := J.add_mem hx hvy
  have dl : ∀ t : A, B.dlog δ N (1 + t) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) t := by
    intro t; simp [B.dlog]
  have dz : B.dlog δ N ((1 + x) * (1 + y)) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    have : (1 + x) * (1 + y) = 1 + (x + (1 + x) * y) := by ring
    rw [this, dl]
  let g : ℕ → ℕ → A := fun a b => (-1 : A) ^ (a + b + 1) * ((a + b - 1).factorial : A) *
    δ.dpow a x * ((1 + x) ^ b * δ.dpow b y)
  have hg : ∀ a b, N < a ∨ N < b → g a b = 0 := by
    intro a b hab
    rcases hab with hab | hab
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk x hx) (a := a) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      rw [mul_assoc ((-1 : A) ^ (a + b + 1)), this]
      ring
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk y hy) (a := b) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      linear_combination
        ((-1 : A) ^ (a + b + 1) * δ.dpow a x * (1 + x) ^ b) * this
  have s1 : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range (2 * N),
      (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    rw [dz]
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [mul_assoc, h k hk _ hz, mul_zero]
  have s2 : ∀ k, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), g p.1 p.2 := by
    intro k
    rw [δ.dpow_add hx hvy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = k + 1 := by simpa using hp
    simp only [g]
    rw [hp', δ.dpow_mul hy, show k + 1 - 1 = k by omega]
    ring
  have s3 := sum_antidiagonal_eq_sum_box g (N := N) (M := 2 * N) le_rfl hg
  rw [Finset.sum_range_succ'] at s3
  have s4 : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b =
      g 0 0 + (B.dlog δ N (1 + x) + B.dlog δ N (1 + y)) := by
    rw [Finset.sum_comm, Finset.sum_range_succ', Finset.sum_range_succ' (fun a => g a 0), dl, dl]
    have t1 : ∀ k, g (k + 1) 0 = (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) x := by
      intro k
      simp only [g, add_zero, pow_zero, δ.dpow_zero hy, show k + 1 - 1 = k by omega]
      ring
    have t2 : ∀ b, ∑ a ∈ Finset.range (N + 1), g a (b + 1) =
        (-1 : A) ^ b * (b.factorial : A) * δ.dpow (b + 1) y := by
      intro b
      rw [← one_add_pow_mul_sum δ hx (fun k hk => h k hk x hx) b]
      simp only [g]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show a + (b + 1) - 1 = a + b by omega]
      ring
    simp only [t1, t2]
    ring
  have s5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, g p.1 p.2 = g 0 0 := by simp
  rw [s5, s4] at s3
  simp only [← s2] at s3
  rw [s1]
  linear_combination s3

end GlobalTheory.CompanionTheory.TruncLog
