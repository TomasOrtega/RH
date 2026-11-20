import Mathlib

namespace GlobalTheory.TwoCocycle

/- English proof (translation)
Establish `h1` using `hc a b (x * y)`. Establish `h2` using `hc b y x`. Establish `h3` using `hc a x (b * y)`. Rewrite `h2` using `[mul_comm y x, hs y x, hs (b * y) x]`. Rewrite `h3` using `[mul_left_comm x b y]`.

Take the linear combination `(norm := abel) h2 + h3 - h1`.
-/
theorem interchange {Γ D : Type} [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (a b x y : Γ) :
    c (a * b) (x * y) + c x y + c a b = c a x + c b y + c (a * x) (b * y) := by
  have h1 := hc a b (x * y)
  have h2 := hc b y x
  have h3 := hc a x (b * y)
  rw [mul_comm y x, hs y x, hs (b * y) x] at h2
  rw [mul_left_comm x b y] at h3
  linear_combination (norm := abel) h2 + h3 - h1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h` using `interchange c hs hc (x ^ n) (y ^ n) x y`. Rewrite `h` using `[← mul_pow]`.

Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, succ_nsmul, pow_succ x, pow_succ y]`. Take the linear combination `(norm := abel) ih + h`.
-/
theorem sum_pow_mul (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (n : ℕ) (x y : Γ) :
    ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y =
      ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y
        + c (x ^ n) (y ^ n) - c 1 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := interchange c hs hc (x ^ n) (y ^ n) x y
    rw [← mul_pow] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, succ_nsmul,
      pow_succ x, pow_succ y]
    linear_combination (norm := abel) ih + h

end GlobalTheory.TwoCocycle
