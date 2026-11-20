import Mathlib

namespace GlobalTheory.AlgEquivTrivialPowerCongruence

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x _`. Simplify using `using h0 x`. Consider the case `succ k ih`.

Introduce `x hx`. Rewrite `hx` using `[pow_succ]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha q hq`. Establish `hd` using `ih a ha`.

Establish `hρa : ρ a ∈ Q ^ k`. Establish `h2 : ρ a - a ∈ Q ^ k` using `Ideal.pow_le_pow_right (Nat.le_succ k) hd`. Establish `h3` using `Ideal.add_mem _ h2 ha`. Simplify using `using h3`. Establish `e : ρ (a * q) - a * q = ρ a * (ρ q - q) + (ρ a - a) * q`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `h4` using `Ideal.mul_mem_mul hρa (h1 q hq)`.

Rewrite `h4` using `[← pow_add]`. Conclude with `h4`. Establish `h4` using `Ideal.mul_mem_mul hd hq`. Rewrite `h4` using `[← pow_succ]`. Conclude with `h4`.

Introduce `a b ha hb`. Establish `e : ρ (a + b) - (a + b) = (ρ a - a) + (ρ b - b)`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ ha hb`.
-/
theorem sub_mem_pow_succ {B : Type} [CommRing B] (Q : Ideal B) (ρ : B →+* B)
    (h0 : ∀ x, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro x _; simpa using h0 x
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha q hq
      have hd := ih a ha
      have hρa : ρ a ∈ Q ^ k := by
        have h2 : ρ a - a ∈ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) hd
        have h3 := Ideal.add_mem _ h2 ha
        simpa using h3
      have e : ρ (a * q) - a * q = ρ a * (ρ q - q) + (ρ a - a) * q := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have h4 := Ideal.mul_mem_mul hρa (h1 q hq)
        rw [← pow_add] at h4
        exact h4
      · have h4 := Ideal.mul_mem_mul hd hq
        rw [← pow_succ] at h4
        exact h4
    · intro a b ha hb
      have e : ρ (a + b) - (a + b) = (ρ a - a) + (ρ b - b) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

/- English proof (translation)
Establish `step : ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1)` using `sub_mem_pow_succ Q (ρ : B →+* B) h0 h1`. Establish `key : ∀ (k : ℕ) (x : B), ρ x - x ∈ Q ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `x`. Establish `hy` using `ih x`. Establish `hj : ∀ j : ℕ, (ρ ^ j) x - x - (j : B) * (ρ x - x) ∈ Q ^ (k + 1)`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ihj`. Establish `hz` using `step (k + 1) _ ihj`.

Establish `hz'` using `Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) hz) ihj`. Rewrite `hz'` using `[sub_add_cancel]`. Establish `hw` using `Ideal.mul_mem_left _ (j : B) (step k _ hy)`. Establish `h5` using `Ideal.add_mem _ hz' hw`. Use `h5 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[pow_succ', AlgEquiv.mul_apply]`. Simplify using `only [map_sub, map_mul, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmm` using `hj m`.

Rewrite `hmm` using `[hρ]`. Simplify using `only [AlgEquiv.one_apply, sub_self, zero_sub, neg_mem_iff] at hmm`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hm).1 hmm`. Establish `hbot : ⨅ k : ℕ, Q ^ k = ⊥` using `Ideal.iInf_pow_eq_bot_of_isDomain Q hQ`. Use extensionality with `x`.

Establish `hx : ρ x - x ∈ ⨅ k : ℕ, Q ^ k` using `Ideal.mem_iInf.2 fun k => key k x`. Rewrite `hx` using `[hbot, Ideal.mem_bot, sub_eq_zero]`. Simplify using `using hx`.
-/
theorem algEquiv_eq_one (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra A B] (Q : Ideal B) (ρ : B ≃ₐ[A] B) (m : ℕ) (hQ : Q ≠ ⊤) (hm : IsUnit (m : B))
    (hρ : ρ ^ m = 1) (h0 : ∀ x : B, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ρ = 1 := by
  have step : ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) :=
    sub_mem_pow_succ Q (ρ : B →+* B) h0 h1
  have key : ∀ (k : ℕ) (x : B), ρ x - x ∈ Q ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hy := ih x
      have hj : ∀ j : ℕ, (ρ ^ j) x - x - (j : B) * (ρ x - x) ∈ Q ^ (k + 1) := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hz := step (k + 1) _ ihj
          have hz' := Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) hz) ihj
          rw [sub_add_cancel] at hz'
          have hw := Ideal.mul_mem_left _ (j : B) (step k _ hy)
          have h5 := Ideal.add_mem _ hz' hw
          convert h5 using 1
          rw [pow_succ', AlgEquiv.mul_apply]
          simp only [map_sub, map_mul, map_natCast]
          push_cast
          ring
      have hmm := hj m
      rw [hρ] at hmm
      simp only [AlgEquiv.one_apply, sub_self, zero_sub, neg_mem_iff] at hmm
      exact (Ideal.unit_mul_mem_iff_mem _ hm).1 hmm
  have hbot : ⨅ k : ℕ, Q ^ k = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ
  ext x
  have hx : ρ x - x ∈ ⨅ k : ℕ, Q ^ k := Ideal.mem_iInf.2 fun k => key k x
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.AlgEquivTrivialPowerCongruence
