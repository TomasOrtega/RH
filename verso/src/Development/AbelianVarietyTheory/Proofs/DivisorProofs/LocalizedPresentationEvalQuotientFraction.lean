import Mathlib

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Introduce `R B _ _ c J n hn m r hgen`. Set `S : Subring B` to `{ carrier := {g | ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P} mul_mem' := by`. Introduce and unpack `a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩`. Use `⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_mul]`.

Conclude with `hQ₁.mul hQ₂`. Rewrite using `[eval₂_mul, eval₂_mul, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `one_mem' := ⟨1, 1, by simp, by simp⟩`. Use the proof step `add_mem' := by`.

Introduce and unpack `a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩`. Use `⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_mul]`. Conclude with `hQ₁.mul hQ₂`. Rewrite using `[eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h₁, ← h₂]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := ⟨0, 1, by simp, by simp⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `a ⟨P, Q, hQ, h⟩`. Use `⟨-P, Q, hQ, ?_⟩` and prove the remaining obligations.

Rewrite using `[eval₂_neg, ← h]`. Use `ring }`. Establish `hS : ∀ g, g ∈ S ↔ ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P` using `fun g => Iff.rfl`. Establish `hcS : ∀ a : R, c a ∈ S` using `fun a => (hS _).2 ⟨C a, 1, by simp, by simp⟩`. Use `set I := Ideal.map c J with hI`.

Establish `hdec : ∀ b : B, ∃ s ∈ S, b - s ∈ I`. Introduce `b`. Take `⟨P, Q, hQ, hb⟩` from `hgen b`. Take `⟨u, hu⟩` from `hQ`. Use `⟨eval₂ c r P * ↑u⁻¹, (hS _).2 ⟨P, Q, ⟨u, hu⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hu, mul_assoc, Units.inv_mul, mul_one]`. Establish `h1 : (↑u⁻¹ : B) * ↑u = 1` using `Units.inv_mul u`. Establish `: b - eval₂ c r P * ↑u⁻¹ = ↑u⁻¹ * (b * eval₂ c r Q - eval₂ c r P)`. Rewrite using `[← hu]`. Take the linear combination `(-b) * h1`.

Rewrite using `[this]`. Conclude with `I.mul_mem_left _ hb`. Establish `hstep : ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ s ∈ S, x - s ∈ I ^ (k + 1)`. Introduce `k x hx`. Establish `hIk : I ^ k = Ideal.span (c '' ↑(J ^ k))` using `by rw [hI, ← Ideal.map_pow]; rfl`.

Rewrite `hx` using `[hIk]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, -, rfl⟩` from `hy`. Conclude with `⟨c j, hcS j, by simp⟩`.

Consider the case `zero => exact ⟨0, S.zero_mem, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨s, hs, hys⟩` from `hy`. Take `⟨t, ht, hzt⟩` from `hz`. Use `⟨s + t, S.add_mem hs ht, ?_⟩` and prove the remaining obligations.

Use `Ideal.add_mem _ hys hzt` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul b y hy ih`. Take `⟨s, hs, hys⟩` from `ih`.

Take `⟨t, ht, hbt⟩` from `hdec b`. Use `⟨t * s, S.mul_mem ht hs, ?_⟩` and prove the remaining obligations. Establish `hy' : y ∈ I ^ k` using `hIk ▸ hy`. Establish `h1 : (b - t) * y ∈ I ^ (k + 1)`. Rewrite using `[pow_succ']`.

Conclude with `Ideal.mul_mem_mul hbt hy'`. Establish `h2 : t * (y - s) ∈ I ^ (k + 1)` using `Ideal.mul_mem_left _ _ hys`. Use `Ideal.add_mem _ h1 h2` as an intermediate fact. Rewrite using `[smul_eq_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `hall : ∀ k : ℕ, ∀ g : B, ∃ s ∈ S, g - s ∈ I ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro g; exact ⟨0, S.zero_mem, by simp⟩`.

Consider the case `succ k ih`. Introduce `g`. Take `⟨s, hs, hgs⟩` from `ih g`. Take `⟨t, ht, hxt⟩` from `hstep k _ hgs`. Use `⟨s + t, S.add_mem hs ht, ?_⟩` and prove the remaining obligations.

Use `hxt using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hIn : I ^ n = ⊥`. Rewrite using `[hI, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]`. Introduce `x hx`.

Rewrite using `[RingHom.mem_ker]`. Conclude with `hn x hx`. Introduce `g`. Take `⟨s, hs, hgs⟩` from `hall n g`. Rewrite `hgs` using `[hIn, Ideal.mem_bot, sub_eq_zero]`.

Conclude with `(hS g).1 (hgs ▸ hs)`.
-/
theorem exists_eval₂_fraction_of_exists_mod_nilpotent : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  intro R B _ _ c J n hn m r hgen
  let S : Subring B :=
    { carrier := {g | ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P}
      mul_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      neg_mem' := by
        rintro a ⟨P, Q, hQ, h⟩
        refine ⟨-P, Q, hQ, ?_⟩
        rw [eval₂_neg, ← h]; ring }
  have hS : ∀ g, g ∈ S ↔ ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P := fun g => Iff.rfl
  have hcS : ∀ a : R, c a ∈ S := fun a => (hS _).2 ⟨C a, 1, by simp, by simp⟩
  set I := Ideal.map c J with hI
  have hdec : ∀ b : B, ∃ s ∈ S, b - s ∈ I := by
    intro b
    obtain ⟨P, Q, hQ, hb⟩ := hgen b
    obtain ⟨u, hu⟩ := hQ
    refine ⟨eval₂ c r P * ↑u⁻¹, (hS _).2 ⟨P, Q, ⟨u, hu⟩, ?_⟩, ?_⟩
    · rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    · have h1 : (↑u⁻¹ : B) * ↑u = 1 := Units.inv_mul u
      have : b - eval₂ c r P * ↑u⁻¹ = ↑u⁻¹ * (b * eval₂ c r Q - eval₂ c r P) := by
        rw [← hu]; linear_combination (-b) * h1
      rw [this]; exact I.mul_mem_left _ hb
  have hstep : ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ s ∈ S, x - s ∈ I ^ (k + 1) := by
    intro k x hx
    have hIk : I ^ k = Ideal.span (c '' ↑(J ^ k)) := by rw [hI, ← Ideal.map_pow]; rfl
    rw [hIk] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨c j, hcS j, by simp⟩
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hys⟩ := hy
      obtain ⟨t, ht, hzt⟩ := hz
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      have := Ideal.add_mem _ hys hzt
      convert this using 1; ring
    | smul b y hy ih =>
      obtain ⟨s, hs, hys⟩ := ih
      obtain ⟨t, ht, hbt⟩ := hdec b
      refine ⟨t * s, S.mul_mem ht hs, ?_⟩
      have hy' : y ∈ I ^ k := hIk ▸ hy
      have h1 : (b - t) * y ∈ I ^ (k + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hbt hy'
      have h2 : t * (y - s) ∈ I ^ (k + 1) := Ideal.mul_mem_left _ _ hys
      have := Ideal.add_mem _ h1 h2
      rw [smul_eq_mul]
      convert this using 1; ring
  have hall : ∀ k : ℕ, ∀ g : B, ∃ s ∈ S, g - s ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro g; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨s, hs, hgs⟩ := ih g
      obtain ⟨t, ht, hxt⟩ := hstep k _ hgs
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      convert hxt using 1; ring
  have hIn : I ^ n = ⊥ := by
    rw [hI, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    exact hn x hx
  intro g
  obtain ⟨s, hs, hgs⟩ := hall n g
  rw [hIn, Ideal.mem_bot, sub_eq_zero] at hgs
  exact (hS g).1 (hgs ▸ hs)

end GlobalTheory
