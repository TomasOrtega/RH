import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `A R _ _ _ φ hφ Q _ hQ hne`. Use `letI := φ.toAlgebra`. Use `haveI : Module.Flat A R := hφ`. Use `haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat`. Use `set p : Ideal A := Q.comap φ with hp`.

Use `haveI : p.IsPrime := Ideal.comap_isPrime φ Q`. Use `haveI : Q.LiesOver p := ⟨rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]`. Introduce `q hq hqp`.

Assume the negation of the conclusion as `hcon`. Establish `hq0 : q ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hcon`. Use `haveI := hq`.

Take `⟨P₁, hP₁Q, hP₁, hP₁o⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := q) (q := p) Q hqp`. Use `haveI := hP₁`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Take `⟨P₀, hP₀P₁, hP₀, -⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := q) P₁ (bot_lt_iff_ne_bot.mpr hq0)`. Use `haveI := hP₀`.

Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q`. Rewrite `h2` using `[hQ]`. Establish `h4 : (1 : ℕ∞) ≤ P₁.height` using `le_trans le_add_self h1`. Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (by gcongr) h2`.

Conclude with `absurd h3 (by decide)`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Use `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)` as an intermediate fact. Simplify using `using this`.
-/
theorem height_comap_eq_one_of_flat :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [CommRing R] (φ : A →+* R), φ.Flat →
      ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ ≠ ⊥ → (Q.comap φ).height = 1 := by
  intro A R _ _ _ φ hφ Q _ hQ hne
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  set p : Ideal A := Q.comap φ with hp
  haveI : p.IsPrime := Ideal.comap_isPrime φ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro q hq hqp
    by_contra hcon
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hq
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := q) (q := p) Q hqp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := q) P₁
      (bot_lt_iff_ne_bot.mpr hq0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

end GlobalTheory
