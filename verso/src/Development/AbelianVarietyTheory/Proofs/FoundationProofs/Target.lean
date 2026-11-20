import Mathlib

namespace GlobalTheory.IntegralNormBound

/- English proof (translation)
Introduce `m u`. Proceed by induction on `m with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ m ih`. Take `⟨p, hp⟩` from `ih`.

Take `⟨y, hy, q, hq, hyq⟩` from `Submodule.mem_sup.mp (hfil m hp)`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Take `⟨a, ha⟩` from `hres c`. Use `⟨p + Polynomial.C a * Polynomial.X ^ m, ?_⟩` and prove the remaining obligations. Establish `hpm : π ^ m * (c - algebraMap k A a) ∈ Q ^ (m + 1)`.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ m) ha`. Establish `key : u - Polynomial.aeval π (p + Polynomial.C a * Polynomial.X ^ m) = q + π ^ m * (c - algebraMap k A a)`. Simplify using `only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]`. Take the linear combination `(-1 : A) * hyq`.

Rewrite using `[key]`. Conclude with `Ideal.add_mem _ hq hpm`.
-/
theorem main {k A : Type} [Field k] [CommRing A] [Algebra k A] {Q : Ideal A} {π : A}
    (hπ : π ∈ Q) (hres : ∀ c : A, ∃ a : k, c - algebraMap k A a ∈ Q)
    (hfil : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) :
    ∀ (m : ℕ) (u : A), ∃ p : Polynomial k, u - Polynomial.aeval π p ∈ Q ^ m := by
  intro m u
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨y, hy, q, hq, hyq⟩ := Submodule.mem_sup.mp (hfil m hp)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨a, ha⟩ := hres c
    refine ⟨p + Polynomial.C a * Polynomial.X ^ m, ?_⟩
    have hpm : π ^ m * (c - algebraMap k A a) ∈ Q ^ (m + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ m) ha
    have key : u - Polynomial.aeval π (p + Polynomial.C a * Polynomial.X ^ m)
        = q + π ^ m * (c - algebraMap k A a) := by
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      linear_combination (-1 : A) * hyq
    rw [key]
    exact Ideal.add_mem _ hq hpm

/- English proof (translation)
Introduce `hπ hres hfil` and use `main hπ hres hfil`.
-/
theorem target : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] {Q : Ideal A} {π : A}, π ∈ Q → (∀ (c : A), ∃ (a : k), c - (Algebra.algebraMap k A : k → A) a ∈ Q) → (∀ (m : ℕ), Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + (1 : ℕ))) → ∀ (m : ℕ) (u : A), ∃ (p : Polynomial k), u - (Polynomial.aeval π : Polynomial k → A) p ∈ Q ^ m :=
  fun hπ hres hfil => main hπ hres hfil

end GlobalTheory.IntegralNormBound
