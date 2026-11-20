import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Introduce `p _ B _ π h`. Establish `hp : p.Prime` using `Fact.out`. Take `⟨⟨F, hF⟩, hred, -, -, -⟩` from `pf_facts p B h`. Establish `hpow : ∀ (N : ℕ) (x : B), π ^ N * x = 0 → π * x = 0`. Introduce `N x e`.

Apply `hred _ (N + 1)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hfrob : ∀ x : B, π * x ^ p = 0 → π * x = 0`. Introduce `x e`. Apply `hred _ p` to reduce the goal to its premises.

Establish `h1 : p = (p - 1) + 1` using `by have := hp.one_lt; omega`. Rewrite using `[mul_pow]`. Use `conv_lhs => rw [h1, pow_succ π]`. Rewrite using `[← h1, mul_assoc, e, mul_zero]`. Set `I : Ideal B` to `{ carrier := {x | π * x = 0} add_mem' := fun {a b} ha hb => by`.

Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[mul_add, ha, hb, add_zero]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun c x hx => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢`.

Rewrite using `[mul_left_comm, hx, mul_zero] }`. Establish `hI : ∀ x, Ideal.Quotient.mk I x = 0 ↔ π * x = 0` using `fun x => Ideal.Quotient.eq_zero_iff_mem`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mk I)` using `Ideal.Quotient.mk_surjective`. Use `⟨B ⧸ I, inferInstance, Ideal.Quotient.mk I, hsurj, ⟨?_, ?_, ?_⟩, ?_, hI, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_natCast (Ideal.Quotient.mk I), h.char, map_zero]`.

Introduce `a b e`. Take `⟨x, rfl⟩` from `hsurj a`. Take `⟨y, rfl⟩` from `hsurj b`. Simplify using `only at e`. Rewrite `e` using `[← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, hI]`.

Rewrite using `[← sub_eq_zero, ← map_sub, hI]`. Apply `hfrob` to reduce the goal to its premises. Establish `: (x - y) ^ p = x ^ p - y ^ p`. Rewrite using `[← hF, map_sub, hF, hF]`. Rewrite using `[this, e]`.

Introduce `a`. Take `⟨x, rfl⟩` from `hsurj a`. Take `⟨y, rfl⟩` from `h.bij.2 x`. Conclude with `⟨Ideal.Quotient.mk I y, by simp only [map_pow]⟩`. Rewrite using `[mem_nonZeroDivisors_iff_right]`.

Introduce `a e`. Take `⟨x, rfl⟩` from `hsurj a`. Rewrite `e` using `[← map_mul, hI]`. Rewrite using `[hI]`. Apply `hpow 2` to reduce the goal to its premises.

Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hA P hP hdeg`. Establish `hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I)` using `(Polynomial.map_surjective _ hsurj P).imp (fun Q hQ => by simpa using hQ) |> fun ⟨Q, hQ⟩ => (Polynomial.mem_lifts _).2 ⟨Q, hQ⟩`. Take `⟨Q, rfl, hQd, hQm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hP`.

Take `⟨x, hx⟩` from `hA Q hQm (hQd ▸ hdeg)`. Conclude with `⟨Ideal.Quotient.mk I x, hx.map⟩`. Introduce `hV f₁ g₁ ⟨N, hN⟩`. Take `⟨f, rfl⟩` from `hsurj f₁`. Take `⟨g, rfl⟩` from `hsurj g₁`.

Take `⟨a₁, b₁, hab⟩` from `Ideal.mem_span_pair.1 hN`. Take `⟨a, rfl⟩` from `hsurj a₁`. Take `⟨b, rfl⟩` from `hsurj b₁`. Establish `ht : π * (a * f + b * g - π ^ N) = 0`. Rewrite using `[← hI, map_sub, map_add, map_mul, map_mul, map_pow, hab, sub_self]`.

Establish `hmem : π ^ (N + 1) ∈ Ideal.span {f, g}`. Use `Ideal.mem_span_pair.2 ⟨π * a, π * b, ?_⟩` and prove the remaining obligations. Take the linear combination `ht`. Take `⟨e, he, h1, h2⟩` from `hV f g ⟨N + 1, hmem⟩`. Use `⟨Ideal.Quotient.mk I e, he.map _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `h1`, the goal using `[Ideal.mem_span_singleton]`. Rewrite using `[← map_mul]`. Conclude with `map_dvd _ h1`. Rewrite `h2`, the goal using `[Ideal.mem_span_singleton]`. Establish `: (1 - Ideal.Quotient.mk I e) * Ideal.Quotient.mk I g = Ideal.Quotient.mk I ((1 - e) * g)`.

Rewrite using `[map_mul, map_sub, map_one]`. Rewrite using `[this]`. Conclude with `map_dvd _ h2`.
-/
theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B →
    ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧
      q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧
      (VAL π → VAL (q π)) := by
  intro p _ B _ π h
  have hp : p.Prime := Fact.out
  obtain ⟨⟨F, hF⟩, hred, -, -, -⟩ := pf_facts p B h

  have hpow : ∀ (N : ℕ) (x : B), π ^ N * x = 0 → π * x = 0 := by
    intro N x e
    apply hred _ (N + 1)
    calc (π * x) ^ (N + 1) = π * x ^ N * (π ^ N * x) := by ring
      _ = 0 := by rw [e, mul_zero]

  have hfrob : ∀ x : B, π * x ^ p = 0 → π * x = 0 := by
    intro x e
    apply hred _ p
    have h1 : p = (p - 1) + 1 := by have := hp.one_lt; omega
    rw [mul_pow]
    conv_lhs => rw [h1, pow_succ π]
    rw [← h1, mul_assoc, e, mul_zero]
  let I : Ideal B :=
    { carrier := {x | π * x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_left_comm, hx, mul_zero] }
  have hI : ∀ x, Ideal.Quotient.mk I x = 0 ↔ π * x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  refine ⟨B ⧸ I, inferInstance, Ideal.Quotient.mk I, hsurj, ⟨?_, ?_, ?_⟩, ?_, hI, ?_, ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk I), h.char, map_zero]
  · intro a b e
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    simp only at e
    rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, hI] at e
    rw [← sub_eq_zero, ← map_sub, hI]
    apply hfrob
    have : (x - y) ^ p = x ^ p - y ^ p := by
      rw [← hF, map_sub, hF, hF]
    rw [this, e]
  · intro a
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := h.bij.2 x
    exact ⟨Ideal.Quotient.mk I y, by simp only [map_pow]⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro a e
    obtain ⟨x, rfl⟩ := hsurj a
    rw [← map_mul, hI] at e
    rw [hI]
    apply hpow 2
    rw [← e]
    ring
  · intro hA P hP hdeg
    have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.map_surjective _ hsurj P).imp (fun Q hQ => by simpa using hQ) |> fun ⟨Q, hQ⟩ =>
        (Polynomial.mem_lifts _).2 ⟨Q, hQ⟩
    obtain ⟨Q, rfl, hQd, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨x, hx⟩ := hA Q hQm (hQd ▸ hdeg)
    exact ⟨Ideal.Quotient.mk I x, hx.map⟩
  · intro hV f₁ g₁ ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := hsurj f₁
    obtain ⟨g, rfl⟩ := hsurj g₁
    obtain ⟨a₁, b₁, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := hsurj a₁
    obtain ⟨b, rfl⟩ := hsurj b₁
    have ht : π * (a * f + b * g - π ^ N) = 0 := by
      rw [← hI, map_sub, map_add, map_mul, map_mul, map_pow, hab, sub_self]
    have hmem : π ^ (N + 1) ∈ Ideal.span {f, g} := by
      refine Ideal.mem_span_pair.2 ⟨π * a, π * b, ?_⟩
      linear_combination ht
    obtain ⟨e, he, h1, h2⟩ := hV f g ⟨N + 1, hmem⟩
    refine ⟨Ideal.Quotient.mk I e, he.map _, ?_, ?_⟩
    · rw [Ideal.mem_span_singleton] at h1 ⊢
      rw [← map_mul]
      exact map_dvd _ h1
    · rw [Ideal.mem_span_singleton] at h2 ⊢
      have : (1 - Ideal.Quotient.mk I e) * Ideal.Quotient.mk I g
          = Ideal.Quotient.mk I ((1 - e) * g) := by
        rw [map_mul, map_sub, map_one]
      rw [this]
      exact map_dvd _ h2

end GlobalTheory.CompanionTheory.PerfectRing
