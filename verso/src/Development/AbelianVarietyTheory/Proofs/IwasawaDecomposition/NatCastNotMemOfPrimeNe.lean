import Mathlib

namespace GlobalTheory.NatCastNotMemPrime

/- English proof (translation)
Introduce `hlP`. Establish `hcop : Nat.Coprime l p` using `(Nat.coprime_primes hl hp).2 hne`. Establish `hc : IsCoprime (l : A) (p : A)` using `Nat.Coprime.cast hcop`. Take `⟨a, b, hab⟩` from `hc`. Apply `hP.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `P.add_mem (P.mul_mem_left a hlP) (P.mul_mem_left b hpP)`.
-/
theorem natCast_notMem_of_prime_ne {A : Type} [inst : CommRing A] (P : Ideal A)
    [hP : Ideal.IsPrime P] {p l : ℕ} (hp : Nat.Prime p) (hl : Nat.Prime l) (hne : l ≠ p)
    (hpP : (↑p : A) ∈ P) : (↑l : A) ∉ P := by
  intro hlP
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 hne
  have hc : IsCoprime (l : A) (p : A) := Nat.Coprime.cast hcop
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact P.add_mem (P.mul_mem_left a hlP) (P.mul_mem_left b hpP)

end GlobalTheory.NatCastNotMemPrime
