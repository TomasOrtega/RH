import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Establish `hg : z ^ (l ^ a).gcd n = 1` using `pow_gcd_eq_one.2 ⟨ha, hz⟩`. Take `⟨k, -, hk'⟩` from `(Nat.dvd_prime_pow hl).1 (Nat.gcd_dvd_left (l ^ a) n)`. Establish `hkn : l ^ k ∣ n`.

Rewrite using `[← hk']`. Conclude with `Nat.gcd_dvd_right _ _`. Use `haveI := Fact.mk hl`. Establish `hkv : k ≤ padicValNat l n` using `(padicValNat_dvd_iff_le hn).1 hkn`. Take `⟨c, hc⟩` from `pow_dvd_pow l hkv`.

Rewrite using `[hc, pow_mul, ← hk', hg, one_pow]`. Introduce `h`. Conclude with `⟨_, h⟩`.
-/
theorem lpow_order_iff {G : Type*} [Monoid G] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (z : G)
    (hz : z ^ n = 1) : (∃ a : ℕ, z ^ (l ^ a) = 1) ↔ z ^ (l ^ padicValNat l n) = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    have hg : z ^ (l ^ a).gcd n = 1 := pow_gcd_eq_one.2 ⟨ha, hz⟩
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow hl).1 (Nat.gcd_dvd_left (l ^ a) n)
    have hkn : l ^ k ∣ n := by
      rw [← hk']
      exact Nat.gcd_dvd_right _ _
    haveI := Fact.mk hl
    have hkv : k ≤ padicValNat l n := (padicValNat_dvd_iff_le hn).1 hkn
    obtain ⟨c, hc⟩ := pow_dvd_pow l hkv
    rw [hc, pow_mul, ← hk', hg, one_pow]
  · intro h
    exact ⟨_, h⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
