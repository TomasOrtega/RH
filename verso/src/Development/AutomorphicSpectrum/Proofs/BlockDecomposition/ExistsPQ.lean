import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPerfectRadical
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfClos

/- English proof (translation)
Introduce `p hpf S _ I hp`. Take `⟨T, inst, i, hc, hb, hpow, hker⟩` from `exists_perfect_radical p S I hp`. Use `⟨T, inst, i, ⟨⟨hc, hb⟩, hpow, fun x => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hker x]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨n, hn⟩`. Use `⟨n, Ideal.pow_mem_of_pow_mem I hn ?_⟩` and prove the remaining obligations. Conclude with `(Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le`. Introduce and unpack `⟨k, hk⟩`. Conclude with `⟨p ^ k, hk⟩`.
-/
theorem exists_PQ : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 →
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := by
  intro p hpf S _ I hp
  obtain ⟨T, inst, i, hc, hb, hpow, hker⟩ := exists_perfect_radical p S I hp
  refine ⟨T, inst, i, ⟨⟨hc, hb⟩, hpow, fun x => ?_⟩⟩
  rw [hker x]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Ideal.pow_mem_of_pow_mem I hn ?_⟩
    exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  · rintro ⟨k, hk⟩
    exact ⟨p ^ k, hk⟩

end GlobalTheory.CompanionTheory.PerfClos
