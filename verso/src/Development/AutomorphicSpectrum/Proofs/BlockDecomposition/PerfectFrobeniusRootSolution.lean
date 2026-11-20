import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Introduce `p _ A _ B _ _ m n k a c hB hS`. Take `⟨y, hy⟩` from `hS`. Take `⟨-, -, hroot, hinj, -⟩` from `pf_facts p B hB`. Take `⟨F, hF⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char k`. Use `choose y' hy' using fun j => hroot k (y j)`.

Use `⟨y', fun i => hinj k _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[← hF, ← hF, map_sum, hF, ← map_pow, ← hy i]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hF, Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow, hy' j]`.
-/
theorem solv_of_solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  intro p _ A _ B _ _ m n k a c hB hS
  obtain ⟨y, hy⟩ := hS
  obtain ⟨-, -, hroot, hinj, -⟩ := pf_facts p B hB
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char k
  choose y' hy' using fun j => hroot k (y j)
  refine ⟨y', fun i => hinj k _ _ ?_⟩
  rw [← hF, ← hF, map_sum, hF, ← map_pow, ← hy i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hF, Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow, hy' j]

end GlobalTheory.CompanionTheory.PerfectRing
