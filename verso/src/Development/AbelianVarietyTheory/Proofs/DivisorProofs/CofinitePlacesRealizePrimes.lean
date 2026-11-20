import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

/- English proof (translation)
Introduce `p _ P hP`. Establish `hfin : {w : AwayP p | ¬ P w}.Finite` using `hP`. Use `⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩` and prove the remaining obligations. Introduce `ℓ hℓ hS`. Establish `hℓp : ℓ ≠ p` using `fun h => hS (by simp [h])`.

Set `q : Nat.Primes` to `⟨ℓ, hℓ.out⟩`. Set `v : HeightOneSpectrum ℤ` to `(primesEquiv (R := ℤ)).symm q`. Establish `hv : ((primesEquiv (R` using `ℤ) v : Nat.Primes) : ℕ) = ℓ := by show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ`. Rewrite using `[Equiv.apply_symm_apply]`. Establish `hne : v.asIdeal ≠ Ideal.span {(p : ℤ)}`.

Introduce `h`. Establish `h1` using `span_natGenerator (R := ℤ) v`. Establish `h2 : natGenerator v = ℓ` using `hv`. Rewrite `h1` using `[h, h2, Ideal.map_span]`. Simplify using `only [Set.image_singleton, map_natCast] at h1`.

Establish `h3 : (ℓ : ℤ) ∣ (p : ℤ)` using `Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)`. Establish `h4 : (p : ℤ) ∣ (ℓ : ℤ)` using `Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)`. Conclude with `hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))`. Use `⟨⟨v, hne⟩, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hw`.

Apply `hS` to reduce the goal to its premises. Use `Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)` and prove the remaining obligations. Conclude with `⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩`.
-/
theorem exists_finset_forall_prime_awayP_padic :
    ∀ (p : ℕ) [Fact p.Prime] (P : AwayP p → Prop), (∀ᶠ w in Filter.cofinite, P w) →
    ∃ S : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ w : AwayP p, P w ∧ Nonempty (w.1.adicCompletion ℚ ≃+* ℚ_[ℓ]) := by
  intro p _ P hP
  have hfin : {w : AwayP p | ¬ P w}.Finite := hP
  refine ⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩
  intro ℓ hℓ hS
  have hℓp : ℓ ≠ p := fun h => hS (by simp [h])
  let q : Nat.Primes := ⟨ℓ, hℓ.out⟩
  let v : HeightOneSpectrum ℤ := (primesEquiv (R := ℤ)).symm q
  have hv : ((primesEquiv (R := ℤ) v : Nat.Primes) : ℕ) = ℓ := by
    show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ
    rw [Equiv.apply_symm_apply]
  have hne : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := span_natGenerator (R := ℤ) v
    have h2 : natGenerator v = ℓ := hv
    rw [h, h2, Ideal.map_span] at h1
    simp only [Set.image_singleton, map_natCast] at h1
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (p : ℤ) ∣ (ℓ : ℤ) := Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)
    exact hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))
  refine ⟨⟨v, hne⟩, ?_, ?_⟩
  · by_contra hw
    apply hS
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)
  · exact ⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩

end GlobalTheory.FinClsLoc
