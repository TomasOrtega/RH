import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. A detailed English derivation is pending.
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
