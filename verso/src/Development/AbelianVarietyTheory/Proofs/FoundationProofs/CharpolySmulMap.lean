import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm

noncomputable section

open Polynomial

namespace GlobalTheory.TwAtt

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem normV_eq (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1
  · rintro ⟨c, rfl⟩
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Prove the second alternative. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Prove the first alternative.
-/
theorem normV_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (normV v).Prime := by
  have h1 : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_normV {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : ((normV v : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := by
    intro x hx
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x := ⟨Rat.ringOfIntegersEquiv x, by
      apply Rat.ringOfIntegersEquiv.injective; simp⟩
    have key : ∀ I : Ideal (𝓞 ℚ), (m : 𝓞 ℚ) ∈ I ↔ ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ I := fun I => by
      rcases Int.natAbs_eq m with e | e
      · conv_lhs => rw [e]
        rw [Int.cast_natCast]
      · conv_lhs => rw [e]
        rw [Int.cast_neg, Int.cast_natCast, neg_mem_iff]
    rw [key, mem_iff] at hx ⊢
    exact ((mem_iff _ _).1 h).trans hx
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem normV_injective : Function.Injective (normV : HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v v' h
  refine (eq_of_normV (v := v') (v' := v) ?_)
  rw [← h]
  exact (mem_iff v _).2 dvd_rfl

end GlobalTheory.TwAtt

end
