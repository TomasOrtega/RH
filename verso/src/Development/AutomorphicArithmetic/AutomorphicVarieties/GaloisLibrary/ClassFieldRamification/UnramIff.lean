import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.CF.unramIff :
    (∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ), p.Prime → (UnramAt L p ↔ ∀ w : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ w.asIdeal → w.asIdeal.inertia Gal(L/ℚ) = ⊥)) ∧ (∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L)) ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime → UnramAt L p → UnramAt K p := by
  have h2 : ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
      (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L) := by
    intro L _ _ p hp
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hpZ]
    unfold UnramAt
    refine forall_congr' fun P => forall_congr' fun hP => ?_
    haveI := hP
    rw [Int.cast_natCast, Ideal.ramificationIdx_eq_one_iff]
  refine ⟨?_, h2, ?_⟩
  · intro L _ _ _ p hp
    unfold UnramAt
    constructor
    · intro h w hw
      haveI := w.isPrime
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
      exact h w.asIdeal w.isPrime hw
    · intro h P hP hpP
      haveI := hP
      have hne : P ≠ ⊥ := by
        intro hb
        rw [hb, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hw := h ⟨P, hP, hne⟩ hpP
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (P.under ℤ) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P Gal(L/ℚ)] at hw
      exact hw
  · intro K L _ _ _ _ _ p hp hL
    exact (h2 K p hp).2 fun hd => (h2 L p hp).1 hL (hd.trans (NumberField.discr_dvd_discr K L))
