import Mathlib

namespace Bl.FirstLemmaD

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {F : Type} [inst : Field.{0} F] [NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F)),
  Exists.{1} fun (p : Nat) ↦
    And (Nat.Prime p) (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} v) (Nat.cast.{0} p)) := by
  intro F _ _ v
  have := v.isPrime
  have hne : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    fun h => v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
  have hpr : (v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F))).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨x, hx, hxp⟩ := hpr.exists_mem_prime_of_ne_bot hne
  refine ⟨x.natAbs, Int.prime_iff_natAbs_prime.mp hxp, ?_⟩
  obtain ⟨c, hc⟩ : x ∣ (x.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hmem : ((x.natAbs : ℤ)) ∈ v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
    rw [hc]
    exact Ideal.mul_mem_right c _ hx
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hmem

end Bl.FirstLemmaD
