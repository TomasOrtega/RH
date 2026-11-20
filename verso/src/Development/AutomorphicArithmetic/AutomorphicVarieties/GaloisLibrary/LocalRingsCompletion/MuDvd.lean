import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.abelian₂.mu_dvd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧,
      (∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f) ∧ (mu f = 0 ↔ map (residue O) f ≠ 0) ∧
        (mu f = 0 → lam f = (map (residue O) f).order.toNat) ∧
        ∀ m : ℕ, mu (C ϖ ^ m * f) = m + mu f ∧ lam (C ϖ ^ m * f) = lam f := by
  intro O _ _ _ ϖ hϖ f
  have hpow : ∀ m : ℕ, addVal O (ϖ ^ m) = m := by
    intro m
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  have hdvd : ∀ m : ℕ, C ϖ ^ m ∣ f ↔ ∀ n, ϖ ^ m ∣ coeff n f := by
    intro m
    constructor
    · rintro ⟨g, rfl⟩ n
      rw [← map_pow, PowerSeries.coeff_C_mul]
      exact dvd_mul_right _ _
    · intro h
      choose g hg using h
      refine ⟨PowerSeries.mk g, ?_⟩
      ext n
      rw [← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n]
  have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f := by
    intro m
    rw [hdvd, mu, le_iInf_iff]
    refine forall_congr' fun n => ?_
    rw [← hpow m, IsDiscreteValuationRing.addVal_le_iff_dvd]
  have hmu0 : mu f = 0 → map (residue O) f ≠ 0 := by
    intro h hzero
    have hc := addVal_coeff_lam f
    rw [h, IsDiscreteValuationRing.addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit] at hc
    apply hc
    rw [← PowerSeries.coeff_map, hzero, map_zero]
  refine ⟨h1, ⟨hmu0, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, coeff n (map (residue O) f) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (PowerSeries.ext fun n => by simpa using hall n)
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
      ← IsDiscreteValuationRing.addVal_eq_zero_iff] at hn
    have hle := mu_le f n
    rw [hn] at hle
    exact le_antisymm hle bot_le
  · intro h
    have hord : (map (residue O) f).order = (lam f : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      constructor
      · rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
          ← IsDiscreteValuationRing.addVal_eq_zero_iff, addVal_coeff_lam, h]
      · intro i hi
        rw [PowerSeries.coeff_map]
        by_contra hne
        have hu : IsUnit (coeff i f) := (residue_ne_zero_iff_isUnit _).1 hne
        rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
        have hli : lam f ≤ i := Nat.sInf_le (by
          show addVal O (coeff i f) = mu f
          rw [hu, h])
        omega
    rw [hord, ENat.toNat_coe]
  · intro m
    have hcoeff : ∀ n, addVal O (coeff n (C ϖ ^ m * f)) = m + addVal O (coeff n f) := by
      intro n
      rw [← map_pow, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, hpow]
    have hmu : mu (C ϖ ^ m * f) = m + mu f := by
      rw [mu, mu, ENat.add_iInf]
      exact iInf_congr hcoeff
    refine ⟨hmu, ?_⟩
    rw [lam, lam]
    congr 1
    ext n
    simp only [Set.mem_setOf_eq, hcoeff, hmu]
    exact ⟨fun h => WithTop.add_left_cancel (ENat.coe_ne_top m) h, fun h => by rw [h]⟩
