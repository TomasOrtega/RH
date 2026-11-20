import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.cocycle_card_euler_formula :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), ContAction ρ → Finite (H1 ρ) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * Nat.card (H0 ρ) = Nat.card (H1 ρ) * Nat.card M := by
  intro R Γ M _ _ _ _ _ _ _ _ ρ hρ hH1
  have hB1Z1 : B1 ρ ≤ Z1 ρ := by
    intro f hf
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hf
    rw [mem_Z1_iff_cocycle]
    have hfun : (d0 ρ m) = fun g => ρ g m - m := funext fun g => amitsur_d0_apply ρ m g
    refine ⟨?_, fun g h => ?_⟩
    · rw [hfun]
      exact (hρ.comp (Continuous.prodMk continuous_id continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · intro h
      funext g
      rw [amitsur_d0_apply, h g, sub_self, Pi.zero_apply]
  have hq : Nat.card (M ⧸ LinearMap.ker (d0 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv
  have hM := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ))
  rw [hq, hker] at hM
  have hB : Nat.card (Submodule.comap (Z1 ρ).subtype (B1 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hB1Z1).toEquiv
  have hZ := Submodule.card_eq_card_quotient_mul_card (Submodule.comap (Z1 ρ).subtype (B1 ρ))
  rw [hB] at hZ
  have hMpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hB1pos : Nat.card (B1 ρ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hM
    exact hMpos hM
  have hH1pos : Nat.card (H1 ρ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero hB1pos hH1pos
  · rw [hZ, hM]
    change Nat.card (B1 ρ) * Nat.card (H1 ρ) * Nat.card (H0 ρ) =
      Nat.card (H1 ρ) * (Nat.card (H0 ρ) * Nat.card (B1 ρ))
    ring
