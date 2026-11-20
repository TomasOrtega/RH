import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.rfEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsLocalRing O] [Algebra O K] [CommRing B] [Algebra O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K), IsCplAt B (RingHom.ker f) Bh → ∃ rF : Bh →+* FractionRing (PowerSeries K), (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) ∧ RingHom.ker rF = maximalIdeal Bh := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ f h
  haveI : IsAdicComplete (maximalIdeal (FractionRing (PowerSeries K))) (FractionRing (PowerSeries K)) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let φ : B →+* FractionRing (PowerSeries K) :=
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (f : B →+* PowerSeries K)
  have hcomap : Ideal.comap φ (maximalIdeal (FractionRing (PowerSeries K))) = RingHom.ker f := by
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    ext b
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply, RingHom.coe_coe]
    exact map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift B (RingHom.ker f) Bh h (FractionRing (PowerSeries K)) φ hcomap
  refine ⟨ψ, fun b => RingHom.congr_fun hψ b, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hm
    have hu : IsUnit x := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
      exact hm
    exact (hu.map ψ).ne_zero (RingHom.mem_ker.mp hx)
  · have hm := IsCplAt.map_pow_eq B (RingHom.ker f) Bh h 1
    rw [pow_one, pow_one] at hm
    rw [← hm]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hψ]
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingHom.mem_ker.mp ha, map_zero]
