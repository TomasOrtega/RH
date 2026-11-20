import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `K O B Bh _ _ _ _ _ _ _ _ _ f h`. Use `haveI : IsAdicComplete (maximalIdeal (FractionRing (PowerSeries K))) (FractionRing (PowerSeries K)) := by`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`. Use `infer_instance`. Set `φ : B →+* FractionRing (PowerSeries K)` to `(algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (f : B →+* PowerSeries K)`.

Establish `hcomap : Ideal.comap φ (maximalIdeal (FractionRing (PowerSeries K))) = RingHom.ker f`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]`. Use extensionality with `b`. Simplify using `only [RingHom.mem_ker, φ, RingHom.comp_apply, RingHom.coe_coe]`. Conclude with `map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))`.

Take `⟨ψ, hψ, -⟩` from `IsCplAt.existsUnique_lift B (RingHom.ker f) Bh h (FractionRing (PowerSeries K)) φ hcomap`. Use `⟨ψ, fun b => RingHom.congr_fun hψ b, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hm`. Establish `hu : IsUnit x`.

Rewrite `hm` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Conclude with `hm`. Conclude with `(hu.map ψ).ne_zero (RingHom.mem_ker.mp hx)`. Establish `hm` using `IsCplAt.map_pow_eq B (RingHom.ker f) Bh h 1`. Rewrite `hm` using `[pow_one, pow_one]`.

Rewrite using `[← hm]`. Use `Ideal.map_le_iff_le_comap.mpr fun a ha => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hψ]`. Simplify using `only [φ, RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[RingHom.mem_ker.mp ha, map_zero]`.
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
