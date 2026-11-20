import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.StalkGenericPointSpecializesOfSpecializes

open Polynomial Matrix

open IsLocalRing in
/- English proof (translation)
Introduce `R _ _ _ _ _ _ p _ _ hdim`. Establish `hKle : Ring.KrullDimLE 1 R`. Rewrite using `[Ring.krullDimLE_iff, hdim]`. Both sides reduce to the same expression. Establish `hm : maximalIdeal R ≠ ⊥`.

Introduce `h`. Establish `h0` using `ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)`. Rewrite `h0` using `[hdim]`. Conclude with `one_ne_zero h0`. Take `⟨π, hπm, hπ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`.

Take `⟨ev, hev⟩` from `GlobalTheory.exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal R) hπm`. Set `f : PowerSeries (ZMod p) →+* R` to `ev.toRingHom.comp (PowerSeries.map (ZMod.castHom (dvd_refl p) R))`. Establish `hfX : f PowerSeries.X = π`. Simplify using `[f, hev]`. Establish `hunit : ∀ g : PowerSeries (ZMod p), PowerSeries.constantCoeff g ≠ 0 → IsUnit g`.

Introduce `g hg`. Conclude with `(PowerSeries.isUnit_iff_constantCoeff).mpr (isUnit_iff_ne_zero.mpr hg)`. Use `⟨f, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `g hg`.

Assume the negation of the conclusion as `hne`. Establish `hu` using `hunit _ (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)`. Establish `hfg` using `congrArg f (PowerSeries.X_pow_order_mul_divXPowOrder (f := g))`. Rewrite `hfg` using `[map_mul, map_pow, hfX, hg]`. Use `(hu.map f).ne_zero` as an intermediate fact.

Conclude with `(mul_ne_zero (pow_ne_zero _ hπ0) this) hfg`. Use `⟨fun g hg => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hng`. Establish `hc : PowerSeries.constantCoeff g = 0`. Assume the negation of the conclusion as `hc`.

Conclude with `hng (hunit g hc)`. Take `⟨h, rfl⟩` from `(PowerSeries.X_dvd_iff).mpr hc`. Rewrite `hg` using `[map_mul, hfX]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hπm) hg`. Use `letI : Algebra (PowerSeries (ZMod p)) R := f.toAlgebra`.

Establish `hmap : Ideal.map (algebraMap (PowerSeries (ZMod p)) R) (Ideal.span {PowerSeries.X}) = Ideal.span {π}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Conclude with `congrArg (fun x => Ideal.span {x}) hfX`. Establish `hrad : maximalIdeal R ≤ (Ideal.span {π}).radical`. Rewrite using `[Ideal.radical_eq_sInf]`.

Use `le_sInf fun P ⟨hJP, hP⟩ => ?_` and prove the remaining obligations. Establish `hPne : P ≠ ⊥`. Introduce `hP0`. Establish `hπP : π ∈ P` using `hJP (Ideal.subset_span rfl)`. Rewrite `hπP` using `[hP0]`.

Conclude with `hπ0 ((Submodule.mem_bot R).mp hπP)`. Conclude with `(IsLocalRing.eq_maximalIdeal (hP.isMaximal_of_ne_bot hPne)).ge`. Take `⟨n, hn⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian (maximalIdeal R))`. Establish `hres : Finite (R ⧸ maximalIdeal R)` using `‹Finite (IsLocalRing.ResidueField R)›`. Establish `hpow : Finite (R ⧸ maximalIdeal R ^ n)` using `Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n`.

Establish `hquot : Finite (R ⧸ Ideal.span {π})` using `Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)`. Establish `hH : IsHausdorff (Ideal.span {π}) R`. Use `⟨fun x hx => IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := maximalIdeal R)) x fun k => ?_⟩` and prove the remaining obligations. Use `SModEq.mono ?_ (hx k)` and prove the remaining obligations. Conclude with `Submodule.smul_mono_left (Ideal.pow_right_mono (Ideal.span_singleton_le_iff_mem _ |>.mpr hπm) k)`.

Use `haveI : IsHausdorff (Ideal.map (algebraMap (PowerSeries (ZMod p)) R) (Ideal.span {PowerSeries.X})) R := hmap ▸ hH`. Use `haveI : Module.Finite (PowerSeries (ZMod p)) (R ⧸ Ideal.map (algebraMap (PowerSeries (ZMod p)) R) (Ideal.span {PowerSeries.X})) := by`. Rewrite using `[hmap]`. Conclude with `Module.Finite.of_finite`. Conclude with `GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (Ideal.span {PowerSeries.X})`.
-/
theorem UpperTheory.V.Pr.T.curveOverSeries :
    ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
      (p : ℕ) [Fact p.Prime] [CharP R p], ringKrullDim R = 1 →
      ∃ f : PowerSeries (ZMod p) →+* R, Function.Injective f ∧ IsLocalHom f ∧ f.Finite := by
  intro R _ _ _ _ _ _ p _ _ hdim
  have hKle : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  have hm : maximalIdeal R ≠ ⊥ := by
    intro h
    have h0 := ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    rw [hdim] at h0
    exact one_ne_zero h0
  obtain ⟨π, hπm, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨ev, hev⟩ := GlobalTheory.exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal R) hπm
  let f : PowerSeries (ZMod p) →+* R :=
    ev.toRingHom.comp (PowerSeries.map (ZMod.castHom (dvd_refl p) R))
  have hfX : f PowerSeries.X = π := by
    simp [f, hev]
  have hunit : ∀ g : PowerSeries (ZMod p), PowerSeries.constantCoeff g ≠ 0 → IsUnit g := by
    intro g hg
    exact (PowerSeries.isUnit_iff_constantCoeff).mpr (isUnit_iff_ne_zero.mpr hg)
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro g hg
    by_contra hne
    have hu := hunit _ (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)
    have hfg := congrArg f (PowerSeries.X_pow_order_mul_divXPowOrder (f := g))
    rw [map_mul, map_pow, hfX, hg] at hfg
    have := (hu.map f).ne_zero
    exact (mul_ne_zero (pow_ne_zero _ hπ0) this) hfg
  · refine ⟨fun g hg => ?_⟩
    by_contra hng
    have hc : PowerSeries.constantCoeff g = 0 := by
      by_contra hc
      exact hng (hunit g hc)
    obtain ⟨h, rfl⟩ := (PowerSeries.X_dvd_iff).mpr hc
    rw [map_mul, hfX] at hg
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hπm) hg
  · letI : Algebra (PowerSeries (ZMod p)) R := f.toAlgebra
    have hmap : Ideal.map (algebraMap (PowerSeries (ZMod p)) R)
        (Ideal.span {PowerSeries.X}) = Ideal.span {π} := by
      rw [Ideal.map_span, Set.image_singleton]
      exact congrArg (fun x => Ideal.span {x}) hfX
    have hrad : maximalIdeal R ≤ (Ideal.span {π}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf fun P ⟨hJP, hP⟩ => ?_
      have hPne : P ≠ ⊥ := by
        intro hP0
        have hπP : π ∈ P := hJP (Ideal.subset_span rfl)
        rw [hP0] at hπP
        exact hπ0 ((Submodule.mem_bot R).mp hπP)
      exact (IsLocalRing.eq_maximalIdeal (hP.isMaximal_of_ne_bot hPne)).ge
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
      (IsNoetherian.noetherian (maximalIdeal R))
    have hres : Finite (R ⧸ maximalIdeal R) :=
      ‹Finite (IsLocalRing.ResidueField R)›
    have hpow : Finite (R ⧸ maximalIdeal R ^ n) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n
    have hquot : Finite (R ⧸ Ideal.span {π}) :=
      Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)
    have hH : IsHausdorff (Ideal.span {π}) R := by
      refine ⟨fun x hx => IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := maximalIdeal R)) x
        fun k => ?_⟩
      refine SModEq.mono ?_ (hx k)
      exact Submodule.smul_mono_left (Ideal.pow_right_mono (Ideal.span_singleton_le_iff_mem _ |>.mpr hπm) k)
    haveI : IsHausdorff (Ideal.map (algebraMap (PowerSeries (ZMod p)) R)
        (Ideal.span {PowerSeries.X})) R := hmap ▸ hH
    haveI : Module.Finite (PowerSeries (ZMod p)) (R ⧸ Ideal.map
        (algebraMap (PowerSeries (ZMod p)) R) (Ideal.span {PowerSeries.X})) := by
      rw [hmap]
      exact Module.Finite.of_finite
    exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (Ideal.span {PowerSeries.X})
