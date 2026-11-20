import Mathlib

open scoped nonZeroDivisors

namespace GlobalTheory

namespace IndexNormEmb

/- English proof (translation)
Rewrite using `[Algebra.norm_apply]`. Set `bs` to `Module.Free.chooseBasis ℤ B`. Use `Submodule.natAbs_det_equiv ((Ideal.span {b}).restrictScalars ℤ) (bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _))` as an intermediate fact. Rewrite using `[show Nat.card (B ⧸ Ideal.span {b}) = Nat.card (B ⧸ (Ideal.span {b}).restrictScalars ℤ) from rfl, ← this]`. Reduce the equality to equality of the corresponding arguments.

Use `bs.ext fun i => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `show ((bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _) (bs i) : Ideal.span {b}) : B) = b * bs i`. Rewrite using `[Module.Basis.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]`.
-/
theorem card_quot_span_eq (B : Type) [CommRing B] [IsDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (b : B) (hb : b ≠ 0) : Nat.card (B ⧸ Ideal.span {b}) = (Algebra.norm ℤ b).natAbs := by
  classical
  rw [Algebra.norm_apply]
  let bs := Module.Free.chooseBasis ℤ B
  have := Submodule.natAbs_det_equiv ((Ideal.span {b}).restrictScalars ℤ)
    (bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _))
  rw [show Nat.card (B ⧸ Ideal.span {b}) = Nat.card (B ⧸ (Ideal.span {b}).restrictScalars ℤ) from rfl,
    ← this]
  congr
  refine bs.ext fun i => ?_
  simp
  show ((bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _) (bs i) : Ideal.span {b}) : B) = b * bs i
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h : (RingHom.ker τ).comap (algebraMap ℤ B) = ⊥`. Use extensionality with `n`. Simplify using `[RingHom.mem_ker, Ideal.mem_comap]`.

Use `Ideal.eq_bot_of_comap_eq_bot h` as an intermediate fact. Establish `hx' : x ∈ RingHom.ker τ` using `hx`. Rewrite `hx'` using `[this]`. Simplify using `using hx'`.
-/
theorem injective_of_ringHom (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (τ : B →+* ℂ) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : (RingHom.ker τ).comap (algebraMap ℤ B) = ⊥ := by
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have := Ideal.eq_bot_of_comap_eq_bot h
  have hx' : x ∈ RingHom.ker τ := hx
  rw [this] at hx'
  simpa using hx'

noncomputable def embEquiv (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] :
    (FractionRing B →ₐ[ℚ] ℂ) ≃ (B →+* ℂ) where
  toFun σ := (σ : FractionRing B →+* ℂ).comp (algebraMap B (FractionRing B))
  invFun τ := (IsFractionRing.lift (K := FractionRing B) (injective_of_ringHom B τ)).toRatAlgHom
  left_inv σ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext B⁰
    ext x
    simp
  right_inv τ := by
    ext x
    simp

/- English proof (translation)
Introduce `B _ _ _ _ b hb`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid B ℤ⁰) (FractionRing B) := Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors ℤ B (FractionRing B)`. Use `haveI : IsScalarTower ℤ ℚ (FractionRing B) := ⟨fun n q x => by rw [zsmul_eq_mul, zsmul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_mul, map_intCast, mul_assoc]⟩`. Use `haveI : @IsScalarTower ℤ ℚ (FractionRing B) Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)`. Use `haveI : FiniteDimensional ℚ (FractionRing B) := Module.Finite.of_isLocalization ℤ B ℤ⁰`.

Establish `hcard` using `card_quot_span_eq B b hb`. Establish `hN0 : Algebra.norm ℤ b ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hb`. Use `⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.mpr hN0), ?_⟩` and prove the remaining obligations. Establish `hN : algebraMap ℤ ℂ (Algebra.norm ℤ b) = ∏ σ : FractionRing B →ₐ[ℚ] ℂ, σ (algebraMap B (FractionRing B) b)`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ ℚ ℂ, ← Algebra.norm_localization ℤ (Sₘ := FractionRing B) ℤ⁰, Algebra.norm_eq_prod_embeddings]`.

Establish `hx : algebraMap B (FractionRing B) b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hb`. Rewrite using `[← finsum_comp_equiv (embEquiv B), finsum_eq_sum_of_fintype]`. Express the relevant statement in the definitionally equal form `_ = ∑ σ : FractionRing B →ₐ[ℚ] ℂ, Real.log ‖σ (algebraMap B (FractionRing B) b)‖`. Rewrite using `[← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hx)), ← norm_prod, ← hN, hcard, Nat.cast_natAbs, eq_intCast, Complex.norm_intCast, Int.cast_abs]`.
-/
theorem log_card_quot_span_eq_finsum_log_norm : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B),
    b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧
      Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  intro B _ _ _ _ b hb
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B ℤ⁰) (FractionRing B) :=
    Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors ℤ B (FractionRing B)
  haveI : IsScalarTower ℤ ℚ (FractionRing B) :=
    ⟨fun n q x => by rw [zsmul_eq_mul, zsmul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_mul, map_intCast, mul_assoc]⟩
  haveI : @IsScalarTower ℤ ℚ (FractionRing B) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FiniteDimensional ℚ (FractionRing B) := Module.Finite.of_isLocalization ℤ B ℤ⁰
  have hcard := card_quot_span_eq B b hb
  have hN0 : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.mpr hN0), ?_⟩
  have hN : algebraMap ℤ ℂ (Algebra.norm ℤ b) =
      ∏ σ : FractionRing B →ₐ[ℚ] ℂ, σ (algebraMap B (FractionRing B) b) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ ℂ,
      ← Algebra.norm_localization ℤ (Sₘ := FractionRing B) ℤ⁰, Algebra.norm_eq_prod_embeddings]
  have hx : algebraMap B (FractionRing B) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hb
  rw [← finsum_comp_equiv (embEquiv B), finsum_eq_sum_of_fintype]
  change _ = ∑ σ : FractionRing B →ₐ[ℚ] ℂ, Real.log ‖σ (algebraMap B (FractionRing B) b)‖
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hx)),
    ← norm_prod, ← hN, hcard, Nat.cast_natAbs, eq_intCast, Complex.norm_intCast, Int.cast_abs]

end IndexNormEmb

end GlobalTheory
