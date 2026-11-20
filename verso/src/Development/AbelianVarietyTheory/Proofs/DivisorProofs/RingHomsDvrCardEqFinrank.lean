import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _`. Use `letI : Algebra ℤ_[p] O := (padicToO p O).toAlgebra`. Use `letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra`. Use `haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hZC : Function.Injective (algebraMap ℤ_[p] C)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Rewrite `hx` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`. Establish `hu : algebraMap ℤ_[p] C (PadicInt.unitCoeff h0 : ℤ_[p]) ≠ 0` using `((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero`.

Establish `hp : (p : C) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero`. Conclude with `(mul_ne_zero hu (pow_ne_zero _ hp)) hx`. Use `haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZC`. Establish `hZE : Function.Injective (algebraMap ℤ_[p] (FractionRing Λ))`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[p] Λ (FractionRing Λ)]`.

Conclude with `(IsFractionRing.injective Λ (FractionRing Λ)).comp (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)`. Use `haveI : FaithfulSMul ℤ_[p] (FractionRing Λ) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZE`. Use `letI : Algebra (FractionRing ℤ_[p]) (FractionRing Λ) := FractionRing.liftAlgebra ℤ_[p] (FractionRing Λ)`. Use `haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) (FractionRing Λ) := FractionRing.isScalarTower_liftAlgebra ℤ_[p] (FractionRing Λ)`. Use `letI : Algebra (FractionRing ℤ_[p]) C := FractionRing.liftAlgebra ℤ_[p] C`.

Use `haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) C := FractionRing.isScalarTower_liftAlgebra ℤ_[p] C`. Establish `hrank : Module.finrank (FractionRing ℤ_[p]) (FractionRing Λ) = Module.finrank ℤ_[p] Λ` using `IsFractionRing.finrank_eq ℤ_[p] (FractionRing ℤ_[p]) Λ (FractionRing Λ)`. Use `haveI : Module.IsTorsionFree ℤ_[p] Λ := NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)`. Establish `hpos : 0 < Module.finrank ℤ_[p] Λ` using `Module.finrank_pos`. Use `haveI : FiniteDimensional (FractionRing ℤ_[p]) (FractionRing Λ) := Module.finite_of_finrank_pos (hrank ▸ hpos)`.

Use `haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing Λ) := inferInstance`. Establish `hcard` using `AlgHom.card (FractionRing ℤ_[p]) (FractionRing Λ) C`. Use `haveI : Algebra.IsIntegral ℤ_[p] Λ := Algebra.IsIntegral.of_finite ℤ_[p] Λ`. Set `Φ : (Λ →+* O) → (Λ →+* C)` to `fun σ => (algebraMap O C).comp σ`. Establish `hΦ : Function.Injective Φ` using `fun σ τ h => RingHom.ext fun x => hv.hom_inj (RingHom.congr_fun h x)`.

Set `Ψ : (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) → (Λ →+* C)` to `fun φ => (φ : FractionRing Λ →+* C).comp (algebraMap Λ (FractionRing Λ))`. Establish `hΨ : Function.Injective Ψ` using `fun φ ψ h => AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Λ) h)`. Establish `hrange : Set.range Φ = Set.range Ψ`. Use extensionality with `τ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨σ, rfl⟩`. Establish `hcomm : ∀ c : ℤ_[p], Φ σ (algebraMap ℤ_[p] Λ c) = algebraMap ℤ_[p] C c`. Introduce `c`. Establish `hu` using `GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))`. Use `RingHom.congr_fun hu c` as an intermediate fact.

Simplify using `only [RingHom.comp_apply] at this`. Express the relevant statement in the definitionally equal form `algebraMap O C (σ (algebraMap ℤ_[p] Λ c)) = algebraMap O C (padicToO p O c)`. Rewrite using `[this]`. Set `τa : Λ →ₐ[ℤ_[p]] C` to `{ Φ σ with commutes' := hcomm }`. Establish `hinj : Function.Injective τa`.

Rewrite using `[injective_iff_map_eq_zero]`. Establish `hk : RingHom.ker (τa : Λ →+* C) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `c hc`.

Rewrite `hc` using `[Ideal.mem_comap, RingHom.mem_ker]`. Establish `: algebraMap ℤ_[p] C c = 0` using `by rw [← hc]; exact (τa.commutes c).symm`. Rewrite using `[Ideal.mem_bot]`. Conclude with `hZC (by rw [this, map_zero])`. Introduce `x hx`.

Establish `: x ∈ RingHom.ker (τa : Λ →+* C)` using `hx`. Rewrite `this` using `[hk, Ideal.mem_bot]`. Then use the resulting hypothesis. Set `φ0 : FractionRing Λ →ₐ[ℤ_[p]] C` to `IsFractionRing.liftAlgHom (K := FractionRing Λ) hinj`. Use `⟨φ0.extendScalarsOfIsLocalization (FractionRing ℤ_[p]) (nonZeroDivisors ℤ_[p]), ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `φ0 (algebraMap Λ (FractionRing Λ) x) = τa x`. Rewrite using `[IsFractionRing.liftAlgHom_apply]`. Conclude with `IsFractionRing.lift_algebraMap hinj x`. Introduce and unpack `⟨φ, rfl⟩`. Set `τa : Λ →ₐ[ℤ_[p]] C` to `(φ.restrictScalars ℤ_[p]).comp (IsScalarTower.toAlgHom ℤ_[p] Λ (FractionRing Λ))`.

Establish `hmem : ∀ x : Λ, ∃ y : O, algebraMap O C y = τa x`. Introduce `x`. Establish `h1 : IsIntegral ℤ_[p] (τa x)` using `(Algebra.IsIntegral.isIntegral x).map τa`. Establish `h2 : IsIntegral O (τa x)` using `h1.tower_top`. Conclude with `hv.exists_of_le_one (hv.mem_of_integral h2)`.

Set `e : O ≃+* (algebraMap O C).range` to `RingEquiv.ofBijective (algebraMap O C).rangeRestrict ⟨fun a b h => hv.hom_inj (congrArg Subtype.val h), (algebraMap O C).rangeRestrict_surjective⟩`. Set `σ : Λ →+* O` to `e.symm.toRingHom.comp ((τa : Λ →+* C).codRestrict (algebraMap O C).range (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩))`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Use `congrArg Subtype.val (e.apply_symm_apply ((τa : Λ →+* C).codRestrict (algebraMap O C).range (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩) x))` as an intermediate fact.

Conclude with `this`. Set `eqv : (Λ →+* O) ≃ (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C)` to `(Equiv.ofInjective Φ hΦ).trans ((Equiv.setCongr hrange).trans (Equiv.ofInjective Ψ hΨ).symm)`. Use `⟨Finite.of_equiv _ eqv.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr eqv, Nat.card_eq_fintype_card, hcard, hrank]`.
-/
theorem card_ringHom_to_integers_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    Finite (Λ →+* O) ∧ Nat.card (Λ →+* O) = Module.finrank ℤ_[p] Λ := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _
  letI : Algebra ℤ_[p] O := (padicToO p O).toAlgebra
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hZC : Function.Injective (algebraMap ℤ_[p] C) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    have hu : algebraMap ℤ_[p] C (PadicInt.unitCoeff h0 : ℤ_[p]) ≠ 0 :=
      ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero
    have hp : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact (mul_ne_zero hu (pow_ne_zero _ hp)) hx
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZC
  have hZE : Function.Injective (algebraMap ℤ_[p] (FractionRing Λ)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] Λ (FractionRing Λ)]
    exact (IsFractionRing.injective Λ (FractionRing Λ)).comp (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : FaithfulSMul ℤ_[p] (FractionRing Λ) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZE
  letI : Algebra (FractionRing ℤ_[p]) (FractionRing Λ) := FractionRing.liftAlgebra ℤ_[p] (FractionRing Λ)
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) (FractionRing Λ) :=
    FractionRing.isScalarTower_liftAlgebra ℤ_[p] (FractionRing Λ)
  letI : Algebra (FractionRing ℤ_[p]) C := FractionRing.liftAlgebra ℤ_[p] C
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) C := FractionRing.isScalarTower_liftAlgebra ℤ_[p] C
  have hrank : Module.finrank (FractionRing ℤ_[p]) (FractionRing Λ) = Module.finrank ℤ_[p] Λ :=
    IsFractionRing.finrank_eq ℤ_[p] (FractionRing ℤ_[p]) Λ (FractionRing Λ)
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  have hpos : 0 < Module.finrank ℤ_[p] Λ := Module.finrank_pos
  haveI : FiniteDimensional (FractionRing ℤ_[p]) (FractionRing Λ) :=
    Module.finite_of_finrank_pos (hrank ▸ hpos)
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing Λ) := inferInstance
  have hcard := AlgHom.card (FractionRing ℤ_[p]) (FractionRing Λ) C

  haveI : Algebra.IsIntegral ℤ_[p] Λ := Algebra.IsIntegral.of_finite ℤ_[p] Λ
  let Φ : (Λ →+* O) → (Λ →+* C) := fun σ => (algebraMap O C).comp σ
  have hΦ : Function.Injective Φ := fun σ τ h =>
    RingHom.ext fun x => hv.hom_inj (RingHom.congr_fun h x)
  let Ψ : (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) → (Λ →+* C) :=
    fun φ => (φ : FractionRing Λ →+* C).comp (algebraMap Λ (FractionRing Λ))
  have hΨ : Function.Injective Ψ := fun φ ψ h =>
    AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Λ) h)
  have hrange : Set.range Φ = Set.range Ψ := by
    ext τ
    constructor
    · rintro ⟨σ, rfl⟩
      have hcomm : ∀ c : ℤ_[p], Φ σ (algebraMap ℤ_[p] Λ c) = algebraMap ℤ_[p] C c := by
        intro c
        have hu := GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))
        have := RingHom.congr_fun hu c
        simp only [RingHom.comp_apply] at this
        change algebraMap O C (σ (algebraMap ℤ_[p] Λ c)) = algebraMap O C (padicToO p O c)
        rw [this]
      let τa : Λ →ₐ[ℤ_[p]] C := { Φ σ with commutes' := hcomm }
      have hinj : Function.Injective τa := by
        rw [injective_iff_map_eq_zero]
        have hk : RingHom.ker (τa : Λ →+* C) = ⊥ := by
          apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
          rw [eq_bot_iff]
          intro c hc
          rw [Ideal.mem_comap, RingHom.mem_ker] at hc
          have : algebraMap ℤ_[p] C c = 0 := by rw [← hc]; exact (τa.commutes c).symm
          rw [Ideal.mem_bot]
          exact hZC (by rw [this, map_zero])
        intro x hx
        have : x ∈ RingHom.ker (τa : Λ →+* C) := hx
        rwa [hk, Ideal.mem_bot] at this
      let φ0 : FractionRing Λ →ₐ[ℤ_[p]] C := IsFractionRing.liftAlgHom (K := FractionRing Λ) hinj
      refine ⟨φ0.extendScalarsOfIsLocalization (FractionRing ℤ_[p]) (nonZeroDivisors ℤ_[p]), ?_⟩
      ext x
      change φ0 (algebraMap Λ (FractionRing Λ) x) = τa x
      rw [IsFractionRing.liftAlgHom_apply]
      exact IsFractionRing.lift_algebraMap hinj x
    · rintro ⟨φ, rfl⟩
      let τa : Λ →ₐ[ℤ_[p]] C :=
        (φ.restrictScalars ℤ_[p]).comp (IsScalarTower.toAlgHom ℤ_[p] Λ (FractionRing Λ))
      have hmem : ∀ x : Λ, ∃ y : O, algebraMap O C y = τa x := by
        intro x
        have h1 : IsIntegral ℤ_[p] (τa x) := (Algebra.IsIntegral.isIntegral x).map τa
        have h2 : IsIntegral O (τa x) := h1.tower_top
        exact hv.exists_of_le_one (hv.mem_of_integral h2)
      let e : O ≃+* (algebraMap O C).range :=
        RingEquiv.ofBijective (algebraMap O C).rangeRestrict
          ⟨fun a b h => hv.hom_inj (congrArg Subtype.val h), (algebraMap O C).rangeRestrict_surjective⟩
      let σ : Λ →+* O := e.symm.toRingHom.comp ((τa : Λ →+* C).codRestrict (algebraMap O C).range
        (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩))
      refine ⟨σ, ?_⟩
      ext x
      have := congrArg Subtype.val (e.apply_symm_apply
        ((τa : Λ →+* C).codRestrict (algebraMap O C).range
          (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩) x))
      exact this
  let eqv : (Λ →+* O) ≃ (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) :=
    (Equiv.ofInjective Φ hΦ).trans ((Equiv.setCongr hrange).trans (Equiv.ofInjective Ψ hΨ).symm)
  refine ⟨Finite.of_equiv _ eqv.symm, ?_⟩
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, hcard, hrank]

end GlobalTheory
