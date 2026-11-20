import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ Ω _ _ hinj S hS`. Use `haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj`. Use `letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω`. Use `haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω`. Use `set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL`.

Use `haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by`. Apply `IntermediateField.finiteDimensional_adjoin` to reduce the goal to its premises. Introduce `x hx`. Conclude with `((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral`. Use `haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance`.

Use `haveI : IsDedekindDomain (integralClosure ℤ_[p] L) := integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L`. Use `haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) := IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)`. Establish `hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L)`. Apply `IsPrincipalIdealRing.of_finite_primes` to reduce the goal to its premises. Use `haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)`.

Apply `((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset` to reduce the goal to its premises. Introduce `I hI`. Distinguish the cases in `h : I = ⊥`. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩`.

Set `f : L →ₐ[ℤ_[p]] Ω` to `{ algebraMap L Ω with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `((algebraMap ℤ_[p] L r : L) : Ω) = _`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]`. Conclude with `(IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }`. Establish `hf : Function.Injective f` using `Subtype.val_injective`.

Set `e` to `Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf`. Use `⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv, IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Take `⟨c, hc0, hci⟩` from `(hS s hs).exists_integral_multiple`. Establish `hsL : s ∈ L` using `IntermediateField.subset_adjoin _ _ hs`.

Use `⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_map]`. Use `⟨c • ⟨s, hsL⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))`. Rewrite using `[← isIntegral_algHom_iff f hf]`.

Conclude with `hci`. Rewrite using `[Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]`.
-/
theorem exists_finite_pid_subalgebra_div_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  intro p _ Ω _ _ hinj S hS
  haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj
  letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω
  set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL
  haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance
  haveI : IsDedekindDomain (integralClosure ℤ_[p] L) :=
    integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)
  have hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L) := by
    apply IsPrincipalIdealRing.of_finite_primes
    haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)
    apply ((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset
    intro I hI
    by_cases h : I = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩
  let f : L →ₐ[ℤ_[p]] Ω :=
    { algebraMap L Ω with
      commutes' := fun r => by
        change ((algebraMap ℤ_[p] L r : L) : Ω) = _
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]
        exact (IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }
  have hf : Function.Injective f := Subtype.val_injective
  let e := Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf
  refine ⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv,
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩
  intro s hs
  obtain ⟨c, hc0, hci⟩ := (hS s hs).exists_integral_multiple
  have hsL : s ∈ L := IntermediateField.subset_adjoin _ _ hs
  refine ⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩
  · rw [Subalgebra.mem_map]
    refine ⟨c • ⟨s, hsL⟩, ?_, rfl⟩
    show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))
    rw [← isIntegral_algHom_iff f hf]
    exact hci
  · rw [Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]

end GlobalTheory
