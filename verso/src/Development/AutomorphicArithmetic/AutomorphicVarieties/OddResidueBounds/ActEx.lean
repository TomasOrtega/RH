import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ N _ hf`. Take `⟨f⟩` from `hf`. Use `haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩`. Use `haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ`. Use `letI : Algebra E (CyclotomicField N ℚ) := f.toRingHom.toAlgebra`.

Use `haveI : IsScalarTower ℚ E (CyclotomicField N ℚ) := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm`. Use `haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)`. Use `haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E (CyclotomicField N ℚ)`. Use `haveI : Algebra.IsAlgebraic E (CyclotomicField N ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`.

Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Set `g : CyclotomicField N ℚ →ₐ[E] Ω` to `IsAlgClosed.lift`. Use `⟨(AlgEquiv.restrictNormalHom E).comp (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm.toMonoidHom, ?_⟩` and prove the remaining obligations. Introduce `b σ hσ x`. Use `set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm b with hτ`.

Establish `hζ` using `IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)`. Establish `key : ∀ y : CyclotomicField N ℚ, σ (g y) = g (τ y)`. Establish `hcomp : (σ.toRingHom.comp (g : CyclotomicField N ℚ →+* Ω)).toRatAlgHom = ((g : CyclotomicField N ℚ →+* Ω).comp (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ)).toRatAlgHom`. Apply `(hζ.powerBasis ℚ).algHom_ext` to reduce the goal to its premises. Simplify using `only [IsPrimitiveRoot.powerBasis_gen, RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgHom.coe_toRingHom]`.

Establish `h1 : (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) ^ N = 1`. Rewrite using `[← map_pow, hζ.pow_eq_one, map_one]`. Express the relevant statement in the definitionally equal form `σ (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) = g (τ (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)))`. Rewrite using `[hσ _ h1, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, map_pow, hτ, MulEquiv.apply_symm_apply]`. Introduce `y`.

Conclude with `congrArg (fun φ => φ y) hcomp`. Express the relevant statement in the definitionally equal form `σ (algebraMap E Ω x) = algebraMap E Ω ((AlgEquiv.restrictNormal τ E) x)`. Rewrite using `[← g.commutes x, ← g.commutes, AlgEquiv.restrictNormal_commutes, key]`.
-/
theorem UpperTheory.V.Odd.actEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E), IsCycAct Ω N ρ := by
  intro E Ω _ _ _ _ _ N _ hf
  obtain ⟨f⟩ := hf
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  letI : Algebra E (CyclotomicField N ℚ) := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ E (CyclotomicField N ℚ) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E (CyclotomicField N ℚ)
  haveI : Algebra.IsAlgebraic E (CyclotomicField N ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let g : CyclotomicField N ℚ →ₐ[E] Ω := IsAlgClosed.lift
  refine ⟨(AlgEquiv.restrictNormalHom E).comp
    (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm.toMonoidHom, ?_⟩
  intro b σ hσ x
  set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm b with hτ
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  have key : ∀ y : CyclotomicField N ℚ, σ (g y) = g (τ y) := by
    have hcomp : (σ.toRingHom.comp (g : CyclotomicField N ℚ →+* Ω)).toRatAlgHom =
        ((g : CyclotomicField N ℚ →+* Ω).comp (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ)).toRatAlgHom := by
      apply (hζ.powerBasis ℚ).algHom_ext
      simp only [IsPrimitiveRoot.powerBasis_gen, RingHom.toRatAlgHom_apply, RingHom.coe_comp,
        Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgHom.coe_toRingHom]
      have h1 : (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) ^ N = 1 := by
        rw [← map_pow, hζ.pow_eq_one, map_one]
      change σ (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) =
        g (τ (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)))
      rw [hσ _ h1, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, map_pow, hτ,
        MulEquiv.apply_symm_apply]
    intro y
    exact congrArg (fun φ => φ y) hcomp
  change σ (algebraMap E Ω x) = algebraMap E Ω ((AlgEquiv.restrictNormal τ E) x)
  rw [← g.commutes x, ← g.commutes, AlgEquiv.restrictNormal_commutes, key]
