import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `M _ L _ _ _ _`. Establish `hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta M ℚ L) M` using `IsCyclotomicExtension.zeta_spec M ℚ L`. Use `set ζ := IsCyclotomicExtension.zeta M ℚ L`. Establish `h1 : sg M L (-1) ζ = ζ⁻¹`. Rewrite using `[sg_apply M L _ hζ.pow_eq_one]`.

Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]`. Use `push_cast`. Simplify using the standard rewrite rules. Establish `h2 : cE L ζ = ζ⁻¹`.

Take `⟨φ⟩` from `(inferInstance : Nonempty (L →+* ℂ))`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Apply `φ.injective` to reduce the goal to its premises. Establish `hz : ‖φ ζ‖ = 1` using `(hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)`. Rewrite using `[map_mul, map_one, cE]`.

Simplify using `only [NumberField.IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]`. Rewrite using `[Complex.conj_mul', hz]`. Simplify using the standard rewrite rules. Establish `hc : sg M L (-1) = AlgEquiv.ofRingEquiv (f` using `cE L) (fun q => by simp) := by`. Apply `AlgEquiv.coe_algHom_injective` to reduce the goal to its premises.

Apply `(hζ.powerBasis ℚ).algHom_ext` to reduce the goal to its premises. Simplify using `only [IsPrimitiveRoot.powerBasis_gen, AlgEquiv.coe_algHom]`. Rewrite using `[h1]`. Conclude with `h2.symm`. Establish `key : (sg M L (-1)).toRingEquiv = cE L`.

Rewrite using `[hc]`. Use extensionality with `x`. Both sides reduce to the same expression. Use `⟨key, ?_⟩` and prove the remaining obligations. Rewrite using `[clA, ← map_inv, inv_neg_one, key]`.
-/
theorem UpperTheory.V.FW.conjEq :
    ∀ (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L], (sg M L (-1)).toRingEquiv = cE L ∧ clA M L (-1) = clMap (cE L) := by
  intro M _ L _ _ _ _
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta M ℚ L) M :=
    IsCyclotomicExtension.zeta_spec M ℚ L
  set ζ := IsCyclotomicExtension.zeta M ℚ L
  have h1 : sg M L (-1) ζ = ζ⁻¹ := by
    rw [sg_apply M L _ hζ.pow_eq_one]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast
    simp
  have h2 : cE L ζ = ζ⁻¹ := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    refine eq_inv_of_mul_eq_one_left ?_
    apply φ.injective
    have hz : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)
    rw [map_mul, map_one, cE]
    simp only [NumberField.IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [Complex.conj_mul', hz]
    simp
  have hc : sg M L (-1) = AlgEquiv.ofRingEquiv (f := cE L) (fun q => by simp) := by
    apply AlgEquiv.coe_algHom_injective
    apply (hζ.powerBasis ℚ).algHom_ext
    simp only [IsPrimitiveRoot.powerBasis_gen, AlgEquiv.coe_algHom]
    rw [h1]
    exact h2.symm
  have key : (sg M L (-1)).toRingEquiv = cE L := by
    rw [hc]
    ext x
    rfl
  refine ⟨key, ?_⟩
  rw [clA, ← map_inv, inv_neg_one, key]
