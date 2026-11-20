import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `letI := (g.comp f).toAlgebra`. Establish `hC : Module.Finite P C` using `h`. Set `gl : B →ₗ[P] C` to `{ toFun := g map_add' := g.map_add map_smul' := fun r b => by`. Simplify using `only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.comp_apply, RingHom.id_apply] }`.

Use `haveI : IsNoetherian P C := isNoetherian_of_isNoetherianRing_of_finite P C`. Use `haveI : IsNoetherian P B := isNoetherian_of_injective gl hg`. Conclude with `Module.IsNoetherian.finite P B`.
-/
private theorem UpperTheory.finite_of_finite_comp_injective_noetherian {P B C : Type*} [CommRing P] [CommRing B] [CommRing C]
    [IsNoetherianRing P] (f : P →+* B) (g : B →+* C) (hg : Function.Injective g)
    (h : (g.comp f).Finite) : f.Finite := by
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  have hC : Module.Finite P C := h
  let gl : B →ₗ[P] C :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.comp_apply,
          RingHom.id_apply] }
  haveI : IsNoetherian P C := isNoetherian_of_isNoetherianRing_of_finite P C
  haveI : IsNoetherian P B := isNoetherian_of_injective gl hg
  exact Module.IsNoetherian.finite P B

/- English proof (translation)
Rewrite using `[RingHom.finite_iff_isIntegral_and_finiteType]`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Use `⟨Polynomial.X ^ (p ^ e) - Polynomial.C x, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_pos k p).ne')`.

Simplify using `[Polynomial.eval₂_sub, iterateFrobenius_def]`. Apply `RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)` to reduce the goal to its premises. Establish `hc : (iterateFrobenius (MvPolynomial ι k) p e).comp MvPolynomial.C = MvPolynomial.C.comp (iterateFrobenius k p e)`. Use extensionality with `a`. Simplify using `[iterateFrobenius_def, map_pow]`.

Rewrite using `[hc]`. Conclude with `(RingHom.finiteType_algebraMap.mpr inferInstance).comp (RingHom.FiniteType.of_surjective _ (bijective_iterateFrobenius k p e).2)`.
-/
private theorem UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect (k : Type*) [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
    (ι : Type*) [Finite ι] [ExpChar (MvPolynomial ι k) p] (e : ℕ) :
    (iterateFrobenius (MvPolynomial ι k) p e).Finite := by
  rw [RingHom.finite_iff_isIntegral_and_finiteType]
  constructor
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_pos k p).ne')
    · simp [Polynomial.eval₂_sub, iterateFrobenius_def]
  · apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
    have hc : (iterateFrobenius (MvPolynomial ι k) p e).comp MvPolynomial.C
        = MvPolynomial.C.comp (iterateFrobenius k p e) := by
      ext a
      simp [iterateFrobenius_def, map_pow]
    rw [hc]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (bijective_iterateFrobenius k p e).2)

/- English proof (translation)
Set `E` to `separableClosure L F`. Use `haveI : FiniteDimensional E F := FiniteDimensional.right L E F`. Use `haveI : IsPurelyInseparable E F := separableClosure.isPurelyInseparable L F`. Use `haveI : ExpChar E p := IntermediateField.expChar' E p`. Use `haveI : IsScalarTower P E F := IsScalarTower.of_algebraMap_eq (fun r => by`.

Rewrite using `[IsScalarTower.algebraMap_apply P L E r, ← IsScalarTower.algebraMap_apply L E F, IsScalarTower.algebraMap_apply P L F])`. Use `set e := IsPurelyInseparable.exponent E F`. Establish `hpow : ∀ x : F, x ^ p ^ e ∈ E` using `fun x => by`. Take `⟨y, hy⟩` from `IsPurelyInseparable.exponent_def' E p x`. Rewrite using `[← hy]`.

Conclude with `y.2`. Use `haveI : Module.Finite P (integralClosure P E) := IsIntegralClosure.finite P L E (integralClosure P E)`. Establish `hq : p ^ e ≠ 0` using `pow_ne_zero _ (expChar_pos F p).ne'`. Set `fr : integralClosure P F →+* integralClosure P E` to `{ toFun := fun b => ⟨⟨b.1 ^ p ^ e, hpow b.1⟩, by`. Rewrite using `[mem_integralClosure_iff, ← isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) (algebraMap E F).injective]`.

Conclude with `b.2.pow _⟩`. Use the proof step `map_one' := by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Use the proof step `map_mul' := fun a b => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_pow]`. Use the proof step `map_zero' := by`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[zero_pow hq]`. Use the proof step `map_add' := fun a b => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[add_pow_expChar_pow] }`. Establish `hinj : Function.Injective fr`. Introduce `a b h`. Establish `h' : a.1 ^ p ^ e = b.1 ^ p ^ e` using `congrArg (fun y : integralClosure P E => ((y.1 : E) : F)) h`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `(iterateFrobenius F p e).injective` to reduce the goal to its premises. Simplify `h'` using `[iterateFrobenius_def]`. Establish `hcomp : fr.comp (algebraMap P (integralClosure P F)) = (algebraMap P (integralClosure P E)).comp (iterateFrobenius P p e)`. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `r`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [fr, iterateFrobenius_def, map_pow, RingHom.coe_comp, Function.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]`. Establish `h1 : ((algebraMap P (integralClosure P F) r : integralClosure P F) : F) = algebraMap P F r` using `rfl`.

Establish `h2 : (((algebraMap P (integralClosure P E) r : integralClosure P E) : E) : F) = algebraMap P F r`. Rewrite using `[IsScalarTower.algebraMap_apply P E F]`. Both sides reduce to the same expression. Simplify using `only [SubmonoidClass.coe_pow, h1, h2]`. Establish `hf` using `UpperTheory.finite_of_finite_comp_injective_noetherian (algebraMap P (integralClosure P F)) fr hinj (by`.

Rewrite using `[hcomp]`. Conclude with `(RingHom.finite_algebraMap.mpr inferInstance).comp (hσ e))`. Conclude with `RingHom.finite_algebraMap.mp hf`.
-/
private theorem UpperTheory.module_finite_integralClosure_of_frobenius_finite (P L F : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [Field L] [Algebra P L] [IsFractionRing P L] [Field F] [Algebra P F]
    [Algebra L F] [IsScalarTower P L F] [FiniteDimensional L F] (p : ℕ) [ExpChar P p]
    [ExpChar F p] (hσ : ∀ e, (iterateFrobenius P p e).Finite) :
    Module.Finite P (integralClosure P F) := by
  let E := separableClosure L F
  haveI : FiniteDimensional E F := FiniteDimensional.right L E F
  haveI : IsPurelyInseparable E F := separableClosure.isPurelyInseparable L F
  haveI : ExpChar E p := IntermediateField.expChar' E p
  haveI : IsScalarTower P E F := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply P L E r, ← IsScalarTower.algebraMap_apply L E F,
      IsScalarTower.algebraMap_apply P L F])
  set e := IsPurelyInseparable.exponent E F
  have hpow : ∀ x : F, x ^ p ^ e ∈ E := fun x => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p x
    rw [← hy]
    exact y.2
  haveI : Module.Finite P (integralClosure P E) :=
    IsIntegralClosure.finite P L E (integralClosure P E)
  have hq : p ^ e ≠ 0 := pow_ne_zero _ (expChar_pos F p).ne'
  let fr : integralClosure P F →+* integralClosure P E :=
    { toFun := fun b => ⟨⟨b.1 ^ p ^ e, hpow b.1⟩, by
        rw [mem_integralClosure_iff,
          ← isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) (algebraMap E F).injective]
        exact b.2.pow _⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [mul_pow]
      map_zero' := by
        apply Subtype.ext; apply Subtype.ext; simp [zero_pow hq]
      map_add' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [add_pow_expChar_pow] }
  have hinj : Function.Injective fr := by
    intro a b h
    have h' : a.1 ^ p ^ e = b.1 ^ p ^ e :=
      congrArg (fun y : integralClosure P E => ((y.1 : E) : F)) h
    apply Subtype.ext
    apply (iterateFrobenius F p e).injective
    simpa [iterateFrobenius_def] using h'
  have hcomp : fr.comp (algebraMap P (integralClosure P F)) =
      (algebraMap P (integralClosure P E)).comp (iterateFrobenius P p e) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply Subtype.ext
    simp only [fr, iterateFrobenius_def, map_pow, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    have h1 : ((algebraMap P (integralClosure P F) r : integralClosure P F) : F) =
        algebraMap P F r := rfl
    have h2 : (((algebraMap P (integralClosure P E) r : integralClosure P E) : E) : F) =
        algebraMap P F r := by
      rw [IsScalarTower.algebraMap_apply P E F]
      rfl
    simp only [SubmonoidClass.coe_pow, h1, h2]
  have hf := UpperTheory.finite_of_finite_comp_injective_noetherian (algebraMap P (integralClosure P F)) fr hinj (by
    rw [hcomp]
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp (hσ e))
  exact RingHom.finite_algebraMap.mp hf

/- English proof (translation)
Introduce `k A K F`. Use `intros`. Take `⟨s, g, hginj, hgfin⟩` from `exists_finite_inj_algHom_of_fg k A`. Take `⟨p, hp⟩` from `ExpChar.exists k`. Use `letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra`.

Use `haveI : Module.Finite (MvPolynomial (Fin s) k) A := hgfin`. Use `letI : Algebra (MvPolynomial (Fin s) k) F := ((algebraMap A F).comp g.toRingHom).toAlgebra`. Use `haveI : IsScalarTower (MvPolynomial (Fin s) k) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hAF : Function.Injective (algebraMap A F)`. Rewrite using `[IsScalarTower.algebraMap_eq A K F]`.

Conclude with `(algebraMap K F).injective.comp (IsFractionRing.injective A K)`. Use `haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hAF`. Use `haveI : FaithfulSMul (MvPolynomial (Fin s) k) A := (faithfulSMul_iff_algebraMap_injective _ A).mpr hginj`. Use `haveI : FaithfulSMul (MvPolynomial (Fin s) k) F := (faithfulSMul_iff_algebraMap_injective _ F).mpr (hAF.comp hginj)`. Use `letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) F := FractionRing.liftAlgebra _ F`.

Use `letI : Algebra (FractionRing A) F := FractionRing.liftAlgebra A F`. Use `letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) := FractionRing.liftAlgebra _ (FractionRing A)`. Use `haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) := inferInstance`. Use `haveI : FiniteDimensional (FractionRing A) F := by`. Use `Module.Finite.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv (RingEquiv.refl F) ?_` and prove the remaining obligations.

Apply `IsLocalization.ringHom_ext (nonZeroDivisors A)` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Use `haveI : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) F := by`.

Apply `IsScalarTower.of_algebraMap_eq'` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin s) k))` to reduce the goal to its premises. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) F, ← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A), IsScalarTower.algebraMap_apply _ A (FractionRing A), ← IsScalarTower.algebraMap_apply A (FractionRing A) F, …`.

Use `haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) F := Module.Finite.trans (FractionRing A) F`. Use `haveI : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p`. Use `haveI : ExpChar F p := expChar_of_injective_algebraMap hAF p`. Use `haveI : ExpChar (MvPolynomial (Fin s) k) p := expChar_of_injective_algebraMap (algebraMap k (MvPolynomial (Fin s) k)).injective p`. Establish `hP` using `UpperTheory.module_finite_integralClosure_of_frobenius_finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) F p (UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect k p (Fin s))`.

Use `haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.of_finite _ A`. Set `φ : integralClosure (MvPolynomial (Fin s) k) F →ₗ[MvPolynomial (Fin s) k] integralClosure A F` to `{ toFun := fun x => ⟨x.1, x.2.tower_top⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hφ : Function.Surjective φ` using `fun y => ⟨⟨y.1, isIntegral_trans (R := MvPolynomial (Fin s) k) y.1 y.2⟩, rfl⟩`. Use `haveI : Module.Finite (MvPolynomial (Fin s) k) (integralClosure A F) := Module.Finite.of_surjective φ hφ`. Conclude with `Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A (integralClosure A F)`.
-/
theorem UpperTheory.module_finite_integralClosure_finiteExt_perfect :
    ∀ (k A K F : Type) [Field k] [PerfectField k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
        [Field K] [Algebra A K] [IsFractionRing A K] [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
        [FiniteDimensional K F], Module.Finite A (integralClosure A F) := by
  intro k A K F
  intros
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  obtain ⟨p, hp⟩ := ExpChar.exists k
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
  letI : Algebra (MvPolynomial (Fin s) k) F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAF : Function.Injective (algebraMap A F) := by
    rw [IsScalarTower.algebraMap_eq A K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective A K)
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hAF
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hginj
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) F :=
    (faithfulSMul_iff_algebraMap_injective _ F).mpr (hAF.comp hginj)
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) F := FractionRing.liftAlgebra _ F
  letI : Algebra (FractionRing A) F := FractionRing.liftAlgebra A F
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    FractionRing.liftAlgebra _ (FractionRing A)
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    inferInstance
  haveI : FiniteDimensional (FractionRing A) F := by
    refine Module.Finite.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (RingEquiv.refl F) ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.toRingEquiv_eq_coe,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin s) k))
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) F,
      ← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A),
      IsScalarTower.algebraMap_apply _ A (FractionRing A),
      ← IsScalarTower.algebraMap_apply A (FractionRing A) F,
      ← IsScalarTower.algebraMap_apply _ A F]
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) F :=
    Module.Finite.trans (FractionRing A) F
  haveI : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p
  haveI : ExpChar F p := expChar_of_injective_algebraMap hAF p
  haveI : ExpChar (MvPolynomial (Fin s) k) p :=
    expChar_of_injective_algebraMap (algebraMap k (MvPolynomial (Fin s) k)).injective p
  have hP := UpperTheory.module_finite_integralClosure_of_frobenius_finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) F p
    (UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect k p (Fin s))
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.of_finite _ A
  let φ : integralClosure (MvPolynomial (Fin s) k) F →ₗ[MvPolynomial (Fin s) k]
      integralClosure A F :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := fun y =>
    ⟨⟨y.1, isIntegral_trans (R := MvPolynomial (Fin s) k) y.1 y.2⟩, rfl⟩
  haveI : Module.Finite (MvPolynomial (Fin s) k) (integralClosure A F) :=
    Module.Finite.of_surjective φ hφ
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A (integralClosure A F)
