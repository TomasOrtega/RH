import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Derivation.ToSquareZero

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `O R _ _ _ _ _ _ hinj halg`. Use `haveI : FaithfulSMul O (ResidueField R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Use `letI : Algebra (FractionRing O) (ResidueField R) := FractionRing.liftAlgebra O _`. Use `haveI := FractionRing.isScalarTower_liftAlgebra O (ResidueField R)`. Use `haveI := halg`.

Use `haveI : Algebra.IsAlgebraic (FractionRing O) (ResidueField R) := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective O (FractionRing O))`. Use `haveI : Algebra.FormallyEtale (FractionRing O) (ResidueField R) := Algebra.FormallyEtale.of_isSeparable _ _`. Use `haveI : Algebra.FormallyEtale O (FractionRing O) := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)`. Use `haveI : Algebra.FormallyEtale O (ResidueField R) := Algebra.FormallyEtale.comp O (FractionRing O) _`. Establish `hle : maximalIdeal R ^ 2 ≤ maximalIdeal R` using `Ideal.pow_le_self two_ne_zero`.

Set `g : R ⧸ maximalIdeal R ^ 2 →ₐ[O] ResidueField R` to `Ideal.Quotient.factorₐ O hle`. Establish `hgmk : ∀ a : R, g (Ideal.Quotient.mk _ a) = residue R a` using `fun a => rfl`. Establish `hg : Function.Surjective g`. Introduce `x`. Take `⟨a, rfl⟩` from `residue_surjective x`.

Conclude with `⟨_, hgmk a⟩`. Establish `hker : ∀ x, g x = 0 → x ∈ (maximalIdeal R).cotangentIdeal`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[hgmk, residue_eq_zero_iff]`.

Conclude with `Ideal.mk_mem_cotangentIdeal.mpr hx`. Establish `hnil : IsNilpotent (RingHom.ker (g : R ⧸ maximalIdeal R ^ 2 →+* ResidueField R))`. Use `⟨2, le_bot_iff.mp ?_⟩` and prove the remaining obligations. Use `(Ideal.pow_right_mono (fun x hx => hker x hx) 2).trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.cotangentIdeal_square]`.

Set `s` to `Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O (ResidueField R)) g hg hnil`. Establish `hs : ∀ x, g (s x) = x` using `fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hg hnil x`. Set `φ` to `s.comp (IsScalarTower.toAlgHom O R (ResidueField R))`. Establish `e : (Ideal.Quotient.mkₐ O (maximalIdeal R).cotangentIdeal).comp φ = IsScalarTower.toAlgHom O R ((R ⧸ maximalIdeal R ^ 2) ⧸ (maximalIdeal R).cotangentIdeal)`. Use extensionality with `r`.

Use `show Ideal.Quotient.mk _ (s (algebraMap R (ResidueField R) r)) = Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal R ^ 2) r)`. Rewrite using `[Ideal.Quotient.eq]`. Apply `hker` to reduce the goal to its premises. Rewrite using `[map_sub, hs, hgmk, ResidueField.algebraMap_eq, sub_self]`. Set `D` to `derivationToSquareZeroOfLift (maximalIdeal R).cotangentIdeal (Ideal.cotangentIdeal_square _) φ e`.

Use `⟨-(((maximalIdeal R).cotangentEquivIdeal.symm : (maximalIdeal R).cotangentIdeal →ₗ[R] (maximalIdeal R).Cotangent).compDer D), fun a => ?_⟩` and prove the remaining obligations. Establish `hφ : φ a = 0` using `by show s (algebraMap R (ResidueField R) a) = 0`. Rewrite using `[ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.2, map_zero]`. Use `show -((maximalIdeal R).cotangentEquivIdeal.symm (D a)) = _`. Rewrite using `[neg_eq_iff_eq_neg, ← map_neg, LinearEquiv.symm_apply_eq]`.

Use `ext`. Simplify using `only [D, derivationToSquareZeroOfLift_apply, hφ, zero_sub, Ideal.cotangentEquivIdeal_apply, map_neg, Submodule.coe_neg, Ideal.toCotangent_to_quotient_square]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Ws.Eb.cotDer :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R] [Algebra O R], Function.Injective (algebraMap O (ResidueField R)) → Algebra.IsAlgebraic O (ResidueField R) →
        ∃ d : Derivation O R (CotangentSpace R), ∀ a : maximalIdeal R, d a = (maximalIdeal R).toCotangent a := by
  intro O R _ _ _ _ _ _ hinj halg
  haveI : FaithfulSMul O (ResidueField R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra (FractionRing O) (ResidueField R) := FractionRing.liftAlgebra O _
  haveI := FractionRing.isScalarTower_liftAlgebra O (ResidueField R)
  haveI := halg
  haveI : Algebra.IsAlgebraic (FractionRing O) (ResidueField R) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective O (FractionRing O))
  haveI : Algebra.FormallyEtale (FractionRing O) (ResidueField R) := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O (FractionRing O) := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O (ResidueField R) := Algebra.FormallyEtale.comp O (FractionRing O) _
  have hle : maximalIdeal R ^ 2 ≤ maximalIdeal R := Ideal.pow_le_self two_ne_zero
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[O] ResidueField R := Ideal.Quotient.factorₐ O hle
  have hgmk : ∀ a : R, g (Ideal.Quotient.mk _ a) = residue R a := fun a => rfl
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact ⟨_, hgmk a⟩
  have hker : ∀ x, g x = 0 → x ∈ (maximalIdeal R).cotangentIdeal := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hgmk, residue_eq_zero_iff] at hx
    exact Ideal.mk_mem_cotangentIdeal.mpr hx
  have hnil : IsNilpotent (RingHom.ker (g : R ⧸ maximalIdeal R ^ 2 →+* ResidueField R)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    refine (Ideal.pow_right_mono (fun x hx => hker x hx) 2).trans ?_
    rw [Ideal.cotangentIdeal_square]
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O (ResidueField R)) g hg hnil
  have hs : ∀ x, g (s x) = x := fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hg hnil x
  let φ := s.comp (IsScalarTower.toAlgHom O R (ResidueField R))
  have e : (Ideal.Quotient.mkₐ O (maximalIdeal R).cotangentIdeal).comp φ
      = IsScalarTower.toAlgHom O R ((R ⧸ maximalIdeal R ^ 2) ⧸ (maximalIdeal R).cotangentIdeal) := by
    ext r
    show Ideal.Quotient.mk _ (s (algebraMap R (ResidueField R) r))
      = Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal R ^ 2) r)
    rw [Ideal.Quotient.eq]
    apply hker
    rw [map_sub, hs, hgmk, ResidueField.algebraMap_eq, sub_self]
  let D := derivationToSquareZeroOfLift (maximalIdeal R).cotangentIdeal
    (Ideal.cotangentIdeal_square _) φ e
  refine ⟨-(((maximalIdeal R).cotangentEquivIdeal.symm :
      (maximalIdeal R).cotangentIdeal →ₗ[R] (maximalIdeal R).Cotangent).compDer D), fun a => ?_⟩
  have hφ : φ a = 0 := by
    show s (algebraMap R (ResidueField R) a) = 0
    rw [ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.2, map_zero]
  show -((maximalIdeal R).cotangentEquivIdeal.symm (D a)) = _
  rw [neg_eq_iff_eq_neg, ← map_neg, LinearEquiv.symm_apply_eq]
  ext
  simp only [D, derivationToSquareZeroOfLift_apply, hφ, zero_sub, Ideal.cotangentEquivIdeal_apply, map_neg,
    Submodule.coe_neg, Ideal.toCotangent_to_quotient_square]
  rfl
