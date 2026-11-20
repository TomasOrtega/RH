import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleBase

/- English proof (translation)
Introduce `A _ _ _ _ _ _ EA _ _ _ _ _ QA _ _ ρ _ _`. Use `set R := Localization.AtPrime QA`. Use `haveI : Algebra.Smooth A (Polynomial A) := Algebra.Smooth.mk`. Use `haveI : Algebra.Smooth A EA := Algebra.Smooth.comp A (Polynomial A) EA`. Use `haveI : Module.Flat EA R := IsLocalization.flat R QA.primeCompl`.

Use `haveI : Module.Flat A EA := Algebra.Smooth.flat A EA`. Use `haveI : Module.Flat (Polynomial A) EA := Algebra.Smooth.flat (Polynomial A) EA`. Establish `hflat : Module.Flat A R` using `Module.Flat.trans A EA R`. Use `⟨hflat, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA`.

Conclude with `IsLocalization.isNoetherianRing QA.primeCompl R inferInstance`. Use `haveI : Module.Flat (Polynomial A) R := Module.Flat.trans (Polynomial A) EA R`. Establish `hX : (Polynomial.X : Polynomial A) ∈ nonZeroDivisors (Polynomial A)` using `Polynomial.monic_X.mem_nonZeroDivisors`. Establish `hreg` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hX`. Establish `h1 : ∀ z : R, algebraMap (Polynomial A) R Polynomial.X * z = 0 → z = 0`.

Introduce `z hz`. Apply `hreg` to reduce the goal to its premises. Simplify using `only [Algebra.smul_def, smul_zero, mul_zero]`. Conclude with `hz`. Conclude with `⟨h1, fun z hz => h1 z (by rw [mul_comm]; exact hz)⟩`.

Introduce `f hf set K := FractionRing A`. Use `letI : Algebra K (R ⊗[A] K) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsScalarTower A K (R ⊗[A] K) := inferInstance`. Use `haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (R ⊗[A] K) := (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) K).2 inferInstance`. Set `e : GlobalTheory.LocAcyc.GenFib A R ≃ₐ[R] R ⊗[A] K` to `IsLocalization.algEquiv (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) _ _`.

Establish `H1 : Function.Bijective (TensorProduct.toIntegralClosure A EA K)` using `TensorProduct.toIntegralClosure_bijective_of_smooth`. Establish `H2 : Function.Bijective (TensorProduct.toIntegralClosure EA R (EA ⊗[A] K))` using `TensorProduct.toIntegralClosure_bijective_of_isLocalization QA.primeCompl`. Establish `H : Function.Bijective (TensorProduct.toIntegralClosure A R K)` using `TensorProduct.toIntegralClosure_bijective_of_tower H1 H2`. Establish `hf' : IsIntegral R (e f)` using `hf.map e.toAlgHom`. Take `⟨y, hy⟩` from `H.2 ⟨e f, hf'⟩`.

Establish `hy' : (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = e f` using `congrArg Subtype.val hy`. Establish `key : ∀ y : R ⊗[A] integralClosure A K, ∃ b : R, (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = b ⊗ₜ[A] (1 : K)`. Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul b c`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 c.2`. Use `⟨r • b, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]`. Both sides reduce to the same expression.

Consider the case `add u v hu hv`. Take `⟨a, ha⟩` from `hu`. Take `⟨b, hb⟩` from `hv`. Conclude with `⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩`. Take `⟨b, hb⟩` from `key y`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.commutes, ← hy', hb]`. Both sides reduce to the same expression.
-/
theorem flat_noetherian_nzd_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ _ ρ _ _
  set R := Localization.AtPrime QA
  haveI : Algebra.Smooth A (Polynomial A) := Algebra.Smooth.mk
  haveI : Algebra.Smooth A EA := Algebra.Smooth.comp A (Polynomial A) EA
  haveI : Module.Flat EA R := IsLocalization.flat R QA.primeCompl
  haveI : Module.Flat A EA := Algebra.Smooth.flat A EA
  haveI : Module.Flat (Polynomial A) EA := Algebra.Smooth.flat (Polynomial A) EA
  have hflat : Module.Flat A R := Module.Flat.trans A EA R
  refine ⟨hflat, ?_, ?_, ?_⟩
  · haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
    exact IsLocalization.isNoetherianRing QA.primeCompl R inferInstance
  · haveI : Module.Flat (Polynomial A) R := Module.Flat.trans (Polynomial A) EA R
    have hX : (Polynomial.X : Polynomial A) ∈ nonZeroDivisors (Polynomial A) :=
      Polynomial.monic_X.mem_nonZeroDivisors
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hX
    have h1 : ∀ z : R, algebraMap (Polynomial A) R Polynomial.X * z = 0 → z = 0 := by
      intro z hz
      apply hreg
      simp only [Algebra.smul_def, smul_zero, mul_zero]
      exact hz
    exact ⟨h1, fun z hz => h1 z (by rw [mul_comm]; exact hz)⟩
  · intro f hf
    set K := FractionRing A
    letI : Algebra K (R ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
    haveI : IsScalarTower A K (R ⊗[A] K) := inferInstance
    haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (R ⊗[A] K) :=
      (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) K).2 inferInstance
    let e : GlobalTheory.LocAcyc.GenFib A R ≃ₐ[R] R ⊗[A] K :=
      IsLocalization.algEquiv (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) _ _
    have H1 : Function.Bijective (TensorProduct.toIntegralClosure A EA K) :=
      TensorProduct.toIntegralClosure_bijective_of_smooth
    have H2 : Function.Bijective (TensorProduct.toIntegralClosure EA R (EA ⊗[A] K)) :=
      TensorProduct.toIntegralClosure_bijective_of_isLocalization QA.primeCompl
    have H : Function.Bijective (TensorProduct.toIntegralClosure A R K) :=
      TensorProduct.toIntegralClosure_bijective_of_tower H1 H2
    have hf' : IsIntegral R (e f) := hf.map e.toAlgHom
    obtain ⟨y, hy⟩ := H.2 ⟨e f, hf'⟩
    have hy' : (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = e f := congrArg Subtype.val hy
    have key : ∀ y : R ⊗[A] integralClosure A K, ∃ b : R,
        (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = b ⊗ₜ[A] (1 : K) := by
      intro y
      induction y with
      | zero => exact ⟨0, by simp⟩
      | tmul b c =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
        refine ⟨r • b, ?_⟩
        rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
        rfl
      | add u v hu hv =>
        obtain ⟨a, ha⟩ := hu
        obtain ⟨b, hb⟩ := hv
        exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
    obtain ⟨b, hb⟩ := key y
    refine ⟨b, ?_⟩
    apply e.injective
    rw [AlgEquiv.commutes, ← hy', hb]
    rfl

end GlobalTheory.GoodEtaleBase
