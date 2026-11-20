import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `K L _ _ cK cL r R T ι ψ τ h hinj z`. Set `A` to `MvPolynomial (Fin r) R`. Set `φ : A →+* T` to `MvPolynomial.eval₂Hom ι τ`. Set `φL : A →+* L` to `T.subtype.comp φ`. Establish `hφL : Function.Injective φL` using `Subtype.val_injective.comp hinj`.

Use `letI : Algebra A T := φ.toAlgebra`. Use `letI : Algebra A L := φL.toAlgebra`. Use `haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.FormallyEtale A T := h.etale`. Use `haveI : IsFractionRing T L := IsFractionRing.of_field T L fun f => by`.

Take `⟨a, ha, b, hb, hb0, e⟩` from `h.top.frac f`. Use `⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f = a / b`. Rewrite using `[← e, mul_div_cancel_right₀ _ hb0]`. Use `haveI : Algebra.FormallyUnramified T L := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors T)`.

Use `haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A T L`. Set `c0 : ℂ →+* R` to `cK.codRestrict R h.base.const_mem`. Set `cT : ℂ →+* T` to `cL.codRestrict T h.top.const_mem`. Use `letI : Algebra ℂ R := c0.toAlgebra`. Use `letI : Algebra ℂ T := cT.toAlgebra`.

Use `letI : Algebra ℂ L := cL.toAlgebra`. Use `haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun a => by`. Express the relevant statement in the definitionally equal form `cL a = T.subtype (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C (c0 a)))`. Rewrite using `[MvPolynomial.eval₂Hom_C]`.

Conclude with `(h.const a).symm`. Use `haveI : Algebra.EssFiniteType ℂ T := RingHom.essFiniteType_algebraMap.1 h.top.essFiniteType`. Use `haveI : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors T)`. Use `haveI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ T L`. Use `haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp ℂ A L`.

Set `F` to `FractionRing A`. Use `letI : Algebra F L := (IsFractionRing.lift hφL : F →+* L).toAlgebra`. Use `haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap hφL a).symm`. Use `haveI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_restrictScalars A F L`. Use `haveI : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L`.

Use `haveI : Algebra.IsSeparable F L := Algebra.FormallyUnramified.isSeparable F L`. Establish `hA : IsAlgebraic A z` using `(IsFractionRing.isAlgebraic_iff A F L).2 (Algebra.IsAlgebraic.isAlgebraic z)`. Take `⟨p, hp, hpz⟩` from `hA`. Use `⟨p.map φL.rangeRestrict, (Polynomial.map_ne_zero_iff (RingHom.injective_codRestrict.2 hφL)).2 hp, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`.

Conclude with `hpz`.
-/
theorem isAlgebraic_range_eval₂Hom_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  intro K L _ _ cK cL r R T ι ψ τ h hinj z
  classical
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  let φL : A →+* L := T.subtype.comp φ
  have hφL : Function.Injective φL := Subtype.val_injective.comp hinj

  letI : Algebra A T := φ.toAlgebra
  letI : Algebra A L := φL.toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale A T := h.etale

  haveI : IsFractionRing T L := IsFractionRing.of_field T L fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.top.frac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI : Algebra.FormallyUnramified T L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A T L

  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun a => by
    change cL a = T.subtype (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C (c0 a)))
    rw [MvPolynomial.eval₂Hom_C]
    exact (h.const a).symm
  haveI : Algebra.EssFiniteType ℂ T := RingHom.essFiniteType_algebraMap.1 h.top.essFiniteType
  haveI : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ T L
  haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp ℂ A L

  let F := FractionRing A
  letI : Algebra F L := (IsFractionRing.lift hφL : F →+* L).toAlgebra
  haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap hφL a).symm
  haveI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_restrictScalars A F L
  haveI : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  haveI : Algebra.IsSeparable F L := Algebra.FormallyUnramified.isSeparable F L
  have hA : IsAlgebraic A z :=
    (IsFractionRing.isAlgebraic_iff A F L).2 (Algebra.IsAlgebraic.isAlgebraic z)

  obtain ⟨p, hp, hpz⟩ := hA
  refine ⟨p.map φL.rangeRestrict, (Polynomial.map_ne_zero_iff
    (RingHom.injective_codRestrict.2 hφL)).2 hp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact hpz

end GlobalTheory.FieldPair
