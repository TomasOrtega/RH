import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval s).toRingHom.toAlgebra`. Establish `hRA : algebraMap (MvPolynomial (Fin d) K) A = (MvPolynomial.aeval s).toRingHom` using `rfl`. Establish `: IsScalarTower K (MvPolynomial (Fin d) K) A` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[hRA, MvPolynomial.algebraMap_eq]`. Simplify using the standard rewrite rules.

Establish `hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) K) A)`. Introduce `a b h`. Conclude with `hs h`. Establish `: FaithfulSMul (MvPolynomial (Fin d) K) A` using `(faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) K) A).2 hinj`. Establish `: Algebra.FiniteType (MvPolynomial (Fin d) K) A` using `Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin d) K) A`.

Establish `: Algebra.FinitePresentation (MvPolynomial (Fin d) K) A` using `Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Establish `: Algebra.IsAlgebraic (MvPolynomial (Fin d) K) A`. Use `Algebra.IsAlgebraic.of_ringHom_of_comp_eq hs.aevalEquiv (RingHom.id A) hs.aevalEquiv.surjective Function.injective_id ?_` and prove the remaining obligations. Use extensionality with `p`. Simplify using `[hRA]`.

Simplify using `[hRA]`. Establish `hL : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A))`. Simplify `Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)` using `[Ideal.primeCompl_bot]`. Use `letI : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A`. Establish `: FaithfulSMul (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))`.

Rewrite using `[faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) K) A (Localization.AtPrime ⊥)]`. Conclude with `(IsFractionRing.injective A _).comp hinj`. Use `letI := FractionRing.liftAlgebra (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))`. Establish `: Algebra.IsAlgebraic A (Localization.AtPrime (⊥ : Ideal A))` using `IsLocalization.isAlgebraic _ (nonZeroDivisors A)`. Establish `: Algebra.IsAlgebraic (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))` using `Algebra.IsAlgebraic.trans (MvPolynomial (Fin d) K) A _`.

Establish `: Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A))` using `Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (MvPolynomial (Fin d) K) _)`. Establish `: CharZero (FractionRing (MvPolynomial (Fin d) K))` using `charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) K) _)`. Establish `: Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A))` using `Algebra.FormallyEtale.of_isSeparable _ _`. Establish `: Algebra.FormallyEtale (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))` using `Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial (Fin d) K))`. Establish `hE : Algebra.IsEtaleAt (MvPolynomial (Fin d) K) (⊥ : Ideal A)` using `Algebra.FormallyEtale.comp (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) _`.

Take `⟨g, hg, he⟩` from `Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial (Fin d) K) (⊥ : Ideal A)`. Use `⟨g, by simpa using hg, ?_⟩` and prove the remaining obligations. Establish `heq : (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g)) (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g) = algebraMap (MvPolynomial (Fin d) K) (Localization.Away g)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Rewrite using `[IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]`. Simplify using `[hRA, IsScalarTower.algebraMap_apply K A (Localization.Away g)]`. Introduce `i`. Rewrite using `[IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]`. Simplify using `[hRA]`.

Rewrite using `[heq]`. Conclude with `RingHom.etale_algebraMap.2 he`.
-/
theorem exists_etale_away_pf {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale := by
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval s).toRingHom.toAlgebra
  have hRA : algebraMap (MvPolynomial (Fin d) K) A = (MvPolynomial.aeval s).toRingHom := rfl
  have : IsScalarTower K (MvPolynomial (Fin d) K) A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hRA, MvPolynomial.algebraMap_eq]
    simp
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) K) A) := by
    intro a b h
    exact hs h
  have : FaithfulSMul (MvPolynomial (Fin d) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) K) A).2 hinj
  have : Algebra.FiniteType (MvPolynomial (Fin d) K) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin d) K) A
  have : Algebra.FinitePresentation (MvPolynomial (Fin d) K) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) A := by
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq hs.aevalEquiv (RingHom.id A)
      hs.aevalEquiv.surjective Function.injective_id ?_
    ext p
    · simp [hRA]
    · simp [hRA]
  have hL : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A
  have : FaithfulSMul (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) K) A (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective A _).comp hinj
  letI := FractionRing.liftAlgebra (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))
  have : Algebra.IsAlgebraic A (Localization.AtPrime (⊥ : Ideal A)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.trans (MvPolynomial (Fin d) K) A _
  have : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : CharZero (FractionRing (MvPolynomial (Fin d) K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyEtale (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial (Fin d) K))
  have hE : Algebra.IsEtaleAt (MvPolynomial (Fin d) K) (⊥ : Ideal A) :=
    Algebra.FormallyEtale.comp (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) _
  obtain ⟨g, hg, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial (Fin d) K) (⊥ : Ideal A)
  refine ⟨g, by simpa using hg, ?_⟩
  have heq : (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g) =
      algebraMap (MvPolynomial (Fin d) K) (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA, IsScalarTower.algebraMap_apply K A (Localization.Away g)]
    · intro i
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA]
  rw [heq]
  exact RingHom.etale_algebraMap.2 he

end CrystallineSemistableComparison.Pb
