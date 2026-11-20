import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcObjIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsEmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFiniteTypeIntFiniteIndexProdNormalDomainsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebrasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualConStep

def conductor (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] : Ideal R where
  carrier := {x | ∀ r : R', ∃ y : R, algebraMap R R' y = algebraMap R R' x * r}
  add_mem' {x x'} hx hx' r := by
    obtain ⟨y, hy⟩ := hx r
    obtain ⟨y', hy'⟩ := hx' r
    exact ⟨y + y', by rw [map_add, map_add, hy, hy', add_mul]⟩
  zero_mem' r := ⟨0, by simp⟩
  smul_mem' b {x} hx r := by
    obtain ⟨y, hy⟩ := hx r
    exact ⟨b * y, by rw [smul_eq_mul, map_mul, map_mul, hy, _root_.mul_assoc]⟩

/- English proof (translation)
Introduce `x hx r`. Take `⟨y, hy⟩` from `hx r`. Use `⟨y, fun r' ↦ ?_, hy⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hx (r * r')`. Conclude with `⟨z, by rw [hz, hy, _root_.mul_assoc]⟩`.
-/
theorem conductor_mul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] :
    ∀ x ∈ conductor R R', ∀ r : R', ∃ y ∈ conductor R R', algebraMap R R' y = algebraMap R R' x * r := by
  intro x hx r
  obtain ⟨y, hy⟩ := hx r
  refine ⟨y, fun r' ↦ ?_, hy⟩
  obtain ⟨z, hz⟩ := hx (r * r')
  exact ⟨z, by rw [hz, hy, _root_.mul_assoc]⟩

/- English proof (translation)
Use `set f := algebraMap R D`. Establish `hP` using `isGrpPullback_pullback A (spMap f)`. Take `⟨hA', hg'⟩` from `GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A ((Over.pullback (spMap f)).obj A) _ g hP hA hg`. Use `haveI : IsAffineHom (pullback.fst A.hom (spMap f)) := (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{0}).of_isPullback (IsPullback.of_hasPullback _ _).flip (inferInstance : IsAffineHom (spMap f))`. Establish `hV' : IsAffineOpen (pullback.fst A.hom (spMap f) ⁻¹ᵁ V)` using `hV.preimage _`.

Establish `hVs' : ∀ s : Sp D, ∃ x ∈ pullback.fst A.hom (spMap f) ⁻¹ᵁ V, ((Over.pullback (spMap f)).obj A).hom x = s`. Introduce `s`. Take `⟨x, hx, hxs⟩` from `hVs (spMap f s)`. Take `⟨z, hz1, hz2⟩` from `Scheme.Pullback.exists_preimage_pullback x s hxs`. Conclude with `⟨z, by simpa [hz1] using hx, hz2⟩`.

Take `⟨L, hL, hLa⟩` from `GlobalTheory.T.exists_relAmple_of_affineOpen_meets_fibres D _ hA' _ hV' hVs'`. Establish `h1` using `GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian D _ g hA' hg' L hL hLa`. Establish `h2` using `((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap f) A _ _ hP g (𝟙_ _)).2).1 h1`. Simplify using `using h2`.
-/
theorem hasRepAF_factor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (V : A.left.Opens) (hV : IsAffineOpen V)
    (hVs : ∀ s : Sp R, ∃ x ∈ V, A.hom x = s) (D : Type) [CommRing D] [Algebra R D] [IsNoetherianRing D]
    [IsDomain D] [IsIntegrallyClosed D] :
    HasRepAF A g (Over.mk (spMap (algebraMap R D))) := by
  set f := algebraMap R D
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) _ g hP hA hg
  haveI : IsAffineHom (pullback.fst A.hom (spMap f)) :=
    (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{0}).of_isPullback (IsPullback.of_hasPullback _ _).flip
      (inferInstance : IsAffineHom (spMap f))
  have hV' : IsAffineOpen (pullback.fst A.hom (spMap f) ⁻¹ᵁ V) := hV.preimage _
  have hVs' : ∀ s : Sp D, ∃ x ∈ pullback.fst A.hom (spMap f) ⁻¹ᵁ V,
      ((Over.pullback (spMap f)).obj A).hom x = s := by
    intro s
    obtain ⟨x, hx, hxs⟩ := hVs (spMap f s)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x s hxs
    exact ⟨z, by simpa [hz1] using hx, hz2⟩
  obtain ⟨L, hL, hLa⟩ := GlobalTheory.T.exists_relAmple_of_affineOpen_meets_fibres D _ hA' _ hV' hVs'
  have h1 := GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian D _ g hA' hg' L hL hLa
  have h2 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap f) A _ _ hP g (𝟙_ _)).2).1 h1
  simpa using h2

/- English proof (translation)
Introduce `R _ _ _ A _ g hA hg V hV hVs hJ`. Use `haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R`. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Use `haveI : IsEmpty (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))`. Take `⟨B, b, P, hP, hG, -⟩` from `GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty _ A (𝟙_ _) g this`.

Conclude with `⟨B, b, P, hP, hG⟩`. Take `⟨n, D, iR, iA, hD, hinj, a, ha0, ha⟩` from `GlobalTheory.T.reduced_finiteType_int_exists_finite_prod_normalDomains_nonzero_conductor R`. Establish `hfac : ∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))`. Introduce `i`. Take `⟨h1, h2, h3⟩` from `hD i`.

Use `haveI : IsNoetherianRing (D i) := by haveI : Algebra.FiniteType R (D i) := inferInstance`. Conclude with `Algebra.FiniteType.isNoetherianRing R (D i)`. Conclude with `hasRepAF_factor R A g hA hg V hV hVs (D i)`. Use `haveI : ∀ i, Module.Finite R (D i) := fun i ↦ (hD i).2.2`. Establish `hprod` using `GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras R A g hA n D hfac`.

Establish `hac : a ∈ conductor R (∀ i, D i)` using `ha`. Establish `hc : conductor R (∀ i, D i) ≠ ⊥` using `fun h ↦ ha0 (by rw [h] at hac; exact (Submodule.mem_bot R).1 hac)`. Conclude with `GlobalTheory.T.hasRepresentingScheme_pinchedBase R A g hA hg (∀ i, D i) hinj _ conductor_mul hprod (hJ _ hc)`.
-/
theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ _ A _ g hA hg V hV hVs hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : IsEmpty (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    obtain ⟨B, b, P, hP, hG, -⟩ := GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty _ A (𝟙_ _) g this
    exact ⟨B, b, P, hP, hG⟩
  obtain ⟨n, D, iR, iA, hD, hinj, a, ha0, ha⟩ := GlobalTheory.T.reduced_finiteType_int_exists_finite_prod_normalDomains_nonzero_conductor R
  have hfac : ∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i)))) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hD i
    haveI : IsNoetherianRing (D i) := by
      haveI : Algebra.FiniteType R (D i) := inferInstance
      exact Algebra.FiniteType.isNoetherianRing R (D i)
    exact hasRepAF_factor R A g hA hg V hV hVs (D i)
  haveI : ∀ i, Module.Finite R (D i) := fun i ↦ (hD i).2.2
  have hprod := GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras R A g hA n D hfac
  have hac : a ∈ conductor R (∀ i, D i) := ha
  have hc : conductor R (∀ i, D i) ≠ ⊥ := fun h ↦ ha0 (by rw [h] at hac; exact (Submodule.mem_bot R).1 hac)
  exact GlobalTheory.T.hasRepresentingScheme_pinchedBase R A g hA hg (∀ i, D i) hinj _ conductor_mul hprod (hJ _ hc)

end GlobalTheory.DualConStep
