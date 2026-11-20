import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinStalk

/- English proof (translation)
Establish `: IsAffine X` using `isAffine_of_isAffineHom f`. Establish `hfin : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.Finite` using `f.finite_appTop.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)`. Use `letI := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra`. Use `haveI : Module.Finite K Γ(X, ⊤) := hfin`. Use `haveI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)`.

Establish `hU` using `isAffineOpen_top X`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))`. Establish `hl` using `hU.isLocalization_stalk ⟨x, trivial⟩`. Conclude with `IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _`.
-/
theorem stalk_isArtinianRing (K : Type) [Field K] (X : Scheme) (f : X ⟶ Sp K) [IsFinite f] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have hfin : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite K Γ(X, ⊤) := hfin
  haveI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  have hU := isAffineOpen_top X
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have hl := hU.isLocalization_stalk ⟨x, trivial⟩
  exact IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _

end GlobalTheory.FinStalk

namespace GlobalTheory.FinStalk

/- English proof (translation)
Introduce `K _ A _ H _ j hj hci hfin x₀ hx₀ J hJ`. Take `⟨p, hp⟩` from `hx₀`. Establish `hη : (η[H] ≫ j).left = η[A].left` using `congrArg CommaMorphism.left (IsMonHom.one_hom j)`. Take `⟨h₀, e⟩ : ∃ h₀ : H.left, x₀ = j.left.base h₀` from `⟨η[H].left.base p, by rw [← hp, ← hη]; rfl⟩`. Substitute `e` using the available equality.

Establish `hJ1 : J ≤ RingHom.ker (j.left.stalkMap h₀).hom` using `(hJ (H.left.presheaf.stalk h₀) (j.left.stalkMap h₀).hom).1 ⟨H.left.fromSpecStalk h₀, (Scheme.SpecMap_stalkMap_fromSpecStalk j.left).symm⟩`. Establish `hne : J ≠ ⊤` using `fun h => RingHom.ker_ne_top _ (top_le_iff.1 (h ▸ hJ1))`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Use `haveI : Nontrivial (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne`. Use `haveI : IsLocalRing (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective`.

Use `haveI : IsLocalHom (Ideal.Quotient.mk J) := Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective`. Take `⟨y, hy⟩` from `(hJ _ (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])`. Set `R` to `CommRingCat.of (A.left.presheaf.stalk (j.left.base h₀) ⧸ J)`. Establish `hpt : y.base (IsLocalRing.closedPoint R) = h₀`. Apply `j.left.isClosedEmbedding.injective` to reduce the goal to its premises.

Establish `: j.left.base (y.base (IsLocalRing.closedPoint R)) = (A.left.fromSpecStalk (j.left.base h₀)).base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base (IsLocalRing.closedPoint R))` using `congrArg (fun g : Sp R ⟶ A.left => g.base (IsLocalRing.closedPoint R)) hy`. Rewrite using `[this]`. Use `haveI : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by`. Express the relevant statement in the definitionally equal form `IsLocalHom (Ideal.Quotient.mk J)`. Use `infer_instance`.

Rewrite using `[Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]`. Establish `key : ∀ z (_ : y.base (IsLocalRing.closedPoint R) = z), ∃ φ : H.left.presheaf.stalk z ⟶ R, Spec.map φ ≫ H.left.fromSpecStalk z = y`. Introduce and unpack `z rfl`. Conclude with `⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y⟩`. Take `⟨φ, hφ⟩` from `key h₀ hpt`.

Establish `hcomp : j.left.stalkMap h₀ ≫ φ = CommRingCat.ofHom (Ideal.Quotient.mk J)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (A.left.fromSpecStalk (j.left.base h₀)), ← hy, ← hφ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]`. Establish `hsurj : Function.Surjective φ.hom`. Introduce `r`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective (I := J) r`. Conclude with `⟨(j.left.stalkMap h₀).hom a, by`. Rewrite using `[← CommRingCat.comp_apply, hcomp]`. Use the proof step `rfl⟩`. Use `haveI := stalk_isArtinianRing K H.left H.hom h₀`.

Conclude with `hsurj.isArtinianRing`.
-/
theorem stalk_quotient_ne_top_and_isArtinianRing : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  intro K _ A _ H _ j hj hci hfin x₀ hx₀ J hJ
  obtain ⟨p, hp⟩ := hx₀
  have hη : (η[H] ≫ j).left = η[A].left := congrArg CommaMorphism.left (IsMonHom.one_hom j)
  obtain ⟨h₀, e⟩ : ∃ h₀ : H.left, x₀ = j.left.base h₀ :=
    ⟨η[H].left.base p, by rw [← hp, ← hη]; rfl⟩
  subst e

  have hJ1 : J ≤ RingHom.ker (j.left.stalkMap h₀).hom :=
    (hJ (H.left.presheaf.stalk h₀) (j.left.stalkMap h₀).hom).1
      ⟨H.left.fromSpecStalk h₀, (Scheme.SpecMap_stalkMap_fromSpecStalk j.left).symm⟩
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top _ (top_le_iff.1 (h ▸ hJ1))
  refine ⟨hne, ?_⟩
  haveI : Nontrivial (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hJ _ (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
  let R := CommRingCat.of (A.left.presheaf.stalk (j.left.base h₀) ⧸ J)
  have hpt : y.base (IsLocalRing.closedPoint R) = h₀ := by
    apply j.left.isClosedEmbedding.injective
    have : j.left.base (y.base (IsLocalRing.closedPoint R)) = (A.left.fromSpecStalk (j.left.base h₀)).base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base (IsLocalRing.closedPoint R)) :=
      congrArg (fun g : Sp R ⟶ A.left => g.base (IsLocalRing.closedPoint R)) hy
    rw [this]
    haveI : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by
      change IsLocalHom (Ideal.Quotient.mk J); infer_instance
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ z (_ : y.base (IsLocalRing.closedPoint R) = z),
      ∃ φ : H.left.presheaf.stalk z ⟶ R, Spec.map φ ≫ H.left.fromSpecStalk z = y := by
    rintro z rfl
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y⟩
  obtain ⟨φ, hφ⟩ := key h₀ hpt
  have hcomp : j.left.stalkMap h₀ ≫ φ = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply Spec.map_injective
    rw [← cancel_mono (A.left.fromSpecStalk (j.left.base h₀)), ← hy, ← hφ, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  have hsurj : Function.Surjective φ.hom := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) r
    exact ⟨(j.left.stalkMap h₀).hom a, by
      rw [← CommRingCat.comp_apply, hcomp]; rfl⟩
  haveI := stalk_isArtinianRing K H.left H.hom h₀
  exact hsurj.isArtinianRing

end GlobalTheory.FinStalk
