import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory

/- English proof (translation)
Introduce `X Y f _ x x' hxx' hf`. Take `⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ`. Establish `hV : IsAffineOpen V` using `hV0`. Establish `hU : IsAffineOpen (f ⁻¹ᵁ V)` using `hV.preimage f`. Establish `hx' : x' ∈ f ⁻¹ᵁ V` using `hxV`.

Establish `hx : x ∈ f ⁻¹ᵁ V` using `hxx'.mem_open (f ⁻¹ᵁ V).isOpen hx'`. Use `set P := hU.primeIdealOf ⟨x, hx⟩ with hPdef`. Use `set P' := hU.primeIdealOf ⟨x', hx'⟩ with hP'def`. Establish `eP : hU.fromSpec P = x` using `hU.fromSpec_primeIdealOf ⟨x, hx⟩`. Establish `eP' : hU.fromSpec P' = x'` using `hU.fromSpec_primeIdealOf ⟨x', hx'⟩`.

Establish `hsp : P ⤳ P'`. Conclude with `hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 (by rw [eP, eP']; exact hxx')`. Establish `hle : P.asIdeal ≤ P'.asIdeal` using `(PrimeSpectrum.le_iff_specializes P P').mpr hsp`. Establish `sq : Spec.map (f.app V) ≫ hV.fromSpec = hU.fromSpec ≫ f`. Rewrite using `[Scheme.Hom.app_eq_appLE]`.

Conclude with `IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl`. Establish `img : ∀ Q : Spec Γ(X, f ⁻¹ᵁ V), hV.fromSpec (Spec.map (f.app V) Q) = f (hU.fromSpec Q)` using `fun Q => (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => m Q) sq).trans (Scheme.Hom.comp_apply _ _ _))`. Establish `hc : Spec.map (f.app V) P = Spec.map (f.app V) P'`. Apply `hV.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises. Conclude with `(img P).trans ((congrArg f eP).trans (hf.trans ((congrArg f eP').symm.trans (img P').symm)))`.

Establish `hc' : P.asIdeal.comap (f.app V).hom = P'.asIdeal.comap (f.app V).hom` using `congrArg PrimeSpectrum.asIdeal hc`. Use `letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra`. Use `haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩`. Establish `heq : P.asIdeal = P'.asIdeal`. Assume the negation of the conclusion as `hne`.

Establish `hlt` using `Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (lt_of_le_of_ne hle hne)`. Conclude with `(ne_of_lt hlt) hc'`. Establish `: P = P'` using `PrimeSpectrum.ext heq`. Rewrite using `[← eP, ← eP', this]`.
-/
theorem eq_of_specializes_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  intro X Y f _ x x' hxx' hf
  obtain ⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hx' : x' ∈ f ⁻¹ᵁ V := hxV
  have hx : x ∈ f ⁻¹ᵁ V := hxx'.mem_open (f ⁻¹ᵁ V).isOpen hx'
  set P := hU.primeIdealOf ⟨x, hx⟩ with hPdef
  set P' := hU.primeIdealOf ⟨x', hx'⟩ with hP'def
  have eP : hU.fromSpec P = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have eP' : hU.fromSpec P' = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have hsp : P ⤳ P' := by
    exact hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 (by rw [eP, eP']; exact hxx')
  have hle : P.asIdeal ≤ P'.asIdeal := (PrimeSpectrum.le_iff_specializes P P').mpr hsp
  have sq : Spec.map (f.app V) ≫ hV.fromSpec = hU.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
  have img : ∀ Q : Spec Γ(X, f ⁻¹ᵁ V), hV.fromSpec (Spec.map (f.app V) Q) = f (hU.fromSpec Q) :=
    fun Q => (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => m Q) sq).trans (Scheme.Hom.comp_apply _ _ _))
  have hc : Spec.map (f.app V) P = Spec.map (f.app V) P' := by
    apply hV.fromSpec.isOpenEmbedding.injective
    exact (img P).trans ((congrArg f eP).trans (hf.trans ((congrArg f eP').symm.trans (img P').symm)))
  have hc' : P.asIdeal.comap (f.app V).hom = P'.asIdeal.comap (f.app V).hom :=
    congrArg PrimeSpectrum.asIdeal hc
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  have heq : P.asIdeal = P'.asIdeal := by
    by_contra hne
    have hlt := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (lt_of_le_of_ne hle hne)
    exact (ne_of_lt hlt) hc'
  have : P = P' := PrimeSpectrum.ext heq
  rw [← eP, ← eP', this]

end GlobalTheory
