import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.Vanish

/- English proof (translation)
Take `⟨z, rfl⟩` from `H2.mk_surjective F c`. Use `H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' T'' φ ψ`. Use `z.2 (h.to T) φ ψ` as an intermediate fact. Rewrite `this` using `[h.to_comp φ]`.

Rewrite using `[d1_apply]`. Take the linear combination `this`.
-/
theorem commAlgFunctorCohomologyTwo_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {T₀ : C} (h : IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp φ] at this
  rw [d1_apply]
  linear_combination this

/- English proof (translation)
The claim follows from `subsingleton_of_forall_eq 0 fun ω ↦ Subtype.ext (funext fun T ↦ by rw [ω.2 (h.to T), Subsingleton.elim (ω.1 T₀) 0, map_zero]; rfl)`.
-/
theorem glob_sub {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : IsInitial T₀) [Subsingleton Ω[F.obj T₀⁄R]] : Subsingleton (Glob1 F) :=
  subsingleton_of_forall_eq 0 fun ω ↦ Subtype.ext (funext fun T ↦ by
    rw [ω.2 (h.to T), Subsingleton.elim (ω.1 T₀) 0, map_zero]; rfl)

def topInit {X : Scheme.{0}} (hX : IsAffineOpen (⊤ : X.Opens)) : IsInitial (op ⟨⊤, hX⟩ : AffOp X) :=
  IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, hX⟩ from le_top (a := U.unop.1))).op)
    fun _ _ ↦ rfl

/- English proof (translation)
Use `KaehlerDifferential.subsingleton_of_surjective R _ ?_` and prove the remaining obligations. Establish `: IsIso (secMap s ⊤)`. Unfold `secMap`. Use `haveI h1 : IsIso s.appTop := inferInstanceAs (IsIso (s.app ⊤))`. Use `haveI h2 : IsIso (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) := by`.

Rewrite using `[show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl]`. Use `infer_instance`. Conclude with `IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance (IsIso.comp_isIso' h1 h2)`. Conclude with `(ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2`.
-/
theorem omega_sub {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] :
    Subsingleton Ω[Sec s ⊤⁄R] := by
  refine KaehlerDifferential.subsingleton_of_surjective R _ ?_
  have : IsIso (secMap s ⊤) := by
    unfold secMap
    haveI h1 : IsIso s.appTop := inferInstanceAs (IsIso (s.app ⊤))
    haveI h2 : IsIso (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) := by
      rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl]
      infer_instance
    exact IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance
      (IsIso.comp_isIso' h1 h2)
  exact (ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2

/- English proof (translation)
Use `⟨fun R _ X s hX ↦ ?_, fun R _ ↦ ?_⟩` and prove the remaining obligations. Establish `h` using `topInit (isAffineOpen_top X)`. Conclude with `⟨subsingleton_of_forall_eq 0 (H1.eq_zero_of_isInitial _ h), subsingleton_of_forall_eq 0 (commAlgFunctorCohomologyTwo_eq_zero_of_isInitial _ h)⟩`. Use `haveI : IsIso (𝟙_ (Over (Sp R))).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))`. Establish `h` using `topInit (isAffineOpen_top (Sp R))`.

Use `haveI : Subsingleton Ω[(OAff (𝟙_ (Over (Sp R))).hom).obj (op ⟨⊤, isAffineOpen_top (Sp R)⟩)⁄R] := omega_sub (𝟙_ (Over (Sp R))).hom`. Use `haveI hg : Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) := glob_sub _ h`. Use `⟨hg, subsingleton_of_forall_eq 0 fun c ↦ ?_⟩` and prove the remaining obligations. Establish `hc : c ∈ Fil1 (OAff (𝟙_ (Over (Sp R))).hom)` using `H1.eq_zero_of_isInitial _ h _`. Rewrite `hc` using `[Fil1_eq_range]`.

Take `⟨ω, rfl⟩` from `hc`. Establish `: ω = 0` using `Subtype.ext (Subsingleton.elim (α := GlobForm (𝟙_ (Over (Sp R))).hom) _ _)`. Rewrite using `[this, map_zero]`.
-/
theorem main :
    (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsAffine X → Subsingleton (HO1 s) ∧ Subsingleton (HO2 s)) ∧
      ∀ (R : Type) [CommRing R], Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) ∧
        Subsingleton (HH1 (𝟙_ (Over (Sp R))).hom) := by
  refine ⟨fun R _ X s hX ↦ ?_, fun R _ ↦ ?_⟩
  · have h := topInit (isAffineOpen_top X)
    exact ⟨subsingleton_of_forall_eq 0 (H1.eq_zero_of_isInitial _ h),
      subsingleton_of_forall_eq 0 (commAlgFunctorCohomologyTwo_eq_zero_of_isInitial _ h)⟩
  · haveI : IsIso (𝟙_ (Over (Sp R))).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    have h := topInit (isAffineOpen_top (Sp R))
    haveI : Subsingleton Ω[(OAff (𝟙_ (Over (Sp R))).hom).obj (op ⟨⊤, isAffineOpen_top (Sp R)⟩)⁄R] :=
      omega_sub (𝟙_ (Over (Sp R))).hom
    haveI hg : Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) := glob_sub _ h
    refine ⟨hg, subsingleton_of_forall_eq 0 fun c ↦ ?_⟩
    have hc : c ∈ Fil1 (OAff (𝟙_ (Over (Sp R))).hom) := H1.eq_zero_of_isInitial _ h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    have : ω = 0 := Subtype.ext (Subsingleton.elim (α := GlobForm (𝟙_ (Over (Sp R))).hom) _ _)
    rw [this, map_zero]

end GlobalTheory.AbCoh.Vanish
