import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeAffine

/- English proof (translation)
Use `set R := Subring.closure (Set.range i.hom ∪ Set.range j.hom)`. Set `l : B ⟶ CommRingCat.of R` to `CommRingCat.ofHom (i.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))`. Set `r : C ⟶ CommRingCat.of R` to `CommRingCat.ofHom (j.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))`. Establish `w : f ≫ l = g ≫ r`. Use extensionality with `a`.

Use `congrArg (fun q : A ⟶ P => q.hom a) h.w` as an intermediate fact. Simplify `this` using `[l, r]`. Set `s : CommRingCat.of R ⟶ P` to `CommRingCat.ofHom R.subtype`. Establish `hid : h.desc l r w ≫ s = 𝟙 P`. Apply `h.hom_ext` to reduce the goal to its premises.

Use extensionality with `b`. Simplify using `[l, s]`. Use extensionality with `c`. Simplify using `[r, s]`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations.

Establish `hx : (((h.desc l r w).hom x : R) : P) = x`. Use `congrArg (fun q : P ⟶ P => q.hom x) hid` as an intermediate fact. Simplify `this` using `[s]`. Rewrite using `[← hx]`. Conclude with `((h.desc l r w).hom x).2`.
-/
theorem closure_range_union_eq_top_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g i j) :
    Subring.closure (Set.range i.hom ∪ Set.range j.hom) = ⊤ := by
  set R := Subring.closure (Set.range i.hom ∪ Set.range j.hom)
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (i.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (j.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let s : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ s = 𝟙 P := by
    apply h.hom_ext
    · ext b; simp [l, s]
    · ext c; simp [r, s]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [s] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2

/- English proof (translation)
Introduce `Z Z' X X' p p' φ g H U U' hU' O hO`. Establish `: IsAffine U.1.toScheme` using `U.2`. Establish `: IsAffine U'.1.toScheme` using `U'.2`. Establish `: IsAffine O.1.toScheme` using `O.2`. Establish `hpb` using `Scheme.Hom.isPullback_resLE H (US := U.1) (UT := U'.1) (UX := O.1) (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU' hO rfl`.

Use `⟨.of_isIso hpb.isoPullback.hom, ?_⟩` and prove the remaining obligations. Establish `po` using `(isIso_pushoutSection_iff H hU' hO (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) rfl).1 (isIso_pushoutSection_of_isAffineOpen H hU' hO rfl U.2 U'.2 O.2)`. Conclude with `closure_range_union_eq_top_of_isPushout po`.
-/
theorem affine_and_closure_eq_top : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (O : Z.affineOpens), O.1 ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) ∧ Subring.closure (Set.range (φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left).hom ∪ Set.range (p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right).hom) = ⊤ := by
  intro Z Z' X X' p p' φ g H U U' hU' O hO
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine U'.1.toScheme := U'.2
  have : IsAffine O.1.toScheme := O.2
  have hpb := Scheme.Hom.isPullback_resLE H (US := U.1) (UT := U'.1) (UX := O.1)
    (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU' hO rfl
  refine ⟨.of_isIso hpb.isoPullback.hom, ?_⟩
  have po := (isIso_pushoutSection_iff H hU' hO (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hU' hO rfl U.2 U'.2 O.2)
  exact closure_range_union_eq_top_of_isPushout po

end GlobalTheory.BaseChangeAffine
