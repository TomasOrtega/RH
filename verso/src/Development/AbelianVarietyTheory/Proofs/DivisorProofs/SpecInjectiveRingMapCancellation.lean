import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

/- English proof (translation)
Take `⟨hcomp, -, -, hloc, hext, -, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk`. Establish `hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R` using `IsLocalRing.comap_closedPoint φ`. Establish `hy : a (IsLocalRing.closedPoint R) = a' (IsLocalRing.closedPoint R)`. Use `congrArg (fun f : Sp R' ⟶ Y => f (IsLocalRing.closedPoint R')) h` as an intermediate fact. Conclude with `(congrArg a hc).symm.trans ((Scheme.Hom.comp_apply _ _ _).symm.trans (this.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg a' hc))))`.

Take `⟨U, hU, hyU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Y) (x := a (IsLocalRing.closedPoint R)) (U := ⊤) trivial`. Establish `h1 : ⊤ ≤ a ⁻¹ᵁ U` using `(hloc R Y a U).2 hyU`. Establish `h2 : ⊤ ≤ a' ⁻¹ᵁ U` using `(hloc R Y a' U).2 (hy ▸ hyU)`. Establish `h1' : ⊤ ≤ (spMap φ ≫ a) ⁻¹ᵁ U` using `(hloc R' Y _ U).2 (((Scheme.Hom.comp_apply _ _ _).trans (congrArg a hc)) ▸ hyU)`. Establish `h2' : ⊤ ≤ (spMap φ ≫ a') ⁻¹ᵁ U` using `h ▸ h1'`.

Establish `key : ∀ (b b' : Sp R' ⟶ Y) (_ : b = b') (hb : ⊤ ≤ b ⁻¹ᵁ U) (hb' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b hb = evAt b' hb'`. Introduce and unpack `b _ rfl _ _`. Both sides reduce to the same expression. Use `hext R Y a a' U hU h1 h2 (RingHom.ext fun f => hφ ?_)` and prove the remaining obligations. Rewrite using `[← hcomp R R' Y φ a U h1 h1' f, ← hcomp R R' Y φ a' U h2 h2' f, key _ _ h h1' h2']`.
-/
theorem spec_localInjective_cancel_left (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
    (φ : R →+* R') [IsLocalHom φ] (hφ : Function.Injective φ) (Y : Scheme.{0}) (a a' : Sp R ⟶ Y)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  obtain ⟨hcomp, -, -, hloc, hext, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint φ
  have hy : a (IsLocalRing.closedPoint R) = a' (IsLocalRing.closedPoint R) := by
    have := congrArg (fun f : Sp R' ⟶ Y => f (IsLocalRing.closedPoint R')) h
    exact (congrArg a hc).symm.trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
      (this.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg a' hc))))
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := a (IsLocalRing.closedPoint R))
    (U := ⊤) trivial
  have h1 : ⊤ ≤ a ⁻¹ᵁ U := (hloc R Y a U).2 hyU
  have h2 : ⊤ ≤ a' ⁻¹ᵁ U := (hloc R Y a' U).2 (hy ▸ hyU)
  have h1' : ⊤ ≤ (spMap φ ≫ a) ⁻¹ᵁ U := (hloc R' Y _ U).2 (((Scheme.Hom.comp_apply _ _ _).trans (congrArg a hc)) ▸ hyU)
  have h2' : ⊤ ≤ (spMap φ ≫ a') ⁻¹ᵁ U := h ▸ h1'
  have key : ∀ (b b' : Sp R' ⟶ Y) (_ : b = b') (hb : ⊤ ≤ b ⁻¹ᵁ U) (hb' : ⊤ ≤ b' ⁻¹ᵁ U),
      evAt b hb = evAt b' hb' := by
    rintro b _ rfl _ _; rfl
  refine hext R Y a a' U hU h1 h2 (RingHom.ext fun f => hφ ?_)
  rw [← hcomp R R' Y φ a U h1 h1' f, ← hcomp R R' Y φ a' U h2 h2' f, key _ _ h h1' h2']

/- English proof (translation)
Set `d : Sp R ⟶ pullback p p` to `pullback.lift a a' hp`. Establish `e1 : a = d ≫ pullback.fst p p` using `(pullback.lift_fst _ _ _).symm`. Establish `e2 : a' = d ≫ pullback.snd p p` using `(pullback.lift_snd _ _ _).symm`. Set `i : pullback d (pullback.diagonal p) ⟶ Sp R` to `pullback.fst _ _`. Establish `hfac : spMap φ ≫ d = (spMap φ ≫ a) ≫ pullback.diagonal p`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]`. Rewrite using `[Category.assoc, ← e2, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]`. Set `g : Sp R' ⟶ pullback d (pullback.diagonal p)` to `pullback.lift (spMap φ) (spMap φ ≫ a) hfac`. Establish `hg : g ≫ i = spMap φ` using `pullback.lift_fst _ _ _`.

Establish `key : (spMap φ).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso _).inv`. Rewrite using `[Scheme.ΓSpecIso_inv_naturality]`. Simplify using the standard rewrite rules. Establish `h2 : Function.Injective (spMap φ).appTop`. Rewrite using `[key]`.

Conclude with `((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.injective.comp hφ).comp (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective`. Establish `hinj : Function.Injective i.appTop`. Rewrite `h2` using `[← hg, Scheme.Hom.comp_appTop]`. Conclude with `Function.Injective.of_comp h2`. Establish `: IsIso i` using `IsClosedImmersion.isIso_of_injective_of_isAffine hinj`.

Establish `hd : d = inv i ≫ pullback.snd _ _ ≫ pullback.diagonal p`. Rewrite using `[← pullback.condition]`. Simplify using `[i]`. Rewrite using `[e1, e2, hd]`. Simplify using the standard rewrite rules.
-/
theorem spec_injective_cancel_left_of_separated (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Injective φ)
    (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y) (hp : a ≫ p = a' ≫ p)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  let d : Sp R ⟶ pullback p p := pullback.lift a a' hp
  have e1 : a = d ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
  have e2 : a' = d ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
  let i : pullback d (pullback.diagonal p) ⟶ Sp R := pullback.fst _ _
  have hfac : spMap φ ≫ d = (spMap φ ≫ a) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, ← e2, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  let g : Sp R' ⟶ pullback d (pullback.diagonal p) := pullback.lift (spMap φ) (spMap φ ≫ a) hfac
  have hg : g ≫ i = spMap φ := pullback.lift_fst _ _ _
  have key : (spMap φ).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality]; simp
  have h2 : Function.Injective (spMap φ).appTop := by
    rw [key]
    exact ((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.injective.comp hφ).comp
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
  have hinj : Function.Injective i.appTop := by
    rw [← hg, Scheme.Hom.comp_appTop] at h2
    exact Function.Injective.of_comp h2
  have : IsIso i := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  have hd : d = inv i ≫ pullback.snd _ _ ≫ pullback.diagonal p := by
    rw [← pullback.condition]; simp [i]
  rw [e1, e2, hd]; simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun R R' _ _ _ _ φ _ hφ Y a a' h => spec_localInjective_cancel_left R R' φ hφ Y a a' h, fun R R' _ _ φ hφ S Y p _ a a' hp h => spec_injective_cancel_left_of_separated R R' φ hφ S Y p a a' hp h⟩`.
-/
theorem spMap_injective_cancel : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') :=
  ⟨fun R R' _ _ _ _ φ _ hφ Y a a' h => spec_localInjective_cancel_left R R' φ hφ Y a a' h,
    fun R R' _ _ φ hφ S Y p _ a a' hp h => spec_injective_cancel_left_of_separated R R' φ hφ S Y p a a' hp h⟩

end GlobalTheory.Nef
