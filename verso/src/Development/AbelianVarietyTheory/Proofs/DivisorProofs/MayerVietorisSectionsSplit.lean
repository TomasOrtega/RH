import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

/- English proof (translation)
Introduce `Y F W₁ W₂ h t`. Set `A` to `(toAbSheaf Y).obj F`. Set `S` to `Flasque.injectiveShortComplex A`. Establish `hS : S.ShortExact` using `Flasque.injectiveShortComplex_shortExact A`. Establish `hfl : TopCat.Sheaf.IsFlasque S.X₂` using `Flasque.isFlasque_injectiveShortComplex_X₂ A`.

Establish `hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W))`. Introduce `W x y hxy`. Take `⟨x, rfl⟩` from `(SheafLES.equivZero.{0} S.X₁ W).surjective x`. Take `⟨y, rfl⟩` from `(SheafLES.equivZero.{0} S.X₁ W).surjective y`. Rewrite `hxy` using `[← SheafLES.equivZero_map, ← SheafLES.equivZero_map]`.

Rewrite using `[SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]`. Establish `hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W))`. Introduce `W x`. Take `⟨x, rfl⟩` from `(SheafLES.equivZero.{0} S.X₂ W).surjective x`. Rewrite using `[← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨_, (SheafLES.equivZero_map S.f W y).symm⟩`. Introduce and unpack `⟨y, hy⟩`. Take `⟨y, rfl⟩` from `(SheafLES.equivZero.{0} S.X₁ W).surjective y`.

Conclude with `⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective ((SheafLES.equivZero_map S.f W y).trans hy)⟩`. Establish `natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x, S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) = S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x)` using `fun hUV x => NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x`. Establish `natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x, S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) = S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x)` using `fun hUV x => NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x`. Establish `resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x, S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) = S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x` using `fun h₁ h₂ x => by`. Rewrite using `[← ConcreteCategory.comp_apply, ← Functor.map_comp]`.

Both sides reduce to the same expression. Establish `resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x, S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) = S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x` using `fun h₁ h₂ x => by`. Rewrite using `[← ConcreteCategory.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression. Take `⟨b', hb'⟩` from `(AddCommGrpCat.epi_iff_surjective (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _) (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))`.

Set `U : Bool → Y.Opens` to `fun b => cond b W₂ W₁`. Set `sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b)))` to `fun b => match b with`. Consider the case `true => S.g.hom.app (op W₂) b'`. Consider the case `false => 0`. Establish `h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0`.

Rewrite using `[← natg, hb']`. Conclude with `(hex _).apply_apply_eq_zero _`. Establish `h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0`. Establish `e` using `resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')`. Rewrite `e` using `[h0, map_zero]`.

Conclude with `e.symm`. Establish `hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf`. Introduce `i j`. Apply the tactic sequence `cases i <;> cases j`. Both sides reduce to the same expression.

Conclude with `(map_zero _).trans h0.symm`. Conclude with `h0'.trans (map_zero _).symm`. Both sides reduce to the same expression. Take `⟨q, hq, -⟩` from `TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂) (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right])) (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp`. Take `⟨i, hi⟩` from `SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q`.

Take `⟨bb, hbb⟩` from `(hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by`. Rewrite using `[map_sub, natg, hi]`. Conclude with `sub_eq_zero.2 (hq true).symm)`. Take `⟨aa, haa⟩` from `(hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by`. Rewrite using `[map_neg, natg, hi]`.

Conclude with `neg_eq_zero.2 (hq false))`. Use `⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩` and prove the remaining obligations. Apply `(sectionsOn.toΓ F _).injective` to reduce the goal to its premises. Rewrite using `[map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]`. Simplify using `only [AddEquiv.apply_symm_apply]`.

Apply `hinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)`. Use `erw [map_sub]`. Rewrite using `[natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']`. Normalize the expressions using the abelian group laws.
-/
theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
