import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

/- English proof (translation)
Set `x₀ : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ π) (by show _ = T.hom ≫ f`. Rewrite using `[Category.assoc, hg.1.w, ← Category.assoc, Over.w])`. Establish `h` using `hg.2 T 1 1 x₀ x₀ rfl rfl`. Rewrite `h` using `[_root_.mul_one]`. Establish `e : x₀ * x₀ = x₀` using `Over.OverMorphism.ext h`.

Establish `e' : x₀ = 1`. Use `congrArg (· * x₀⁻¹) e` as an intermediate fact. Simplify using `using this`. Conclude with `congrArg Over.Hom.left e'`.
-/
theorem one_left_π {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) (T : Over S') :
    (1 : T ⟶ G').left ≫ π = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
    show _ = T.hom ≫ f
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
  have h := hg.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have e : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have e' : x₀ = 1 := by
    have := congrArg (· * x₀⁻¹) e
    simpa using this
  exact congrArg Over.Hom.left e'

/- English proof (translation)
Take `⟨β₀, h1, h2⟩` from `P'.fin.one O (lo P' x0 hu)`. Establish `hβ₀ : β₀.comp P'.str = (algebraMap O O).comp x0`. Rewrite using `[GlobalTheory.HTMap.FP.str, ← RingHom.comp_assoc, h1, lo_comp]`. Apply the tactic sequence `try rfl`. Establish `hid : (specO O O).hom = 𝟙 _`.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (algebraMap O O)) = _`. Rewrite using `[Algebra.algebraMap_self]`. Conclude with `Spec.map_id _`. Apply the tactic sequence `let c : S ⟶ specO O O := Over.homMk S.hom (by rw [hid, Category.comp_id]; try rfl)`. Use `⟨c ≫ ptOf P' x0 hu β₀ hβ₀, ?_⟩` and prove the remaining obligations.

Establish `hz : ptOf P' x0 hu β₀ hβ₀ ≫ aH P' x0 hu hg.1 = 1`. Use `Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[ptOf_aH_π, h2, one_left_π hg]`. Use `(GlobalTheory.HTMap.one_of (G := t.G) (g := 𝟙 _) ?_).trans (Category.id_comp _)` and prove the remaining obligations. Rewrite using `[Category.id_comp, hid, Category.id_comp, GlobalTheory.HTMap.spc_assoc, lo_comp]`.

Rewrite using `[Over.w, Over.w]`. Rewrite using `[Category.assoc, hz, MonObj.comp_one]`.
-/
theorem exists_unit {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) :
    ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = 1 := by
  obtain ⟨β₀, h1, h2⟩ := P'.fin.one O (lo P' x0 hu)
  have hβ₀ : β₀.comp P'.str = (algebraMap O O).comp x0 := by
    rw [GlobalTheory.HTMap.FP.str, ← RingHom.comp_assoc, h1, lo_comp]
    try rfl
  have hid : (specO O O).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let c : S ⟶ specO O O := Over.homMk S.hom (by rw [hid, Category.comp_id]; try rfl)
  refine ⟨c ≫ ptOf P' x0 hu β₀ hβ₀, ?_⟩
  have hz : ptOf P' x0 hu β₀ hβ₀ ≫ aH P' x0 hu hg.1 = 1 := by
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, h2, one_left_π hg]
      refine (GlobalTheory.HTMap.one_of (G := t.G) (g := 𝟙 _) ?_).trans (Category.id_comp _)
      rw [Category.id_comp, hid, Category.id_comp, GlobalTheory.HTMap.spc_assoc, lo_comp]
    · rw [Over.w, Over.w]
  rw [Category.assoc, hz, MonObj.comp_one]

end GlobalTheory.FinPartAt
