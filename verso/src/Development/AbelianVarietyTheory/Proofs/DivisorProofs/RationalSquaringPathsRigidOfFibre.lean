import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

/- English proof (translation)
Use `ext1 a`. Establish `h` using `(RatFunc.coe_coe (Polynomial.C a)).symm`. Rewrite `h` using `[Polynomial.coe_C]`. Conclude with `h`.
-/
theorem ratFunc_C_laurent (F : Type) [Field F] : (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C =
    (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  ext1 a
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

/- English proof (translation)
Set `x₀ : Over.mk (G'.hom ≫ f) ⟶ G` to `Over.homMk φ h.1.w`. Establish `e` using `h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl`. Establish `e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G)` using `by rw [comp_mul]; simp`. Rewrite `e` using `[e2]`. Conclude with `e.symm`.
-/
theorem sqr_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : sqr G' ≫ φ = φ ≫ sqr G := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e := h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl
  have e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G) := by rw [comp_mul]; simp
  rw [e2] at e
  exact e.symm

/- English proof (translation)
Introduce `S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩`. Establish `hp` using `isGrpPullback_pullback G b`. Establish `hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G` using `unitSec_comp hp`. Establish `hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G` using `sqr_comp_of_isGrpPullback hp`. Establish `hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b` using `Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))`.

Establish `hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _` using `sec_hom _`. Set `ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left` to `pullback.lift ξ (spMap PowerSeries.C) hξ.base`. Establish `hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ` using `pullback.lift_fst _ _ _`. Establish `hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C` using `pullback.lift_snd _ _ _`. Establish `hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), spMap g ≫ spMap f = spMap (g.comp f)` using `fun f g => by`.

Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hξ₂.trans (Category.comp_id _).symm`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]`. Rewrite using `[Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]`. Establish `: (PowerSeries.constantCoeff (R` using `Ω)).comp PowerSeries.C = RingHom.id Ω := by`. Use extensionality with `a`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]`. Rewrite using `[Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]`. Establish `: (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C` using `by ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]`. Apply the tactic sequence `rcases n with _ | n <;> simp`. Rewrite using `[this]`.

Establish `hβb : β ≫ G.hom = spMap RatFunc.C ≫ b`. Apply `GlobalTheory.spec_map_field_cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))` to reduce the goal to its premises. Rewrite using `[← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp, ratFunc_C_laurent]`. Set `β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left` to `pullback.lift β (spMap RatFunc.C) hβb`. Establish `hrat : IsRatPath ξ'`.

Use `⟨β', ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]`. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]`. Establish `e` using `hR ξ' hpath hrat`.

Rewrite using `[← hξ₁, e]`. Simplify using `only [triv, Category.assoc, hu, Category.id_comp]`.
-/
theorem ratRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω]
    (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  intro S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩
  have hp := isGrpPullback_pullback G b
  have hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G := unitSec_comp hp
  have hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G :=
    sqr_comp_of_isGrpPullback hp
  have hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b :=
    Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))
  have hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _ := sec_hom _
  let ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift ξ (spMap PowerSeries.C) hξ.base
  have hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ := pullback.lift_fst _ _ _
  have hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C := pullback.lift_snd _ _ _
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ' := by
    refine ⟨?_, ?_, ?_⟩
    · exact hξ₂.trans (Category.comp_id _).symm
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]
      · rw [Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]
        have : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω := by
          ext a; simp
        rw [this]
        show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _
        rw [CommRingCat.ofHom_id, Spec.map_id]
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]
      · rw [Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]
        have : (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C := by
          ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
          rcases n with _ | n <;> simp
        rw [this]
  have hβb : β ≫ G.hom = spMap RatFunc.C ≫ b := by
    apply GlobalTheory.spec_map_field_cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp,
      ratFunc_C_laurent]
  let β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift β (spMap RatFunc.C) hβb
  have hrat : IsRatPath ξ' := by
    refine ⟨β', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]
  have e := hR ξ' hpath hrat
  rw [← hξ₁, e]
  simp only [triv, Category.assoc, hu, Category.id_comp]

end GlobalTheory.Nef
