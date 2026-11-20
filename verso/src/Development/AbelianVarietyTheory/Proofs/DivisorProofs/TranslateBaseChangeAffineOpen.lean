import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R R₁ _ _ ρ G _ V hV a`. Set `f` to `spMap ρ`. Set `G₁` to `(Over.pullback f).obj G`. Set `a₁ : Over.mk (𝟙 (Sp R₁)) ⟶ G₁` to `Over.homMk (pullback.lift (f := G.hom) (g := f) a.left (𝟙 (Sp R₁)) ((Over.w a).trans (Category.id_comp _).symm)) (by show pullback.lift _ _ _ ≫ pullback.snd G.hom f = 𝟙 _; exact pullback.lift_snd _ _ _)`. Set `e : G₁ ⟶ Over.mk (𝟙 (Sp R₁))` to `Over.homMk G₁.hom (by simp)`.

Set `c : G₁ ⟶ G₁` to `e ≫ a₁`. Establish `hc : ∀ g : G₁ ⟶ G₁, g ≫ c = c` using `fun g => by rw [← Category.assoc]; congr 1; ext; simp [e]`. Set `T : G₁ ⟶ G₁` to `𝟙 G₁ * c`. Set `T' : G₁ ⟶ G₁` to `𝟙 G₁ * c⁻¹`. Establish `h₁ : T ≫ T' = 𝟙 G₁`.

Simplify using `only [T', MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, hc, T, mul_inv_cancel_right]`. Establish `h₂ : T' ≫ T = 𝟙 G₁`. Simplify using `only [T, MonObj.comp_mul, Category.comp_id, T', hc, inv_mul_cancel_right]`. Use `haveI : IsIso T := ⟨⟨T', h₁, h₂⟩⟩`. Use `haveI : IsIso T.left := Functor.map_isIso (Over.forget _) T`.

Use `haveI : IsAffineHom (pullback.fst G.hom f) := isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.hom f).flip (inferInstanceAs (IsAffineHom (spMap ρ)))`. Use `⟨(T.left ≫ pullback.fst G.hom f) ⁻¹ᵁ V, hV.preimage _, ?_⟩` and prove the remaining obligations. Introduce `Ω _ z t x a' hx ha hxa w`. Establish `ht : t = (z ≫ pullback.snd G.hom f) ≫ f`. Establish `h0 : x.left ≫ G.hom = t` using `Over.w x`.

Rewrite using `[← h0, hx, Category.assoc, pullback.condition, Category.assoc]`. Substitute `ht` using the available equality. Set `Z : Over (Sp R₁)` to `Over.mk (z ≫ pullback.snd G.hom f)`. Set `z' : Z ⟶ G₁` to `Over.homMk z (by simp [G₁, Z])`. Establish `key` using `(isGrpPullback_pullback G f).2 Z z' (z' ≫ c) x a' (by simpa [z'] using hx) (by rw [ha]; simp [z', c, e, a₁, G₁, pullback.lift_fst]; rfl)`.

Establish `hT : z' * (z' ≫ c) = z' ≫ T` using `by simp only [T, MonObj.comp_mul, Category.comp_id]`. Rewrite `key` using `[hT]`. Establish `: (z ≫ T.left ≫ pullback.fst G.hom f) w ∈ V`. Establish `e2 : z ≫ T.left ≫ pullback.fst G.hom f = (x * a').left`. Rewrite using `[key]`.

Simplify using `[z']`. Rewrite using `[e2]`. Conclude with `hxa w`. Simplify using `using this`.
-/
theorem translate_baseChange_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (G : Over (Sp R)) [GrpObj G] (V : G.left.Opens), IsAffineOpen V → ∀ (a : Over.mk (spMap ρ) ⟶ G), ∃ W : (pullback G.hom (spMap ρ)).Opens, IsAffineOpen W ∧ ∀ (Ω : Type) [Field Ω] (z : Sp Ω ⟶ pullback G.hom (spMap ρ)) (t : Sp Ω ⟶ Sp R) (x a' : Over.mk t ⟶ G), x.left = z ≫ pullback.fst _ _ → a'.left = z ≫ pullback.snd _ _ ≫ a.left → (∀ w, (x * a').left w ∈ V) → ∀ w, z w ∈ W := by
  intro R R₁ _ _ ρ G _ V hV a
  let f := spMap ρ
  let G₁ := (Over.pullback f).obj G
  let a₁ : Over.mk (𝟙 (Sp R₁)) ⟶ G₁ :=
    Over.homMk (pullback.lift (f := G.hom) (g := f) a.left (𝟙 (Sp R₁))
      ((Over.w a).trans (Category.id_comp _).symm))
      (by show pullback.lift _ _ _ ≫ pullback.snd G.hom f = 𝟙 _; exact pullback.lift_snd _ _ _)
  let e : G₁ ⟶ Over.mk (𝟙 (Sp R₁)) := Over.homMk G₁.hom (by simp)
  let c : G₁ ⟶ G₁ := e ≫ a₁
  have hc : ∀ g : G₁ ⟶ G₁, g ≫ c = c := fun g =>
    by rw [← Category.assoc]; congr 1; ext; simp [e]
  let T : G₁ ⟶ G₁ := 𝟙 G₁ * c
  let T' : G₁ ⟶ G₁ := 𝟙 G₁ * c⁻¹
  have h₁ : T ≫ T' = 𝟙 G₁ := by
    simp only [T', MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, hc, T, mul_inv_cancel_right]
  have h₂ : T' ≫ T = 𝟙 G₁ := by
    simp only [T, MonObj.comp_mul, Category.comp_id, T', hc, inv_mul_cancel_right]
  haveI : IsIso T := ⟨⟨T', h₁, h₂⟩⟩
  haveI : IsIso T.left := Functor.map_isIso (Over.forget _) T
  haveI : IsAffineHom (pullback.fst G.hom f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.hom f).flip
      (inferInstanceAs (IsAffineHom (spMap ρ)))
  refine ⟨(T.left ≫ pullback.fst G.hom f) ⁻¹ᵁ V, hV.preimage _, ?_⟩
  intro Ω _ z t x a' hx ha hxa w
  have ht : t = (z ≫ pullback.snd G.hom f) ≫ f := by
    have h0 : x.left ≫ G.hom = t := Over.w x
    rw [← h0, hx, Category.assoc, pullback.condition, Category.assoc]
  subst ht
  let Z : Over (Sp R₁) := Over.mk (z ≫ pullback.snd G.hom f)
  let z' : Z ⟶ G₁ := Over.homMk z (by simp [G₁, Z])
  have key := (isGrpPullback_pullback G f).2 Z z' (z' ≫ c) x a' (by simpa [z'] using hx)
    (by rw [ha]; simp [z', c, e, a₁, G₁, pullback.lift_fst]; rfl)
  have hT : z' * (z' ≫ c) = z' ≫ T := by simp only [T, MonObj.comp_mul, Category.comp_id]
  rw [hT] at key
  have : (z ≫ T.left ≫ pullback.fst G.hom f) w ∈ V := by
    have e2 : z ≫ T.left ≫ pullback.fst G.hom f = (x * a').left := by
      rw [key]; simp [z']
    rw [e2]; exact hxa w
  simpa using this

end GlobalTheory.Mum
