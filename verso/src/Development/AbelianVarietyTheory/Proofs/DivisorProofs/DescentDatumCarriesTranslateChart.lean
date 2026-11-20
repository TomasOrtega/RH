import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G' : Over S} [GrpObj G']

/- English proof (translation)
Take `⟨x₁, e₁, e₂, e₃⟩` from `hφ.2 T (x₀ ≫ pullback.fst _ _) z ⟨x₀, rfl, by rw [← Category.assoc, hz₂, h₂], hz₁.symm⟩`. Establish `: x₁ = x₀'` using `pullback.hom_ext (e₁.trans h₁.symm) (by rw [e₂, ← Category.assoc, hz₂, h₃])`. Rewrite using `[← e₃, this]`.
-/
theorem Near.datum_pt (N : Near π G') {φ} (hφ : N.Datum φ) {T : Scheme.{0}} (s : T ⟶ pullback π π)
    (x₀ x₀' : T ⟶ pullback N.U.hom π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (h₁ : x₀' ≫ pullback.fst _ _ = x₀ ≫ pullback.fst _ _) (h₂ : x₀ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₃ : x₀' ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (hz₁ : z ≫ pullback.fst _ _ = x₀ ≫ N.u)
    (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = x₀' ≫ N.u := by
  obtain ⟨x₁, e₁, e₂, e₃⟩ := hφ.2 T (x₀ ≫ pullback.fst _ _) z
    ⟨x₀, rfl, by rw [← Category.assoc, hz₂, h₂], hz₁.symm⟩
  have : x₁ = x₀' := pullback.hom_ext (e₁.trans h₁.symm) (by rw [e₂, ← Category.assoc, hz₂, h₃])
  rw [← e₃, this]

/- English proof (translation)
Unfold `transl`. Rewrite using `[comp_mul, Category.comp_id, ← Category.assoc]`. Use `congr 2`. Use `ext`. Simplify using `[Over.w g]`.
-/
theorem transl_pt {T : Scheme.{0}} (t : T ⟶ S) (g : Over.mk t ⟶ G') (y : Over.mk (𝟙 S) ⟶ G') :
    g ≫ transl y = g * (Over.homMk t (Category.comp_id t) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  ext
  simp [Over.w g]

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))`.
-/
theorem pull_pt_ext {S' : Scheme.{0}} (f : S' ⟶ S) {T : Scheme.{0}} {s : T ⟶ S'}
    (a b : Over.mk s ⟶ (Over.pullback f).obj G') (h : a.left ≫ pullback.fst G'.hom f = b.left ≫ pullback.fst G'.hom f) :
    a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

end

/- English proof (translation)
Consider the cases of `j with`. Consider the case `none => exact N.datum_pt hφ s y₁ y₂ z hy.symm h₁ h₂ hz₁ hz₂`. Consider the case `some k`. Use `haveI := hφ.1`. Rewrite `hz₁`, the goal using `[Near.chart_some]`.

Take `⟨x₀, e₁, e₂, e₃⟩` from `hx k`. Establish `hxo : (x k).left ≫ G'.hom = 𝟙 S` using `Over.w (x k)`. Establish `c₁ : (y₁ ≫ N.u) ≫ G'.hom = s ≫ pullback.fst π π` using `by rw [Category.assoc, N.u_over, h₁]`. Establish `c₂ : (y₂ ≫ N.u) ≫ G'.hom = s ≫ pullback.snd π π` using `by rw [Category.assoc, N.u_over, h₂]`. Establish `d₁ : (s ≫ pullback.fst π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.fst π π`.

Simplify using `only [Category.assoc, hxo, Category.comp_id]`. Establish `d₂ : (s ≫ pullback.snd π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.snd π π`. Simplify using `only [Category.assoc, hxo, Category.comp_id]`. Set `G₁` to `(Over.pullback (pullback.fst π π)).obj G'`. Set `G₂` to `(Over.pullback (pullback.snd π π)).obj G'`.

Set `W₁ : Over.mk s ⟶ G₁` to `Over.homMk (pullback.lift _ _ c₁) (pullback.lift_snd _ _ _)`. Set `X₁ : Over.mk s ⟶ G₁` to `Over.homMk (pullback.lift _ _ d₁) (pullback.lift_snd _ _ _)`. Set `W₂ : Over.mk s ⟶ G₂` to `Over.homMk (pullback.lift _ _ c₂) (pullback.lift_snd _ _ _)`. Set `X₂ : Over.mk s ⟶ G₂` to `Over.homMk (pullback.lift _ _ d₂) (pullback.lift_snd _ _ _)`. Set `Z₁ : Over.mk s ⟶ G₁` to `Over.homMk z hz₂`.

Set `P₁` to `pushHom (isGrpPullback_pullback G' (pullback.fst π π)) (Over.mk s)`. Set `P₂` to `pushHom (isGrpPullback_pullback G' (pullback.snd π π)) (Over.mk s)`. Set `w₁ : Over.mk (s ≫ pullback.fst π π) ⟶ G'` to `Over.homMk (y₁ ≫ N.u) c₁`. Set `w₂ : Over.mk (s ≫ pullback.snd π π) ⟶ G'` to `Over.homMk (y₂ ≫ N.u) c₂`. Establish `pW₁ : P₁ W₁ = w₁` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`.

Establish `pW₂ : P₂ W₂ = w₂` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`. Establish `pX₁ : P₁ X₁ = Over.homMk (s ≫ pullback.fst π π) (Category.comp_id _) ≫ x k` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`. Establish `pX₂ : P₂ X₂ = Over.homMk (s ≫ pullback.snd π π) (Category.comp_id _) ≫ x k` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`. Establish `hZ : Z₁ = W₁ * X₁⁻¹`. Apply `pull_pt_ext` to reduce the goal to its premises.

Establish `e : P₁ Z₁ = P₁ (W₁ * X₁⁻¹)`. Rewrite using `[map_mul, map_inv, pW₁, pX₁, ← GrpObj.comp_inv, ← transl_pt]`. Conclude with `Over.OverMorphism.ext (by show z ≫ pullback.fst _ _ = (y₁ ≫ N.u) ≫ (transl (x k)⁻¹).left`. Rewrite using `[hz₁, Category.assoc])`. Conclude with `congrArg (fun q => q.left) e`.

Establish `hW : W₁ ≫ φ.hom = W₂`. Apply `pull_pt_ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Category.assoc]`. Use `(N.datum_pt hφ s y₁ y₂ _ hy.symm h₁ h₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans ?_` and prove the remaining obligations. Conclude with `(pullback.lift_fst _ _ _).symm`.

Establish `hX : X₁ ≫ φ.hom = X₂`. Apply `pull_pt_ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Category.assoc]`. Use `(N.datum_pt hφ s (s ≫ pullback.fst π π ≫ x₀) (s ≫ pullback.snd π π ≫ x₀) _ ?_ ?_ ?_ ?_ (pullback.lift_snd _ _ _)).trans ?_` and prove the remaining obligations. Simplify using `only [Category.assoc, e₁]`.

Rewrite using `[← Category.assoc (pullback.snd π π), ← pullback.condition, Category.assoc]`. Simplify using `only [Category.assoc, e₂, Category.comp_id]`. Simplify using `only [Category.assoc, e₂, Category.comp_id]`. Rewrite using `[pullback.lift_fst]`. Simplify using `only [Category.assoc, e₃]`.

Use `Eq.trans ?_ (pullback.lift_fst _ _ d₂).symm` and prove the remaining obligations. Simplify using `only [Category.assoc, e₃]`. Establish `e : P₂ (Z₁ ≫ φ.hom) = w₂ ≫ transl (x k)⁻¹`. Rewrite using `[hZ, mul_comp, GrpObj.inv_comp, hW, hX, map_mul, map_inv, pW₂, pX₂, ← GrpObj.comp_inv, ← transl_pt]`. Establish `e' : (z ≫ φ.hom.left) ≫ pullback.fst G'.hom (pullback.snd π π) = (y₂ ≫ N.u) ≫ (transl (x k)⁻¹).left` using `congrArg (fun q => q.left) e`.

Simplify `e'` using `only [Category.assoc]`.
-/
theorem Near.datum_chart {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G'))
    (hx : ∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) (φ) (hφ : N.Datum φ) (j : Option (Fin n)) (T : Scheme.{0})
    (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π)
    (hy : y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _) (h₁ : y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π)
    (h₂ : y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π) (z : T ⟶ pullback G'.hom (pullback.fst π π))
    (hz₁ : z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j) (hz₂ : z ≫ pullback.snd _ _ = s) :
    z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  cases j with
  | none => exact N.datum_pt hφ s y₁ y₂ z hy.symm h₁ h₂ hz₁ hz₂
  | some k =>
  haveI := hφ.1
  rw [Near.chart_some] at hz₁ ⊢
  obtain ⟨x₀, e₁, e₂, e₃⟩ := hx k
  have hxo : (x k).left ≫ G'.hom = 𝟙 S := Over.w (x k)
  have c₁ : (y₁ ≫ N.u) ≫ G'.hom = s ≫ pullback.fst π π := by rw [Category.assoc, N.u_over, h₁]
  have c₂ : (y₂ ≫ N.u) ≫ G'.hom = s ≫ pullback.snd π π := by rw [Category.assoc, N.u_over, h₂]
  have d₁ : (s ≫ pullback.fst π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.fst π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  have d₂ : (s ≫ pullback.snd π π ≫ (x k).left) ≫ G'.hom = s ≫ pullback.snd π π := by
    simp only [Category.assoc, hxo, Category.comp_id]
  let G₁ := (Over.pullback (pullback.fst π π)).obj G'
  let G₂ := (Over.pullback (pullback.snd π π)).obj G'
  let W₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ c₁) (pullback.lift_snd _ _ _)
  let X₁ : Over.mk s ⟶ G₁ := Over.homMk (pullback.lift _ _ d₁) (pullback.lift_snd _ _ _)
  let W₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ c₂) (pullback.lift_snd _ _ _)
  let X₂ : Over.mk s ⟶ G₂ := Over.homMk (pullback.lift _ _ d₂) (pullback.lift_snd _ _ _)
  let Z₁ : Over.mk s ⟶ G₁ := Over.homMk z hz₂
  let P₁ := pushHom (isGrpPullback_pullback G' (pullback.fst π π)) (Over.mk s)
  let P₂ := pushHom (isGrpPullback_pullback G' (pullback.snd π π)) (Over.mk s)
  let w₁ : Over.mk (s ≫ pullback.fst π π) ⟶ G' := Over.homMk (y₁ ≫ N.u) c₁
  let w₂ : Over.mk (s ≫ pullback.snd π π) ⟶ G' := Over.homMk (y₂ ≫ N.u) c₂
  have pW₁ : P₁ W₁ = w₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pW₂ : P₂ W₂ = w₂ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₁ : P₁ X₁ = Over.homMk (s ≫ pullback.fst π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have pX₂ : P₂ X₂ = Over.homMk (s ≫ pullback.snd π π) (Category.comp_id _) ≫ x k :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)

  have hZ : Z₁ = W₁ * X₁⁻¹ := by
    apply pull_pt_ext
    have e : P₁ Z₁ = P₁ (W₁ * X₁⁻¹) := by
      rw [map_mul, map_inv, pW₁, pX₁, ← GrpObj.comp_inv, ← transl_pt]
      exact Over.OverMorphism.ext (by
        show z ≫ pullback.fst _ _ = (y₁ ≫ N.u) ≫ (transl (x k)⁻¹).left
        rw [hz₁, Category.assoc])
    exact congrArg (fun q => q.left) e
  have hW : W₁ ≫ φ.hom = W₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s y₁ y₂ _ hy.symm h₁ h₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans ?_
    exact (pullback.lift_fst _ _ _).symm
  have hX : X₁ ≫ φ.hom = X₂ := by
    apply pull_pt_ext
    rw [Over.comp_left, Category.assoc]
    refine (N.datum_pt hφ s (s ≫ pullback.fst π π ≫ x₀) (s ≫ pullback.snd π π ≫ x₀) _ ?_ ?_ ?_ ?_
      (pullback.lift_snd _ _ _)).trans ?_
    · simp only [Category.assoc, e₁]
      rw [← Category.assoc (pullback.snd π π), ← pullback.condition, Category.assoc]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · simp only [Category.assoc, e₂, Category.comp_id]
    · rw [pullback.lift_fst]; simp only [Category.assoc, e₃]
    · refine Eq.trans ?_ (pullback.lift_fst _ _ d₂).symm
      simp only [Category.assoc, e₃]
  have e : P₂ (Z₁ ≫ φ.hom) = w₂ ≫ transl (x k)⁻¹ := by
    rw [hZ, mul_comp, GrpObj.inv_comp, hW, hX, map_mul, map_inv, pW₂, pX₂, ← GrpObj.comp_inv, ← transl_pt]
  have e' : (z ≫ φ.hom.left) ≫ pullback.fst G'.hom (pullback.snd π π) = (y₂ ≫ N.u) ≫ (transl (x k)⁻¹).left :=
    congrArg (fun q => q.left) e
  simpa only [Category.assoc] using e'

end GlobalTheory.Mum
