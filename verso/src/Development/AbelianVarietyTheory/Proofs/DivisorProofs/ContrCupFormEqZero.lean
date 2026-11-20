import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProductStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

/- English proof (translation)
Introduce `R _ A B _ _ m₁ m₂ v hv α b κ hκ D _ _ D' _ _ φ x`. Take `⟨s, i, s', i', a, b', τ, hs, hi, hs', hi', ha, hb, hτ⟩` from `(GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product R A B v hv).1 D D' φ x`. Rewrite using `[hκ D D' φ x s i s' i' a b' τ hs hi hs' hi' ha hb hτ]`. Establish `ha0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ a = 0` using `α.2 (m₁.functor.map a) rfl rfl`. Establish `hb0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ b' = 0` using `α.2 (m₁.functor.map b') rfl rfl`.

Set `e : m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x))` to `{ φ := { toRingHom := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D), commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r } φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) comm := fun _ ↦ rfl dp := isDPMorphism_of_eq_bot _ rfl _ _ pt := by`. Establish `h1 : pt0 B x ≫ fst A B = x` using `lift_fst _ _`. Establish `h2 : ptV v x ≫ fst A B = spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x` using `lift_fst _ _`. Express the relevant statement in the definitionally equal form `spMap _ ≫ (pt0 B x).left ≫ (fst A B).left = (ptV v x).left ≫ (fst A B).left`. Rewrite using `[← Over.comp_left, h1, ← Over.comp_left, h2, Over.comp_left]`.

Use `rfl }`. Establish `he0 : α.1.1 _ _ e = 0` using `α.2 e rfl rfl`. Establish `hes : e ≫ m₁.functor.map i = m₁.functor.map s` using `Thick.hom_ext fun c ↦ by`. Express the relevant statement in the definitionally equal form `i.φ (TrivSqZeroExt.inl c) = s.φ c`. Rewrite using `[hi]`.

Conclude with `(hs c).symm`. Establish `hsi : (m₁.coef.pullbackOneCocycle α.1).1 _ _ s = (m₁.coef.pullbackOneCocycle α.1).1 _ _ i`. Express the relevant statement in the definitionally equal form `α.1.1 _ _ (m₁.functor.map s) = α.1.1 _ _ (m₁.functor.map i)`. Rewrite using `[← hes]`. Establish `h` using `GlobalTheory.Cris.ev_comp α.1 e (m₁.functor.map i)`.

Simplify using `only [GlobalTheory.Cris.ev] at h`. Rewrite using `[h, he0, map_zero, zero_add]`. Simplify using `only [cupZ_apply]`. Rewrite using `[ha0, hb0, hsi]`. Simplify using the standard rewrite rules.
-/
theorem contr_cup_form_eq_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (v : epsR R ⟶ B), IsTangent v → ∀ (α : Form (A.hom ≫ 𝟙 _)) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (κ : Fn1 A), IsContr (cupZ _ (m₁.coef.pullbackOneCocycle α.1) (m₂.coef.pullbackOneCocycle b)).1 v κ → ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), κ D D' φ x = 0 := by
  intro R _ A B _ _ m₁ m₂ v hv α b κ hκ D _ _ D' _ _ φ x
  obtain ⟨s, i, s', i', a, b', τ, hs, hi, hs', hi', ha, hb, hτ⟩ := (GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product R A B v hv).1 D D' φ x
  rw [hκ D D' φ x s i s' i' a b' τ hs hi hs' hi' ha hb hτ]
  have ha0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ a = 0 := α.2 (m₁.functor.map a) rfl rfl
  have hb0 : (m₁.coef.pullbackOneCocycle α.1).1 _ _ b' = 0 := α.2 (m₁.functor.map b') rfl rfl
  let e : m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x)) :=
    { φ := { toRingHom := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D),
             commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r }
      φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_of_eq_bot _ rfl _ _
      pt := by
        have h1 : pt0 B x ≫ fst A B = x := lift_fst _ _
        have h2 : ptV v x ≫ fst A B = spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x := lift_fst _ _
        change spMap _ ≫ (pt0 B x).left ≫ (fst A B).left = (ptV v x).left ≫ (fst A B).left
        rw [← Over.comp_left, h1, ← Over.comp_left, h2, Over.comp_left]
        rfl }
  have he0 : α.1.1 _ _ e = 0 := α.2 e rfl rfl
  have hes : e ≫ m₁.functor.map i = m₁.functor.map s := Thick.hom_ext fun c ↦ by
    change i.φ (TrivSqZeroExt.inl c) = s.φ c
    rw [hi]
    exact (hs c).symm
  have hsi : (m₁.coef.pullbackOneCocycle α.1).1 _ _ s = (m₁.coef.pullbackOneCocycle α.1).1 _ _ i := by
    change α.1.1 _ _ (m₁.functor.map s) = α.1.1 _ _ (m₁.functor.map i)
    rw [← hes]
    have h := GlobalTheory.Cris.ev_comp α.1 e (m₁.functor.map i)
    simp only [GlobalTheory.Cris.ev] at h
    rw [h, he0, map_zero, zero_add]
  simp only [cupZ_apply]
  rw [ha0, hb0, hsi]
  simp

end GlobalTheory.PtExt
