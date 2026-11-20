import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R R' _ _ σ A _ A' _ φ h`. Establish `pA : IsPullback (fst A A).left (snd A A).left A.hom A.hom` using `IsPullback.of_hasPullback _ _`. Establish `pA' : IsPullback (fst A' A').left (snd A' A').left A'.hom A'.hom` using `IsPullback.of_hasPullback _ _`. Take `⟨Φ, h₁, h₂⟩ : ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Φ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ Φ ≫ (snd A A).left = (snd A' A').left ≫ φ` from `⟨pA.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by`. Rewrite using `[Category.assoc, Category.assoc, h.1.w, ← Category.assoc, ← Category.assoc, pA'.w]),`.

Use the proof step `pA.lift_fst _ _ _, pA.lift_snd _ _ _⟩`. Establish `hP : IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ)`. Establish `q` using `pA'.paste_horiz h.1`. Rewrite `q` using `[← h₁, ← h.1.w]`. Establish `r` using `(IsPullback.of_right q h₂ pA).paste_vert h.1`.

Rewrite `r` using `[Over.w, Over.w]`. Then use the resulting hypothesis. Establish `one : ∀ T : Over (Sp R'), (toUnit T ≫ η[A']).left ≫ φ = (T.hom ≫ spMap σ) ≫ η[A].left`. Introduce `T`. Set `x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A` to `Over.homMk ((toUnit T ≫ η[A']).left ≫ φ) (by`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w]`.

Use the proof step `rfl)`. Establish `hx : x₀ * x₀ = x₀`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[h.2 T 1 1 x₀ x₀ rfl rfl, _root_.mul_one]`. Both sides reduce to the same expression.

Establish `e : x₀ = 1` using `mul_eq_left.1 hx`. Establish `e'` using `congrArg (fun q => q.left) e`. Use `e'.trans ?_` and prove the remaining obligations. Use `show (toUnit _ ≫ η[A]).left = _`. Rewrite using `[Over.comp_left, Over.toUnit_left]`.

Both sides reduce to the same expression. Set `Ψ : Over.mk ((A' ⊗ A').hom ≫ spMap σ) ⟶ A ⊗ A` to `Over.homMk Φ hP.w`. Establish `hm` using `h.2 (A' ⊗ A') (fst A' A') (snd A' A') (Ψ ≫ fst A A) (Ψ ≫ snd A A) h₁ h₂`. Rewrite `hm` using `[← MonObj.comp_mul, Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_fst_snd, Category.id_comp, Category.id_comp, Over.comp_left]`. Use `⟨Φ, hP, hm.symm, h₁.symm, h₂.symm, ?_, ?_⟩` and prove the remaining obligations.

Use `pA.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]`. Rewrite using `[Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left, lift_snd, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]`. Use `pA.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left, lift_fst, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]`.

Rewrite using `[Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]`.
-/
theorem prod_pullback_sq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  intro R R' _ _ σ A _ A' _ φ h
  have pA : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have pA' : IsPullback (fst A' A').left (snd A' A').left A'.hom A'.hom := IsPullback.of_hasPullback _ _
  obtain ⟨Φ, h₁, h₂⟩ : ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left,
      Φ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ Φ ≫ (snd A A).left = (snd A' A').left ≫ φ :=
    ⟨pA.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by
      rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc, ← Category.assoc, pA'.w]),
      pA.lift_fst _ _ _, pA.lift_snd _ _ _⟩
  have hP : IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) := by
    have q := pA'.paste_horiz h.1
    rw [← h₁, ← h.1.w] at q
    have r := (IsPullback.of_right q h₂ pA).paste_vert h.1
    rwa [Over.w, Over.w] at r
  have one : ∀ T : Over (Sp R'), (toUnit T ≫ η[A']).left ≫ φ = (T.hom ≫ spMap σ) ≫ η[A].left := by
    intro T
    let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk ((toUnit T ≫ η[A']).left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have e : x₀ = 1 := mul_eq_left.1 hx
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    show (toUnit _ ≫ η[A]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  let Ψ : Over.mk ((A' ⊗ A').hom ≫ spMap σ) ⟶ A ⊗ A := Over.homMk Φ hP.w
  have hm := h.2 (A' ⊗ A') (fst A' A') (snd A' A') (Ψ ≫ fst A A) (Ψ ≫ snd A A) h₁ h₂
  rw [← MonObj.comp_mul, Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_fst_snd, Category.id_comp, Category.id_comp,
    Over.comp_left] at hm
  refine ⟨Φ, hP, hm.symm, h₁.symm, h₂.symm, ?_, ?_⟩
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

end GlobalTheory.AbCoh
