import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

/- English proof (translation)
Use `ext`. Simplify using `only [pullTop, Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]`. Both sides reduce to the same expression.
-/
theorem pullTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    pullTop (f ≫ g) u = pullTop f (pullTop g u) := by
  ext
  simp only [pullTop, Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

section Tri

variable {S : Scheme.{0}} (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A)

def triM₁₂ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _) (lift (snd A _ ≫ fst N _) (snd A _ ≫ snd N _ ≫ snd N T))

def triM₂₃ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _ * (snd A _ ≫ fst N _ ≫ i)) (snd A _ ≫ snd N (N ⊗ T))

def triM₁₃ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _) (lift (snd A _ ≫ fst N _ * (snd A _ ≫ snd N _ ≫ fst N T)) (snd A _ ≫ snd N _ ≫ snd N T))

/- English proof (translation)
Apply the tactic sequence `apply hom_ext <;> simp [triM₁₂, triM₂₃, actMap, prMap, comp_mul]`.
-/
theorem triM₁₂_actMap_eq : triM₁₂ A N T ≫ actMap i T = triM₂₃ A N T i ≫ prMap A N T := by
  apply hom_ext <;> simp [triM₁₂, triM₂₃, actMap, prMap, comp_mul]

/- English proof (translation)
Use `IsPullback.of_isLimit (c := PullbackCone.mk _ _ (triM₁₂_actMap_eq A N T i)) (PullbackCone.IsLimit.mk (triM₁₂_actMap_eq A N T i) (fun s => lift (s.fst ≫ fst A _) (lift (s.fst ≫ snd A _ ≫ fst N T) (lift (s.snd ≫ snd A _ ≫ fst N T) (s.fst ≫ snd A _ ≫ snd N T)))) ?_ ?_ ?_)` and prove the remaining obligations. Introduce `s`. Apply `hom_ext` to reduce the goal to its premises. Simplify using `[triM₁₂]`. Apply the tactic sequence `apply hom_ext <;> simp [triM₁₂]`.

Introduce `s`. Establish `h` using `s.condition`. Establish `h₁` using `congrArg (· ≫ fst A T) h`. Establish `h₂` using `congrArg (· ≫ snd A T) h`. Simplify using `only [Category.assoc, actMap, prMap, lift_fst, lift_snd, comp_mul] at h₁ h₂`.

Apply `hom_ext` to reduce the goal to its premises. Simplify using `[triM₂₃, comp_mul, ← h₁]`. Apply `hom_ext` to reduce the goal to its premises. Simplify using `[triM₂₃]`. Simplify using `[triM₂₃, h₂]`.

Introduce `s m h₁ h₂`. Establish `e₁` using `congrArg (· ≫ fst A _) h₁`. Establish `e₂` using `congrArg (· ≫ snd A _ ≫ fst N T) h₁`. Establish `e₃` using `congrArg (· ≫ snd A _ ≫ snd N T) h₁`. Establish `e₄` using `congrArg (· ≫ snd A _ ≫ fst N T) h₂`.

Simplify using `only [triM₁₂, triM₂₃, Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e₁ e₂ e₃ e₄`. Apply `hom_ext` to reduce the goal to its premises. Simplify using `using e₁`. Apply `hom_ext` to reduce the goal to its premises. Simplify using `using e₂`.

Apply `hom_ext` to reduce the goal to its premises. Simplify using `using e₄`. Simplify using `using e₃`.
-/
theorem tri_isPullback_over : IsPullback (triM₁₂ A N T) (triM₂₃ A N T i) (actMap i T) (prMap A N T) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (triM₁₂_actMap_eq A N T i))
    (PullbackCone.IsLimit.mk (triM₁₂_actMap_eq A N T i)
      (fun s => lift (s.fst ≫ fst A _) (lift (s.fst ≫ snd A _ ≫ fst N T)
        (lift (s.snd ≫ snd A _ ≫ fst N T) (s.fst ≫ snd A _ ≫ snd N T)))) ?_ ?_ ?_)
  · intro s
    apply hom_ext
    · simp [triM₁₂]
    · apply hom_ext <;> simp [triM₁₂]
  · intro s
    have h := s.condition
    have h₁ := congrArg (· ≫ fst A T) h
    have h₂ := congrArg (· ≫ snd A T) h
    simp only [Category.assoc, actMap, prMap, lift_fst, lift_snd, comp_mul] at h₁ h₂
    apply hom_ext
    · simp [triM₂₃, comp_mul, ← h₁]
    · apply hom_ext
      · simp [triM₂₃]
      · simp [triM₂₃, h₂]
  · intro s m h₁ h₂
    have e₁ := congrArg (· ≫ fst A _) h₁
    have e₂ := congrArg (· ≫ snd A _ ≫ fst N T) h₁
    have e₃ := congrArg (· ≫ snd A _ ≫ snd N T) h₁
    have e₄ := congrArg (· ≫ snd A _ ≫ fst N T) h₂
    simp only [triM₁₂, triM₂₃, Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e₁ e₂ e₃ e₄
    apply hom_ext
    · simpa using e₁
    · apply hom_ext
      · simpa using e₂
      · apply hom_ext
        · simpa using e₄
        · simpa using e₃

/- English proof (translation)
Apply the tactic sequence `apply hom_ext <;> simp [triM₁₃, triM₁₂, prMap]`.
-/
theorem triM₁₃_prMap : triM₁₃ A N T ≫ prMap A N T = triM₁₂ A N T ≫ prMap A N T := by
  apply hom_ext <;> simp [triM₁₃, triM₁₂, prMap]

/- English proof (translation)
Apply `hom_ext` to reduce the goal to its premises. Simplify using `only [triM₁₃, triM₂₃, actMap, comp_lift, lift_fst, lift_fst_assoc, lift_snd_assoc, comp_mul, mul_comp, Category.assoc]`. Conclude with `(mul_assoc _ _ _).symm`. Simplify using `[triM₁₃, triM₂₃, actMap]`.
-/
theorem triM₁₃_actMap [IsMonHom i] : triM₁₃ A N T ≫ actMap i T = triM₂₃ A N T i ≫ actMap i T := by
  apply hom_ext
  · simp only [triM₁₃, triM₂₃, actMap, comp_lift, lift_fst, lift_fst_assoc, lift_snd_assoc, comp_mul, mul_comp,
      Category.assoc]
    exact (mul_assoc _ _ _).symm
  · simp [triM₁₃, triM₂₃, actMap]

/- English proof (translation)
Apply the tactic sequence `apply hom_ext <;> simp [triM₁₃, comp_mul]`.
-/
theorem triM₁₃_snd : triM₁₃ A N T ≫ snd A (N ⊗ T) =
    snd A (N ⊗ (N ⊗ T)) ≫ lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) := by
  apply hom_ext <;> simp [triM₁₃, comp_mul]

/- English proof (translation)
Apply the tactic sequence `apply hom_ext <;> simp [triM₁₂]`.
-/
theorem triM₁₂_snd : triM₁₂ A N T ≫ snd A (N ⊗ T) =
    snd A (N ⊗ (N ⊗ T)) ≫ lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) := by
  apply hom_ext <;> simp [triM₁₂]

/- English proof (translation)
Simplify using `[triM₂₃]`.
-/
theorem triM₂₃_snd : triM₂₃ A N T i ≫ snd A (N ⊗ T) = snd A (N ⊗ (N ⊗ T)) ≫ snd N (N ⊗ T) := by
  simp [triM₂₃]

end Tri

/- English proof (translation)
Introduce `S A N T _ _ i χ hi hχ`. Use `haveI := hi`. Use `⟨(A ⊗ (N ⊗ (N ⊗ T))).left, (triM₁₂ A N T).left, (triM₂₃ A N T i).left, (triM₁₃ A N T).left, (tri_isPullback_over A N T i).map (Over.forget S), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ← Over.comp_left, triM₁₃_prMap]`. Rewrite using `[← Over.comp_left, ← Over.comp_left, triM₁₃_actMap]`.

Rewrite using `[← pullTop_comp_apply, ← pullTop_comp_apply, ← pullTop_comp_apply, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, triM₁₃_snd, triM₁₂_snd, triM₂₃_snd, Over.comp_left, Over.comp_left, Over.comp_left, pullTop_comp_apply, pullTop_comp_apply, pullTop_comp_apply]`. Unfold `IsCharacter at hχ`. Rewrite using `[hχ, map_mul]`.
-/
theorem triOverlap : ∀ (S : Scheme.{0}) (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A) (χ : Γ((N ⊗ T).left, ⊤)ˣ),
    IsMonHom i → IsCharacter χ → ∃ (W : Scheme.{0}) (m₁₂ m₂₃ m₁₃ : W ⟶ (A ⊗ (N ⊗ T)).left),
      IsPullback m₁₂ m₂₃ (actMap i T).left (prMap A N T).left ∧
      m₁₃ ≫ (prMap A N T).left = m₁₂ ≫ (prMap A N T).left ∧
      m₁₃ ≫ (actMap i T).left = m₂₃ ≫ (actMap i T).left ∧
      pullTop m₁₃ (pullTop (snd A (N ⊗ T)).left χ) =
        pullTop m₁₂ (pullTop (snd A (N ⊗ T)).left χ) * pullTop m₂₃ (pullTop (snd A (N ⊗ T)).left χ) := by
  intro S A N T _ _ i χ hi hχ
  haveI := hi
  refine ⟨(A ⊗ (N ⊗ (N ⊗ T))).left, (triM₁₂ A N T).left, (triM₂₃ A N T i).left, (triM₁₃ A N T).left,
    (tri_isPullback_over A N T i).map (Over.forget S), ?_, ?_, ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, triM₁₃_prMap]
  · rw [← Over.comp_left, ← Over.comp_left, triM₁₃_actMap]
  · rw [← pullTop_comp_apply, ← pullTop_comp_apply, ← pullTop_comp_apply, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
      triM₁₃_snd, triM₁₂_snd, triM₂₃_snd, Over.comp_left, Over.comp_left, Over.comp_left, pullTop_comp_apply, pullTop_comp_apply,
      pullTop_comp_apply]
    unfold IsCharacter at hχ
    rw [hχ, map_mul]

end GlobalTheory.CharKer
