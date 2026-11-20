import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

/- English proof (translation)
Introduce `S A B _ _ _ _ u v hA hB hu hv t ht`. Use `hA.proper` as an intermediate fact. Establish `hε : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S` using `Over.w η[A]`. Take `⟨V, htV, hV⟩` from `GlobalTheory.local_rigidity A.left S B.left A.hom (η[A] : 𝟙_ (Over S) ⟶ A).left (u * v⁻¹).left hε inferInstance (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns A hA) t _ ht`. Use `⟨V, htV, ?_⟩` and prove the remaining obligations.

Establish `h1 : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ (u * v⁻¹) = η[B]`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Set `i : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A` to `Over.homMk (A.hom ⁻¹ᵁ V).ι rfl`. Establish `h2 : i ≫ (u * v⁻¹) = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[Over.comp_left, Hom.one_def, Over.comp_left]`. Express the relevant statement in the definitionally equal form `(A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = _`. Rewrite using `[hV, ← Over.comp_left, h1]`. Establish `e : (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom))).left = (A.hom ⁻¹ᵁ V).ι ≫ A.hom` using `by simpa using Over.w (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom)))`. Rewrite using `[e, Category.assoc]`.

Establish `h3 : i ≫ u = i ≫ v`. Use `congrArg (· * (i ≫ v)) h2` as an intermediate fact. Simplify `this` using `[MonObj.comp_mul, GrpObj.comp_inv]`. Conclude with `congrArg (·.left) h3`.
-/
theorem eq_near_fibre_of_quot_contracts : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t : S, (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left := by
  intro S A B _ _ _ _ u v hA hB hu hv t ht
  have := hA.proper
  have hε : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨V, htV, hV⟩ := GlobalTheory.local_rigidity A.left S B.left A.hom (η[A] : 𝟙_ (Over S) ⟶ A).left
    (u * v⁻¹).left hε inferInstance
    (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns A hA) t _ ht
  refine ⟨V, htV, ?_⟩
  have h1 : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ (u * v⁻¹) = η[B] := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel, Hom.one_def,
      toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let i : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
  have h2 : i ≫ (u * v⁻¹) = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    change (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = _
    rw [hV, ← Over.comp_left, h1]
    have e : (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom))).left = (A.hom ⁻¹ᵁ V).ι ≫ A.hom :=
      by simpa using Over.w (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom)))
    rw [e, Category.assoc]
  have h3 : i ≫ u = i ≫ v := by
    have := congrArg (· * (i ≫ v)) h2
    simpa [MonObj.comp_mul, GrpObj.comp_inv] using this
  exact congrArg (·.left) h3

end GlobalTheory.EndLoc
