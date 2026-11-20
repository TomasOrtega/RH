import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAcyclic
open CategoryTheory Limits AlgebraicGeometry Opposite Abelian Simplicial GlobalTheory.Et
universe v u

namespace GlobalTheory

/- English proof (translation)
Establish `hd : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I) m`. Conclude with `CochainComplex.of_d (fun n => (X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋n⦌) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I)) m`. Rewrite using `[hd]`. Set `φ : (((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m⦌) ⟶ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌)) →+ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌)` to `AddMonoidHom.mk' (fun f => f x) (fun f g => rfl)`. Express the relevant statement in the definitionally equal form `φ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ m) = _`.

Establish `h2 : (AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) = ∑ i : Fin (m+2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i ≫ (show X _⦋m⦌ ⟶ I from x))`. Rewrite using `[AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]`. Conclude with `Finset.sum_congr rfl fun i _ => Preadditive.zsmul_comp _ _ _`. Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Simplify using `only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum, map_zsmul]`.

Both sides reduce to the same expression.
-/
theorem alternatingCofaceMapComplex_preadditiveYoneda_d_apply {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) (m : ℕ)
  (x : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).X m) :
  ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1) x
   = (show X _⦋m+1⦌ ⟶ I from AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) := by
  have hd : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1)
      = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I) m := by
    exact CochainComplex.of_d (fun n => (X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋n⦌)
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I)) m
  rw [hd]
  let φ : (((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m⦌) ⟶ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌)) →+ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌) :=
    AddMonoidHom.mk' (fun f => f x) (fun f g => rfl)
  change φ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ m) = _
  have h2 : (AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) =
      ∑ i : Fin (m+2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i ≫ (show X _⦋m⦌ ⟶ I from x)) := by
    rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun i _ => Preadditive.zsmul_comp _ _ _
  refine Eq.trans ?_ h2.symm
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum, map_zsmul]
  rfl

/- English proof (translation)
Introduce `C _ _ X I _ n h`. Rewrite `h` using `[HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]`. Rewrite using `[HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp), ShortComplex.ab_exact_iff]`. Introduce `x hx`. Set `S` to `((AlgebraicTopology.alternatingFaceMapComplex C).obj X).sc' (n+2) (n+1) n`.

Establish `hS1 : S.f = AlgebraicTopology.AlternatingFaceMapComplex.objD X (n+1)` using `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X (n+1)`. Establish `hS2 : S.g = AlgebraicTopology.AlternatingFaceMapComplex.objD X n` using `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X n`. Set `f : S.X₂ ⟶ I` to `x`. Establish `hf : S.f ≫ f = 0`. Establish `h1` using `alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I (n+1) x`.

Rewrite using `[hS1]`. Conclude with `h1.symm.trans hx`. Establish `hm : Mono (cokernel.desc S.f S.g S.zero)` using `h.mono_cokernelDesc`. Set `g : S.X₃ ⟶ I` to `@Injective.factorThru _ _ _ _ _ _ (cokernel.desc S.f f hf) (cokernel.desc S.f S.g S.zero) hm`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d n (n+1) g = x`. Use `(alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I n g).trans ?_` and prove the remaining obligations. Rewrite using `[← hS2]`. Express the relevant statement in the definitionally equal form `S.g ≫ g = f`. Establish `e2 : cokernel.desc S.f S.g S.zero ≫ g = cokernel.desc S.f f hf` using `@Injective.comp_factorThru _ _ _ _ _ _ _ _ hm`.

Rewrite using `[← cokernel.π_desc S.f S.g S.zero, Category.assoc, e2, cokernel.π_desc]`.
-/
theorem alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ : ∀ {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) [Injective I] (n : ℕ), ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).ExactAt (n + 1) → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).ExactAt (n + 1) := by
  intro C _ _ X I _ n h
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x hx
  let S := ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).sc' (n+2) (n+1) n
  have hS1 : S.f = AlgebraicTopology.AlternatingFaceMapComplex.objD X (n+1) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X (n+1)
  have hS2 : S.g = AlgebraicTopology.AlternatingFaceMapComplex.objD X n :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X n
  let f : S.X₂ ⟶ I := x
  have hf : S.f ≫ f = 0 := by
    have h1 := alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I (n+1) x
    rw [hS1]
    exact h1.symm.trans hx
  have hm : Mono (cokernel.desc S.f S.g S.zero) := h.mono_cokernelDesc
  let g : S.X₃ ⟶ I := @Injective.factorThru _ _ _ _ _ _ (cokernel.desc S.f f hf) (cokernel.desc S.f S.g S.zero) hm
  refine ⟨g, ?_⟩
  change ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d n (n+1) g = x
  refine (alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I n g).trans ?_
  rw [← hS2]
  change S.g ≫ g = f
  have e2 : cokernel.desc S.f S.g S.zero ≫ g = cokernel.desc S.f f hf :=
    @Injective.comp_factorThru _ _ _ _ _ _ _ _ hm
  rw [← cokernel.π_desc S.f S.g S.zero, Category.assoc, e2, cokernel.π_desc]

end GlobalTheory
