import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIffStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingCofaceMapComplexPreadditiveYonedaDApp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Set `K : SimplicialObject (Shv R)` to `((SimplicialObject.whiskering _ _).obj (free R)).obj ((X ⋙ Ψ).leftOp)`. Set `B : Shv R` to `(free R).obj (Ψ.obj U).unop`. Set `f : K ⟶ (SimplicialObject.const (Shv R)).obj B` to `((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a) ≫ (Functor.constComp _ _ _).hom`. Use `haveI h1 : QuasiIso ((chainsN R).map (lev Ψ a)) := (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hq`. Establish `hq' : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f)`.

Establish `e : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f = (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a)) ≫ (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp _ _ _).hom` using `Functor.map_comp _ _ _`. Rewrite using `[e]`. Use `haveI : IsIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) := Functor.map_isIso _ _`. Use `haveI h2 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a))) := h1`. Use `haveI h3 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) := quasiIso_of_isIso _`.

Conclude with `quasiIso_comp (hφ := h2) (hφ' := h3) _ _`. Take `⟨hepi, ⟨w, hex⟩, hn⟩` from `(GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact _ K B f).1 hq'`. Establish `hepi' : Epi ((free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop)`. Establish `e : f.app (op (SimplexCategory.mk 0)) = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop` using `Category.comp_id _`. Rewrite using `[← e]`.

Conclude with `hepi`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Express the relevant statement in the definitionally equal form `(free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ x = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ y at hxy`. Conclude with `(cancel_epi _).1 hxy`.

Introduce `y hy`. Express the relevant statement in the definitionally equal form `(free R).map (Ψ.map (X.δ (n := 0) 0)).unop ≫ y = (free R).map (Ψ.map (X.δ (n := 0) 1)).unop ≫ y at hy`. Set `y' : K.obj (op (SimplexCategory.mk 0)) ⟶ J` to `y`. Establish `hy' : (K.δ (n` using `0) 0 - K.δ (n := 0) 1) ≫ y' = 0 := by`. Use `(Preadditive.sub_comp _ _ _).trans (sub_eq_zero.2 ?_)` and prove the remaining obligations.

Conclude with `hy`. Use `⟨hex.descToInjective (J := J) y' hy', ?_⟩` and prove the remaining obligations. Conclude with `hex.comp_descToInjective (J := J) y' hy'`. Introduce `n`. Conclude with `GlobalTheory.alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ K J n (hn n)`.
-/
theorem wExact_preadditiveYoneda_of_injective (R : Type) [CommRing R] (T : Type 1) [Category.{0} T]
    (Ψ : T ⥤ PShᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (J : Shv R) (hJ : Injective J) (hq : QuasiIso ((chains R).map (lev Ψ a))) :
    WExact (Ψ ⋙ (free R).op ⋙ preadditiveYoneda.obj J) a := by
  let K : SimplicialObject (Shv R) := ((SimplicialObject.whiskering _ _).obj (free R)).obj ((X ⋙ Ψ).leftOp)
  let B : Shv R := (free R).obj (Ψ.obj U).unop
  let f : K ⟶ (SimplicialObject.const (Shv R)).obj B :=
    ((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a) ≫ (Functor.constComp _ _ _).hom
  haveI h1 : QuasiIso ((chainsN R).map (lev Ψ a)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hq
  have hq' : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f) := by
    have e : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f =
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a)) ≫
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp _ _ _).hom :=
      Functor.map_comp _ _ _
    rw [e]
    haveI : IsIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      Functor.map_isIso _ _
    haveI h2 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a))) := h1
    haveI h3 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      quasiIso_of_isIso _
    exact quasiIso_comp (hφ := h2) (hφ' := h3) _ _
  obtain ⟨hepi, ⟨w, hex⟩, hn⟩ := (GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact _ K B f).1 hq'
  have hepi' : Epi ((free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop) := by
    have e : f.app (op (SimplexCategory.mk 0)) = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop :=
      Category.comp_id _
    rw [← e]; exact hepi
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    change (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ x =
      (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ y at hxy
    exact (cancel_epi _).1 hxy
  · intro y hy
    change (free R).map (Ψ.map (X.δ (n := 0) 0)).unop ≫ y = (free R).map (Ψ.map (X.δ (n := 0) 1)).unop ≫ y at hy
    let y' : K.obj (op (SimplexCategory.mk 0)) ⟶ J := y
    have hy' : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ y' = 0 := by
      refine (Preadditive.sub_comp _ _ _).trans (sub_eq_zero.2 ?_)
      exact hy
    refine ⟨hex.descToInjective (J := J) y' hy', ?_⟩
    exact hex.comp_descToInjective (J := J) y' hy'
  · intro n
    exact GlobalTheory.alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ K J n (hn n)

end GlobalTheory.EtC
