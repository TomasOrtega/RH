import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate

namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

/- English proof (translation)
Establish `hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F'` using `AlgebraicClosure F) E u) := (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)`. Take `⟨c, hc⟩` from `exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'`. Conclude with `exists_algebraMap_eq_of_bcEmb E hc.symm`.
-/
theorem exists_algebraMap_eq_of_isAlgebraic_ff (E : WeierstrassCurve F) [E.IsElliptic]
    {u : E.toAffine.FunctionField} (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = u := by
  classical
  have hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F' := AlgebraicClosure F) E u) :=
    (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'
  exact exists_algebraMap_eq_of_bcEmb E hc.symm

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

/- English proof (translation)
Break down `Q with _ | ⟨x, y, h⟩` into its components or cases. Conclude with `absurd rfl h0`. Assume the negation of the conclusion as `hx`. Establish `hx' : IsAlgebraic F x` using `not_not.mp hx`. Take `⟨a, rfl⟩` from `exists_algebraMap_eq_of_isAlgebraic_ff E hx'`.

Establish `hy' : IsAlgebraic F y`. Use `isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))` as an intermediate fact. Conclude with `mem_algebraicClosure_iff.1 this`. Take `⟨b, rfl⟩` from `exists_algebraMap_eq_of_isAlgebraic_ff E hy'`. Establish `hc : (E'.baseChange F).toAffine.Nonsingular a b` using `(E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField) (algebraMap F _).injective a b).mp h`.

Establish `hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) = Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc)`. Rewrite using `[Point.map_some, Point.some.injEq]`. Conclude with `⟨rfl, rfl⟩`. Establish `key` using `(respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E) (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)`. Establish `hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E), Point.map σ (Point.some _ _ h) = Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc)` using `fun σ => by`.

Rewrite using `[hQc, Point.map_map]`. Establish `e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E)` using `AlgHom.ext fun z => by`. Rewrite using `[AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]`. Rewrite using `[e]`. Rewrite `key` using `[hconst, hconst, hconst, left_eq_add]`.

Use `Point.map_injective (W' := E') (Algebra.ofId F (univField E)) (key.trans (map_zero _).symm)` as an intermediate fact. Conclude with `Point.some_ne_zero hc this`.
-/
theorem isGenPt_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsGenPt E' Q := by
  classical
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · by_contra hx
    have hx' : IsAlgebraic F x := not_not.mp hx
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hx'
    have hy' : IsAlgebraic F y := by
      have := isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))
      exact mem_algebraicClosure_iff.1 this
    obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hy'
    have hc : (E'.baseChange F).toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField)
        (algebraMap F _).injective a b).mp h
    have hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) =
        Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc) := by
      rw [Point.map_some, Point.some.injEq]; exact ⟨rfl, rfl⟩
    have key := (respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E)
      (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)
    have hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E),
        Point.map σ (Point.some _ _ h) =
          Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc) := fun σ => by
      rw [hQc, Point.map_map]
      have e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E) :=
        AlgHom.ext fun z => by
          rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]
      rw [e]
    rw [hconst, hconst, hconst, left_eq_add] at key
    have := Point.map_injective (W' := E') (Algebra.ofId F (univField E))
      (key.trans (map_zero _).symm)
    exact Point.some_ne_zero hc this

/- English proof (translation)
The claim follows from `(isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩`.
-/
theorem isIsogeny_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsIsogeny E E' Q :=
  (isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩

end

end GroundTheory.Global
