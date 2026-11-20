import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogeny

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

section Generic

variable [W.IsElliptic]

omit [W.IsElliptic] in

/- English proof (translation)
Use `haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _`. Establish `h₁ : (curveK (W.baseChange K).toAffine.FunctionField (gaussCurve W V)).Nonsingular (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y)` using `by show ((gaussCurve W V).map (algebraMap _ _)).toAffine.Nonsingular _ _`. Rewrite using `[gaussCurve_map_functionField]`. Conclude with `h`. Establish `e₁ : pointCongr (gaussCurve_map_functionField K W V).symm (Point.some _ _ h) = Point.some _ _ h₁` using `pointCongr_some _ h`.

Establish `n₁` using `nonsingular_residue_of_isElliptic (W.baseChange K).toAffine.FunctionField (gaussCurve W V) h₁.1`. Take `⟨h₂, e₂⟩` from `pointMapRing_some (gaussResidue W) ((gaussCurve W V).map (residue _)) n₁`. Use `⟨by rw [← gaussCurve_map_residue W V]; exact h₂, ?_⟩` and prove the remaining obligations. Simplify using `only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]`. Rewrite using `[e₁, reducePoint_some_integral _ _ h₁ n₁]`.

Use `erw [e₂]`. Rewrite using `[pointCongr_some]`.
-/
theorem reduceFF_some (V : WeierstrassCurve 𝒪) [V.IsElliptic] {x y : gaussRing W}
    (h : ((V.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y)) :
    ∃ h', reduceFF K W V (Point.some _ _ h) =
      Point.some (gaussResidue W (residue _ x)) (gaussResidue W (residue _ y)) h' := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have h₁ : (curveK (W.baseChange K).toAffine.FunctionField (gaussCurve W V)).Nonsingular
      (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y) := by
    show ((gaussCurve W V).map (algebraMap _ _)).toAffine.Nonsingular _ _
    rw [gaussCurve_map_functionField]; exact h
  have e₁ : pointCongr (gaussCurve_map_functionField K W V).symm (Point.some _ _ h) =
      Point.some _ _ h₁ := pointCongr_some _ h
  have n₁ := nonsingular_residue_of_isElliptic (W.baseChange K).toAffine.FunctionField
    (gaussCurve W V) h₁.1
  obtain ⟨h₂, e₂⟩ := pointMapRing_some (gaussResidue W) ((gaussCurve W V).map (residue _)) n₁
  refine ⟨by rw [← gaussCurve_map_residue W V]; exact h₂, ?_⟩
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [e₁, reducePoint_some_integral _ _ h₁ n₁]
  erw [e₂]
  rw [pointCongr_some]

/- English proof (translation)
Use `haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _`. Establish `hx` using `algebraMap_gaussX W K`. Establish `hy` using `algebraMap_gaussY W K`. Choose the witnesses or unpack the hypotheses as in `⟨h₁, e₁⟩ : ∃ h₁ : (curveK (W.baseChange K).toAffine.FunctionField (gaussCurve W W)).Nonsingular (algebraMap (gaussRing W) _ (gaussX W)) (algebraMap (gaussRing W) _ (gaussY W)), pointCongr (gaussCurve_map_functionField K W W).symm (GroundTheory.Arith.Abelian.genericPoint (W.baseCh …`. Rewrite using `[GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]`.

Conclude with `exists_some_eq _ hx.symm hy.symm`. Establish `n₁` using `nonsingular_residue_of_isElliptic (W.baseChange K).toAffine.FunctionField (gaussCurve W W) h₁.1`. Take `⟨h₂, e₂⟩` from `pointMapRing_some (gaussResidue W) ((gaussCurve W W).map (residue _)) n₁`. Simplify using `only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]`. Rewrite using `[e₁, reducePoint_some_integral _ _ h₁ n₁]`.

Use `erw [e₂]`. Rewrite using `[pointCongr_some, GroundTheory.Arith.Abelian.genericPoint, Point.some.injEq, gaussResidue_gaussX, gaussResidue_gaussY]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem reduceFF_genericPoint :
    reduceFF K W W (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) =
      GroundTheory.Arith.Abelian.genericPoint (W.map (residue 𝒪)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hx := algebraMap_gaussX W K
  have hy := algebraMap_gaussY W K
  obtain ⟨h₁, e₁⟩ : ∃ h₁ : (curveK (W.baseChange K).toAffine.FunctionField
      (gaussCurve W W)).Nonsingular (algebraMap (gaussRing W) _ (gaussX W))
        (algebraMap (gaussRing W) _ (gaussY W)),
      pointCongr (gaussCurve_map_functionField K W W).symm
        (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) = Point.some _ _ h₁ := by
    rw [GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
    exact exists_some_eq _ hx.symm hy.symm
  have n₁ := nonsingular_residue_of_isElliptic (W.baseChange K).toAffine.FunctionField
    (gaussCurve W W) h₁.1
  obtain ⟨h₂, e₂⟩ := pointMapRing_some (gaussResidue W) ((gaussCurve W W).map (residue _)) n₁
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [e₁, reducePoint_some_integral _ _ h₁ n₁]
  erw [e₂]
  rw [pointCongr_some, GroundTheory.Arith.Abelian.genericPoint, Point.some.injEq, gaussResidue_gaussX,
    gaussResidue_gaussY]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Rewrite using `[map_zsmul, reduceFF_genericPoint]`.
-/
theorem reduceFF_zsmul_genericPoint (n : ℤ) :
    reduceFF K W W (n • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K)) =
      n • GroundTheory.Arith.Abelian.genericPoint (W.map (residue 𝒪)) := by
  rw [map_zsmul, reduceFF_genericPoint]

end Generic

section Coordinates

variable {F : Type*} [Field F] [DecidableEq F]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem xOf_pointCongr {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    xOf V₂ (pointCongr h P) = xOf V₁ P := by
  subst h; rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem yOf_pointCongr {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    yOf V₂ (pointCongr h P) = yOf V₁ P := by
  subst h; rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem pointCongr_eq_zero_iff {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂)
    (P : V₁.toAffine.Point) : pointCongr h P = 0 ↔ P = 0 := by
  subst h; rfl

variable {L : Type*} [Field L] [DecidableEq L]

/- English proof (translation)
Break down `P with _ | ⟨x, y, h⟩` into its components or cases. Use `show (0 : L) = f 0`. Rewrite using `[map_zero]`. Take `⟨h', e⟩` from `pointMapRing_some f V h`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem xOf_pointMapRing (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    xOf (V.map f) (pointMapRing f V P) = f (xOf V P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : L) = f 0; rw [map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]; rfl

/- English proof (translation)
Break down `P with _ | ⟨x, y, h⟩` into its components or cases. Use `show (0 : L) = f 0`. Rewrite using `[map_zero]`. Take `⟨h', e⟩` from `pointMapRing_some f V h`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem yOf_pointMapRing (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    yOf (V.map f) (pointMapRing f V P) = f (yOf V P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : L) = f 0; rw [map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]; rfl

/- English proof (translation)
Break down `P with _ | ⟨x, y, h⟩` into its components or cases. Conclude with `⟨fun _ => rfl, fun _ => rfl⟩`. Take `⟨h', e⟩` from `pointMapRing_some f V h`. Rewrite using `[e]`. Conclude with `⟨fun h0 => absurd h0 (Point.some_ne_zero _), fun h0 => absurd h0 (Point.some_ne_zero _)⟩`.
-/
theorem pointMapRing_eq_zero_iff (f : F →+* L) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨h', e⟩ := pointMapRing_some f V h
    rw [e]
    exact ⟨fun h0 => absurd h0 (Point.some_ne_zero _), fun h0 => absurd h0 (Point.some_ne_zero _)⟩

/- English proof (translation)
Apply the tactic sequence `rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩`. Both sides reduce to the same expression. Conclude with `absurd (h0.1 rfl) (Point.some_ne_zero _)`. Conclude with `absurd (h0.2 rfl) (Point.some_ne_zero _)`. Rewrite using `[Point.some.injEq]`.

Conclude with `⟨hx, hy⟩`.
-/
theorem point_ext_xy {V : WeierstrassCurve F} {P Q : V.toAffine.Point} (h0 : P = 0 ↔ Q = 0)
    (hx : xOf V P = xOf V Q) (hy : yOf V P = yOf V Q) : P = Q := by
  rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩
  · rfl
  · exact absurd (h0.1 rfl) (Point.some_ne_zero _)
  · exact absurd (h0.2 rfl) (Point.some_ne_zero _)
  · rw [Point.some.injEq]; exact ⟨hx, hy⟩

end Coordinates

section Composition

/- English proof (translation)
Substitute `h₁` using the available equality. Substitute `h₂` using the available equality. Substitute `h₃` using the available equality. Both sides reduce to the same expression.
-/
theorem pointCongr₃_eq {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ V₄ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (h₃ : V₃ = V₄)
    (h₄ : V₁ = V₄) (P : V₁.toAffine.Point) :
    pointCongr h₃ (pointCongr h₂ (pointCongr h₁ P)) = pointCongr h₄ P := by
  subst h₁; subst h₂; subst h₃; rfl

omit [IsFractionRing 𝒪 K] in
/- English proof (translation)
Apply `ringHom_ext_functionField` to reduce the goal to its premises. Introduce `c`. Rewrite using `[fieldEvalRed_algebraMap, fieldEvalRed_algebraMap]`. Rewrite using `[fieldEvalRed_genX, fieldEvalRed_genX, ex]`. Rewrite using `[fieldEvalRed_genY, fieldEvalRed_genY, ey]`.
-/
theorem fieldEvalRed_congr {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    (j : 𝒪 →+* Λ) [IsLocalHom j] {x₁ y₁ x₂ y₂ : Λ} (hxy₁ : (W.map j).toAffine.Equation x₁ y₁)
    (hxy₂ : (W.map j).toAffine.Equation x₂ y₂)
    (hx₁ : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x₁)))
    (hx₂ : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x₂)))
    (ex : residue Λ x₁ = residue Λ x₂) (ey : residue Λ y₁ = residue Λ y₂) :
    fieldEvalRed W j hxy₁ hx₁ = fieldEvalRed W j hxy₂ hx₂ := by
  apply ringHom_ext_functionField
  · intro c; rw [fieldEvalRed_algebraMap, fieldEvalRed_algebraMap]
  · rw [fieldEvalRed_genX, fieldEvalRed_genX, ex]
  · rw [fieldEvalRed_genY, fieldEvalRed_genY, ey]

omit [IsFractionRing 𝒪 K] in
/- English proof (translation)
Use `RingHom.ext fun c => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `residue_surjective c`. Rewrite using `[RingHom.comp_apply, ResidueField.map_residue, gaussResidue_residue_algebraMap]`.
-/
theorem gaussResidue_comp_residueField_map :
    (gaussResidue W).comp (ResidueField.map (algebraMap 𝒪 (gaussRing W))) =
      algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField := by
  refine RingHom.ext fun c => ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [RingHom.comp_apply, ResidueField.map_residue, gaussResidue_residue_algebraMap]

variable (W' W'' : WeierstrassCurve 𝒪) [W'.IsElliptic] [W''.IsElliptic]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _`. Establish `e` using `gaussCurve_map_functionField K W W'`. Establish `hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W') (pointCongr e.symm R) ≠ 0`. Introduce `h0`. Apply `isGenPt_ne_zero _ hR'` to reduce the goal to its premises.

Simplify using `only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]`. Use `erw [h0]`. Rewrite using `[map_zero, map_zero]`. Take `⟨x, y, h₀, hP⟩` from `exists_integral_of_reducePoint_ne_zero _ _ hne`. Establish `hRe : R = pointCongr e (Point.some _ _ h₀)`.

Rewrite using `[← hP, pointCongr_pointCongr]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨h, hRs⟩ : ∃ h, R = Point.some (algebraMap (gaussRing W) _ x) (algebraMap (gaussRing W) _ y) h := by`. Rewrite using `[hRe, pointCongr_some]`. Conclude with `⟨_, rfl⟩`.

Substitute `hRs` using the available equality. Take `⟨h', e'⟩` from `reduceFF_some K W W' h`. Establish `hR'' : IsGenPt (W'.map (residue 𝒪)) (Point.some _ _ h')` using `e' ▸ hR'`. Rewrite using `[genEval_congr _ e' hR' hR'']`. Use `set j := algebraMap 𝒪 (gaussRing W)`.

Establish `hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) = algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (j c)` using `fun c => by`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Establish `hxy : (W'.map j).toAffine.Equation x y`. Establish `h₁ : ((W'.map j).map (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation (algebraMap _ _ x) (algebraMap _ _ y)`. Rewrite using `[← map_baseChange_eq_map_of K W' j _ hjM]`.

Conclude with `h.1`. Conclude with `(WeierstrassCurve.Affine.map_equation (W'.map j).toAffine (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁`. Establish `hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue _ x))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`.

Assume the negation of the conclusion as `hp0`. Establish `hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x))` using `hR''`. Apply `hT` to reduce the goal to its premises. Use `⟨p, hp0, ?_⟩` and prove the remaining obligations. Establish `key : aeval (gaussResidue W (residue _ x)) p = gaussResidue W (eval₂RingHom (ResidueField.map j) (residue _ x) p)`.

Rewrite using `[aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]`. Rewrite using `[key, hp, map_zero]`. Establish `hring : (gaussResidue W).comp (fieldEvalRed W' j hxy hx) = (genEval (W'.map (residue 𝒪)) _ hR'').toRingHom`. Apply `ringHom_ext_functionField` to reduce the goal to its premises. Introduce `c`.

Rewrite using `[RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply, gaussResidue_comp_residueField_map]`. Conclude with `((genEval _ _ hR'').commutes c).symm`. Rewrite using `[RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, genEval_genX]`. Both sides reduce to the same expression. Rewrite using `[RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, genEval_genY]`.

Both sides reduce to the same expression. Establish `main` using `reducePoint_genEval (K := K) (W := W') (W' := W'') (j := j) (M := (W.baseChange K).toAffine.FunctionField) (hxy := hxy) (hx := hx) hjM h hR Q`. Establish `main' : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'') (pointCongr (gaussCurve_map_functionField K W W'').symm (Point.map (genEval (W'.baseChange K) _ hR) Q)) = pointCongr (map_fieldEvalRed_eq W' W'' j hxy hx) (pointMapRing (fieldEvalRed W' j hxy hx) _ (re …` using `main`. Establish `hL : reduceFF K W W'' (Point.map (genEval (W'.baseChange K) _ hR) Q) = pointCongr (gaussCurve_map_residue W W'') (pointMapRing (gaussResidue W) _ (reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'') (pointCongr (gaussCurve_map_functionField K W W'').symm (Point …`. Simplify using `only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]`.

Both sides reduce to the same expression. Rewrite using `[hL, main']`. Establish `hf` using `DFunLike.congr_fun hring`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf`. Apply `point_ext_xy` to reduce the goal to its premises.

Rewrite using `[pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, map_eq_pointCongr_pointMapRing, pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]`. Rewrite using `[xOf_pointCongr, xOf_pointMapRing, xOf_pointCongr, xOf_pointMapRing, hf, map_eq_pointCongr_pointMapRing, xOf_pointCongr, xOf_pointMapRing]`. Both sides reduce to the same expression. Rewrite using `[yOf_pointCongr, yOf_pointMapRing, yOf_pointCongr, yOf_pointMapRing, hf, map_eq_pointCongr_pointMapRing, yOf_pointCongr, yOf_pointMapRing]`. Both sides reduce to the same expression.
-/
theorem reduceFF_map_genEval
    {R : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hR : IsGenPt (W'.baseChange K) R) (hR' : IsGenPt (W'.map (residue 𝒪)) (reduceFF K W W' R))
    (Q : ((W''.baseChange K).baseChange (W'.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reduceFF K W W'' (Point.map (genEval (W'.baseChange K) R hR) Q) =
      Point.map (genEval (W'.map (residue 𝒪)) _ hR') (reduceFF K W' W'' Q) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have e := gaussCurve_map_functionField K W W'
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr e.symm R) ≠ 0 := by
    intro h0
    apply isGenPt_ne_zero _ hR'
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    erw [h0]
    rw [map_zero, map_zero]
  obtain ⟨x, y, h₀, hP⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have hRe : R = pointCongr e (Point.some _ _ h₀) := by
    rw [← hP, pointCongr_pointCongr]; rfl
  obtain ⟨h, hRs⟩ : ∃ h, R = Point.some (algebraMap (gaussRing W) _ x)
      (algebraMap (gaussRing W) _ y) h := by
    rw [hRe, pointCongr_some]; exact ⟨_, rfl⟩
  subst hRs
  obtain ⟨h', e'⟩ := reduceFF_some K W W' h
  have hR'' : IsGenPt (W'.map (residue 𝒪)) (Point.some _ _ h') := e' ▸ hR'
  rw [genEval_congr _ e' hR' hR'']
  set j := algebraMap 𝒪 (gaussRing W)
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (j c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map j).toAffine.Equation x y := by
    have h₁ : ((W'.map j).map (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' j _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map j).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  have hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue _ x)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := hR''
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (gaussResidue W (residue _ x)) p =
        gaussResidue W (eval₂RingHom (ResidueField.map j) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]
    rw [key, hp, map_zero]
  have hring : (gaussResidue W).comp (fieldEvalRed W' j hxy hx) =
      (genEval (W'.map (residue 𝒪)) _ hR'').toRingHom := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((genEval _ _ hR'').commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        genEval_genX]
      rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        genEval_genY]
      rfl
  have main := reducePoint_genEval (K := K) (W := W') (W' := W'') (j := j)
    (M := (W.baseChange K).toAffine.FunctionField) (hxy := hxy) (hx := hx) hjM h hR Q
  have main' : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'')
      (pointCongr (gaussCurve_map_functionField K W W'').symm
        (Point.map (genEval (W'.baseChange K) _ hR) Q)) =
      pointCongr (map_fieldEvalRed_eq W' W'' j hxy hx)
        (pointMapRing (fieldEvalRed W' j hxy hx) _ (reduceFF K W' W'' Q)) := main
  have hL : reduceFF K W W'' (Point.map (genEval (W'.baseChange K) _ hR) Q) =
      pointCongr (gaussCurve_map_residue W W'') (pointMapRing (gaussResidue W) _
        (reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W'')
          (pointCongr (gaussCurve_map_functionField K W W'').symm
            (Point.map (genEval (W'.baseChange K) _ hR) Q)))) := by
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rfl
  rw [hL, main']
  have hf := DFunLike.congr_fun hring
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
  apply point_ext_xy
  · rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, pointCongr_eq_zero_iff,
      pointMapRing_eq_zero_iff, map_eq_pointCongr_pointMapRing, pointCongr_eq_zero_iff,
      pointMapRing_eq_zero_iff]
  · rw [xOf_pointCongr, xOf_pointMapRing, xOf_pointCongr, xOf_pointMapRing, hf,
      map_eq_pointCongr_pointMapRing, xOf_pointCongr, xOf_pointMapRing]
    rfl
  · rw [yOf_pointCongr, yOf_pointMapRing, yOf_pointCongr, yOf_pointMapRing, hf,
      map_eq_pointCongr_pointMapRing, yOf_pointCongr, yOf_pointMapRing]
    rfl

end Composition

end

end GroundTheory.Global
