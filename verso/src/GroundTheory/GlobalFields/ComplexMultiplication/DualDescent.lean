import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescentBase
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent

namespace GroundTheory.Global

open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
  {A B C : WeierstrassCurve K} [A.IsElliptic] [B.IsElliptic] [C.IsElliptic]

end AlgClosed

section DualOver

variable {F : Type u} [Field F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

/- English proof (translation)
Establish `hQ` using `isGenPt_dualPtOver φ`. Establish `hxy : ∀ Q : (E.baseChange E'.toAffine.FunctionField).toAffine.Point, IsGenPt E Q → xOf _ (Point.map (W'` using `E) (bcEmb (F' := AlgebraicClosure F) E') Q : ((E.baseChange (AlgebraicClosure F)).baseChange (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) = bcEmb (F' := AlgebraicClosure F) E' (xOf _ Q) ∧ yOf _ (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) …`. Introduce `Q hQ`. Consider the cases of `Q with`. Consider the case `zero => exact hQ.elim`.

Consider the case `some x y h => exact ⟨rfl, rfl⟩`. Use `respectsAdd_of_map (algebraMap F (AlgebraicClosure F)) (isogBaseChange (F' := AlgebraicClosure F) φ).dual (isGenPt_ne_zero E hQ) ?_ ?_` and prove the remaining obligations. Rewrite using `[ffMap_algebraMap_eq_bcEmb] show _ = xOf _ (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1`. Rewrite using `[← map_bcEmb_dualPtOver]`. Conclude with `((hxy _ hQ).1).symm`.

Rewrite using `[ffMap_algebraMap_eq_bcEmb] show _ = yOf _ (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1`. Rewrite using `[← map_bcEmb_dualPtOver]`. Conclude with `((hxy _ hQ).2).symm`.
-/
theorem respectsAdd_dualPtOver (φ : Isogeny E E') : RespectsAdd E' E (dualPtOver φ) := by
  classical
  have hQ := isGenPt_dualPtOver φ
  have hxy : ∀ Q : (E.baseChange E'.toAffine.FunctionField).toAffine.Point, IsGenPt E Q →
      xOf _ (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') Q :
        ((E.baseChange (AlgebraicClosure F)).baseChange
          (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
        bcEmb (F' := AlgebraicClosure F) E' (xOf _ Q) ∧
      yOf _ (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') Q :
        ((E.baseChange (AlgebraicClosure F)).baseChange
          (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
        bcEmb (F' := AlgebraicClosure F) E' (yOf _ Q) := by
    intro Q hQ
    cases Q with
    | zero => exact hQ.elim
    | some x y h => exact ⟨rfl, rfl⟩
  refine respectsAdd_of_map (algebraMap F (AlgebraicClosure F))
    (isogBaseChange (F' := AlgebraicClosure F) φ).dual (isGenPt_ne_zero E hQ) ?_ ?_
  · rw [ffMap_algebraMap_eq_bcEmb]
    show _ = xOf _ (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1
    rw [← map_bcEmb_dualPtOver]
    exact ((hxy _ hQ).1).symm
  · rw [ffMap_algebraMap_eq_bcEmb]
    show _ = yOf _ (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1
    rw [← map_bcEmb_dualPtOver]
    exact ((hxy _ hQ).2).symm

noncomputable def dualOver (φ : Isogeny E E') : Isogeny E' E :=
  ⟨dualPtOver φ, (isIsogeny_iff _).mpr ⟨isGenPt_dualPtOver φ, respectsAdd_dualPtOver φ⟩⟩

/- English proof (translation)
The claim follows from `Subtype.ext (map_bcEmb_dualPtOver φ)`.
-/
theorem isogBaseChange_dualOver [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    isogBaseChange (F' := AlgebraicClosure F) (dualOver φ) = (isogBaseChange φ).dual :=
  Subtype.ext (map_bcEmb_dualPtOver φ)

/- English proof (translation)
Apply `isogBaseChange_injective (Ω := AlgebraicClosure F)` to reduce the goal to its premises. Rewrite using `[isogBaseChange_comp, isogBaseChange_dualOver, isogBaseChange_mulIsogeny, mulIsogeny_eq_dual_comp_isogBaseChange]`.
-/
theorem dualOver_comp (φ : Isogeny E E') :
    (dualOver φ).comp φ = mulIsogeny E φ.degree (isogeny_degree_ne_zero φ) := by
  classical
  apply isogBaseChange_injective (Ω := AlgebraicClosure F)
  rw [isogBaseChange_comp, isogBaseChange_dualOver, isogBaseChange_mulIsogeny,
    mulIsogeny_eq_dual_comp_isogBaseChange]

/- English proof (translation)
Apply `isogBaseChange_injective (Ω := AlgebraicClosure F)` to reduce the goal to its premises. Rewrite using `[isogBaseChange_comp, isogBaseChange_dualOver, isogBaseChange_mulIsogeny, Isogeny.comp_dual]`. Conclude with `mulIsogeny_congr (by rw [degree_isogBaseChange]) _ _`.
-/
theorem comp_dualOver (φ : Isogeny E E') :
    φ.comp (dualOver φ) = mulIsogeny E' φ.degree (isogeny_degree_ne_zero φ) := by
  classical
  apply isogBaseChange_injective (Ω := AlgebraicClosure F)
  rw [isogBaseChange_comp, isogBaseChange_dualOver, isogBaseChange_mulIsogeny, Isogeny.comp_dual]
  exact mulIsogeny_congr (by rw [degree_isogBaseChange]) _ _

/- English proof (translation)
Rewrite using `[← degree_isogBaseChange (Ω := AlgebraicClosure F), isogBaseChange_dualOver, Isogeny.degree_dual, degree_isogBaseChange]`.
-/
theorem degree_dualOver (φ : Isogeny E E') : (dualOver φ).degree = φ.degree := by
  classical
  rw [← degree_isogBaseChange (Ω := AlgebraicClosure F), isogBaseChange_dualOver,
    Isogeny.degree_dual, degree_isogBaseChange]

end DualOver

end GroundTheory.Global
