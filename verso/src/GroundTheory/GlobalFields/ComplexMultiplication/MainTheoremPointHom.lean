import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionAtPoint
import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section OverF

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω]

omit [DecidableEq F] [PerfectField F] in
/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem app_eq_of_eq {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (φ : Isogeny E E')
    {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {P P' : (E.baseChange L).toAffine.Point}
    (h : P = P') (hP : IsGenPt E P) (hP' : IsGenPt E P') : φ.app P hP = φ.app P' hP' := by
  subst h
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem pointHomOver_comp {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E''.IsElliptic] (ψ : Isogeny E' E'') (φ : Isogeny E E') (R : E.toAffine.Point) :
    pointHomOver Ω (ψ.comp φ) R = pointHomOver Ω ψ (pointHomOver Ω φ R) := by
  apply constMap_injective E'' E.toAffine.FunctionField
  set R' := pointHomOver Ω φ R
  have hX' := isGenPt_genericPoint_add_constMap E' R'
  have e0 := app_genericPoint_add_constMap Ω φ R
  have h1 := app_genericPoint_add_constMap Ω (ψ.comp φ) R

  have e : φ.1 + constMap E' E.toAffine.FunctionField R' =
      Point.map φ.comap (genericPoint E' + constMap E' E'.toAffine.FunctionField R') := by
    rw [map_add, Isogeny.map_comap_genericPoint, map_constMap]
  have hY : IsGenPt E' (φ.1 + constMap E' E.toAffine.FunctionField R') := by
    rw [e]
    exact isGenPt_map E' φ.comap hX'
  have h2 : ψ.app (φ.1 + constMap E' E.toAffine.FunctionField R') hY =
      Point.map φ.comap (ψ.1 + constMap E'' E'.toAffine.FunctionField (pointHomOver Ω ψ R')) := by
    rw [← app_genericPoint_add_constMap Ω ψ R', Isogeny.map_app]
    exact app_eq_of_eq ψ e _ _
  rw [Isogeny.app_comp, app_eq_of_eq ψ e0 _ hY, h2, map_add, map_constMap, ← Isogeny.comp_val,
    add_right_inj] at h1
  exact h1.symm

/- English proof (translation)
Substitute using the available equality. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem pointHomOver_congr {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E₁.IsElliptic] [E₁'.IsElliptic] (φ : Isogeny E E') (hE : E = E₁) (hE' : E' = E₁')
    (R : E.toAffine.Point) :
    pointHomOver Ω (φ.congr hE hE') (pointCongr hE R) = pointCongr hE' (pointHomOver Ω φ R) := by
  subst hE hE'
  rw [Isogeny.congr_rfl]
  rfl

end OverF

section Frobenius

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime] [CharP F p]

omit [PerfectField F] [E.IsElliptic] in
/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem frobeniusPoint_constMap {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (R : E.toAffine.Point) :
    frobeniusPoint E p L (constMap E L R) =
      constMap (frobeniusTwist E p) L (pointMapRing (frobenius F p) E R) := by
  rcases R with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := pointMapRing_some (frobenius F p) E h
    rw [e]
    show Point.some _ _ _ = Point.some _ _ _
    simp only [Algebra.ofId_apply, frobenius_def, map_pow]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem pointHomOver_frobeniusIsogeny (R : E.toAffine.Point) :
    pointHomOver Ω (frobeniusIsogeny E p) R = pointMapRing (frobenius F p) E R := by
  have : CharP E.toAffine.FunctionField p :=
    charP_of_injective_algebraMap (algebraMap F E.toAffine.FunctionField).injective p
  apply constMap_injective (frobeniusTwist E p) E.toAffine.FunctionField
  have hX := isGenPt_genericPoint_add_constMap E R
  have h1 := app_genericPoint_add_constMap Ω (frobeniusIsogeny E p) R
  rw [frobeniusIsogeny_app, frobeniusPoint_add, frobeniusPoint_constMap] at h1
  have h2 : frobeniusPoint E p E.toAffine.FunctionField (genericPoint E) = (frobeniusIsogeny E p).1 :=
    rfl
  rw [h2, add_right_inj] at h1
  exact h1.symm

end Frobenius

end

end GroundTheory.Global
