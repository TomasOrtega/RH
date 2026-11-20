import Mathlib

namespace GlobalTheory.TraceEqualFinrank

open Module

/- English proof (translation)
Establish `he : IsIdempotentElem (Matrix.toLin' P)`. Express the relevant statement in the definitionally equal form `Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P`. Rewrite using `[Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]`. Establish `hproj` using `(LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' P)).mpr he`. Rewrite using `[← Matrix.trace_toLin'_eq, hproj.trace]`.
-/
theorem trace_eq_finrank_range {g : ℕ} (P : Matrix (Fin g) (Fin g) ℂ) (hP : IsIdempotentElem P) :
    Matrix.trace P = (finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' P)).mpr he
  rw [← Matrix.trace_toLin'_eq, hproj.trace]

/- English proof (translation)
Establish `hrk : finrank ℂ (LinearMap.range (Matrix.toLin' P')) = finrank ℂ (LinearMap.range (Matrix.toLin' P))`. Establish `h2` using `(trace_eq_finrank_range P' hP').symm.trans (h.symm.trans (trace_eq_finrank_range P hP))`. Conclude with `h2` after adjusting the coercions. Set `e` to `LinearEquiv.ofFinrankEq _ _ hrk`. Establish `hid' : ∀ w ∈ LinearMap.range (Matrix.toLin' P'), Matrix.toLin' P' w = w`.

Introduce and unpack `w ⟨u, rfl⟩`. Rewrite using `[← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP'.eq]`. Set `Xl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `(LinearMap.range (Matrix.toLin' P')).subtype ∘ₗ e.symm.toLinearMap ∘ₗ (Matrix.toLin' P).rangeRestrict`. Set `Yl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `(LinearMap.range (Matrix.toLin' P)).subtype ∘ₗ e.toLinearMap ∘ₗ (Matrix.toLin' P').rangeRestrict`. Use `⟨LinearMap.toMatrix' Xl, LinearMap.toMatrix' Yl, ?_⟩` and prove the remaining obligations.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hw` using `(e.symm ((Matrix.toLin' P).rangeRestrict v)).2`. Establish `h1 : (Matrix.toLin' P').rangeRestrict (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ))) = e.symm ((Matrix.toLin' P).rangeRestrict v)`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.toLin' P' (Matrix.toLin' P' _) = _`. Rewrite using `[hid' _ hw, hid' _ hw]`. Express the relevant statement in the definitionally equal form `((e ((Matrix.toLin' P').rangeRestrict (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ)))) : LinearMap.range (Matrix.toLin' P)) : Fin g → ℂ) = Matrix.toLin' P v`. Rewrite using `[h1, LinearEquiv.apply_symm_apply]`.

Both sides reduce to the same expression.
-/
theorem exists_mul_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P')
    (h : Matrix.trace P = Matrix.trace P') :
    ∃ (X : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℂ), Y * P' * X = P := by
  have hrk : finrank ℂ (LinearMap.range (Matrix.toLin' P')) =
      finrank ℂ (LinearMap.range (Matrix.toLin' P)) := by
    have h2 := (trace_eq_finrank_range P' hP').symm.trans (h.symm.trans (trace_eq_finrank_range P hP))
    exact_mod_cast h2
  let e := LinearEquiv.ofFinrankEq _ _ hrk
  have hid' : ∀ w ∈ LinearMap.range (Matrix.toLin' P'), Matrix.toLin' P' w = w := by
    rintro w ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP'.eq]
  let Xl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P')).subtype ∘ₗ
    e.symm.toLinearMap ∘ₗ (Matrix.toLin' P).rangeRestrict
  let Yl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P)).subtype ∘ₗ
    e.toLinearMap ∘ₗ (Matrix.toLin' P').rangeRestrict
  refine ⟨LinearMap.toMatrix' Xl, LinearMap.toMatrix' Yl, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  have hw := (e.symm ((Matrix.toLin' P).rangeRestrict v)).2
  have h1 : (Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ))) =
      e.symm ((Matrix.toLin' P).rangeRestrict v) := by
    apply Subtype.ext
    change Matrix.toLin' P' (Matrix.toLin' P' _) = _
    rw [hid' _ hw, hid' _ hw]
  change ((e ((Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ)))) :
      LinearMap.range (Matrix.toLin' P)) : Fin g → ℂ) = Matrix.toLin' P v
  rw [h1, LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.TraceEqualFinrank
