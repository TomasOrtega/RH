import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyA

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) X` using `fun a b => ((ContinuousLinearMap.proj b).comp (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt X`. Simplify using `only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]`. Use `Finset.analyticAt_fun_sum _ fun σ _ => ?_` and prove the remaining obligations. Conclude with `analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)`.
-/
theorem analyticAt_det {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) X := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) X := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt X
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

/- English proof (translation)
Establish `h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0` using `(analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)`. Conclude with `h1.zpow (by simp)`.
-/
theorem analyticAt_det_one_add_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℤ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.zpow (by simp)

/- English proof (translation)
Introduce `ι _ _ A t`. Use `set e := Fintype.equivFin ι`. Establish `h1` using `hE ι (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) A (analyticAt_det_one_add_zpow t)`. Establish `h2` using `hR ι (Fin (Fintype.card ι)) e (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) (analyticAt_det_one_add_zpow t)`. Establish `h3 : (fun T : Matrix ι ι ℂ => (1 + Matrix.reindex e e T).det ^ t) = fun T => (1 + T).det ^ t`.

Use function extensionality and compare the values at `T`. Establish `h4 : 1 + Matrix.reindex e e T = Matrix.reindex e e (1 + T)`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Rewrite using `[h4, Matrix.det_reindex_self]`.

Rewrite `h2` using `[h3, hK]`. Rewrite using `[h1, h2, mul_comm]`.
-/
theorem cayley_of (hE : Equivar) (hR : Reindex) (hK : KappaFin) : Cayley := by
  intro ι _ _ A t
  set e := Fintype.equivFin ι
  have h1 := hE ι (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) A (analyticAt_det_one_add_zpow t)
  have h2 := hR ι (Fin (Fintype.card ι)) e
    (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t)
    (analyticAt_det_one_add_zpow t)
  have h3 : (fun T : Matrix ι ι ℂ => (1 + Matrix.reindex e e T).det ^ t) =
      fun T => (1 + T).det ^ t := by
    funext T
    have h4 : 1 + Matrix.reindex e e T = Matrix.reindex e e (1 + T) := by
      ext i j
      simp [Matrix.one_apply]
    rw [h4, Matrix.det_reindex_self]
  rw [h3, hK] at h2
  rw [h1, h2, mul_comm]

end PositivityTheory.Rg.Sw.LVs
