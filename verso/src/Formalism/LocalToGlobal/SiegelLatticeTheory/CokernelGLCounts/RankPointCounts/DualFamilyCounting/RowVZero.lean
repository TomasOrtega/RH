import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameZZEqNegT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanAtMono
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `first`. Consider the case `simp only [hJ, star_add, Matrix.add_dotProduct]`. Consider the case `simp only [hJ, star_add, add_dotProduct]`. Consider the case `simp [hJ, Matrix.add_dotProduct]`. Consider the case `simp [hJ, add_dotProduct]`.
-/
theorem hJ_add_l {n : ℕ} (ε : Fin n → Bool) (x y z : Fin n → ℂ) : hJ ε (x + y) z = hJ ε x z + hJ ε y z := by
  first
    | simp only [hJ, star_add, Matrix.add_dotProduct]
    | simp only [hJ, star_add, add_dotProduct]
    | simp [hJ, Matrix.add_dotProduct]
    | simp [hJ, add_dotProduct]

/- English proof (translation)
Simplify using `only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : ε i <;> simp [h, mul_comm]`.
-/
theorem hJ_conj' {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h, mul_comm]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Use `first`. Consider the case `exact NumberField.IsCMField.complexEmbedding_complexConj _ t`. Consider the case `(simp only [Formalism.MainNotions.S.embS]; exact NumberField.IsCMField.complexEmbedding_complexConj _ t)`. Consider the case `(haveI := D.host.isCMField_hostE`. Rewrite using `[show (star t : D.host.E) = NumberField.IsCMField.complexConj D.host.E t from rfl]`.

Conclude with `NumberField.IsCMField.complexEmbedding_complexConj _ _ t)`. Consider the case `(haveI := D.host.isCMField_hostE`. Conclude with `NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embS D (X.pl v)) t)`.
-/
theorem emb_star (v : InfinitePlace X.B.I.F) (t : D.host.E) :
    embS D (X.pl v) (star t) = star (embS D (X.pl v) t) := by
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ t
    | (simp only [Formalism.MainNotions.S.embS]; exact NumberField.IsCMField.complexEmbedding_complexConj _ t)
    | (haveI := D.host.isCMField_hostE
       rw [show (star t : D.host.E) = NumberField.IsCMField.complexConj D.host.E t from rfl]
       exact NumberField.IsCMField.complexEmbedding_complexConj _ _ t)
    | (haveI := D.host.isCMField_hostE
       exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embS D (X.pl v)) t)

/- English proof (translation)
Use function extensionality and compare the values at `v j`. Establish `hc : X.crd (x + y) = X.crd x + X.crd y` using `by first`. Consider the case `exact Formalism.L2.SG.Pf.Vanish2.crd_add X x y`. Consider the case `exact Formalism.L2.SG.HidaSetting.crd_add X x y`. Consider the case `(funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf])`.

Establish `hr : rv X.B.I v (X.crd x + X.crd y) = rv X.B.I v (X.crd x) + rv X.B.I v (X.crd y)`. Unfold `rv`. Rewrite using `[← Matrix.mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Simplify using `only [rowV, Pi.add_apply, hc, hr]`. Apply the tactic sequence `split_ifs <;> exact hJ_add_l _ _ _ _`.
-/
theorem rowV_add (x y : (VS D).V) : rowV X u (x + y) = rowV X u x + rowV X u y := by
  funext v j
  have hc : X.crd (x + y) = X.crd x + X.crd y := by
    first
      | exact Formalism.L2.SG.Pf.Vanish2.crd_add X x y
      | exact Formalism.L2.SG.HidaSetting.crd_add X x y
      | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf])
  have hr : rv X.B.I v (X.crd x + X.crd y) = rv X.B.I v (X.crd x) + rv X.B.I v (X.crd y) := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  simp only [rowV, Pi.add_apply, hc, hr]
  split_ifs <;> exact hJ_add_l _ _ _ _

/- English proof (translation)
Establish `h` using `rowV_add X u 0 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h`.
-/
theorem rowV_zero : rowV X u 0 = 0 := by
  have h := rowV_add X u 0 0
  rw [add_zero] at h
  simpa using h

/- English proof (translation)
Rewrite using `[eq_neg_iff_add_eq_zero, add_comm (rowV X u (-x)), ← rowV_add, add_neg_cancel, rowV_zero]`.
-/
theorem rowV_neg (x : (VS D).V) : rowV X u (-x) = -rowV X u x := by
  rw [eq_neg_iff_add_eq_zero, add_comm (rowV X u (-x)), ← rowV_add, add_neg_cancel, rowV_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, sub_eq_add_neg, rowV_add, rowV_neg]`.
-/
theorem rowV_sub (x y : (VS D).V) : rowV X u (x - y) = rowV X u x - rowV X u y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, rowV_add, rowV_neg]

def rowHom : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
  AddMonoidHom.mk' (rowV X u) (rowV_add X u)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
