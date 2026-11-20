import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenTopH

variable {D : D7} {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_projFin (g : G D n) : (mat g).map (finPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projFin D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_projInf (g : G D n) : (mat g).map (infPart D) = (HA.mat _ D.sp.cm.sig (Jst D n) (projInf D.sp.cm.sig (Jst D n) g)).1 :=
  rfl

end PositivityTheory.Rg.Sw.Glob.GenTopH

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Introduce `_ hP hKi hKf D n`. Use `show Subgroup.closure (genSet D n) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `g _`. Take `⟨p, hp, k, hk, rfl⟩` from `GlobalTheory.StdUnn.Iwasawa.exists_mul D n g`.

Use `Subgroup.mul_mem _ (hP D n p hp) ?_` and prove the remaining obligations. Rewrite using `[← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig (Jst D n) k]`. Establish `hk'` using `mem_levelAll.1 hk`. Use `Subgroup.mul_mem _ (hKi D n _ ?_ ?_) (hKf D n _ ?_ ?_)` and prove the remaining obligations. Use `mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[proj_ofInf]`. Conclude with `one_mem _`. Rewrite using `[projArch_ofInf, projInfArch_projInf]`. Conclude with `hk'.2 w`. Rewrite using `[GenTopH.mat_projFin, projFin_ofInf]`.

Both sides reduce to the same expression. Use `mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[proj_ofFin, projFinLoc_projFin]`. Conclude with `hk'.1 v`. Rewrite using `[projArch_ofFin]`.

Conclude with `one_mem _`. Introduce `τ`. Establish `e : Formalism.IndefR.Eqv.psiT D τ = (Formalism.IndefR.Eqv.thetaC D τ).comp (infPart D)` using `rfl`. Rewrite using `[e, RingHom.coe_comp, ← Matrix.map_map, GenTopH.mat_projInf, projInf_ofFin]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem genA_of : UnitD → PIn → KInInf → KInFin → GenA := by
  intro _ hP hKi hKf D n
  show Subgroup.closure (genSet D n) = ⊤
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  refine Subgroup.mul_mem _ (hP D n p hp) ?_
  rw [← ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig (Jst D n) k]
  have hk' := mem_levelAll.1 hk
  refine Subgroup.mul_mem _ (hKi D n _ ?_ ?_) (hKf D n _ ?_ ?_)
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofInf]; exact one_mem _
    · rw [projArch_ofInf, projInfArch_projInf]; exact hk'.2 w
  · rw [GenTopH.mat_projFin, projFin_ofInf]; rfl
  · refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [proj_ofFin, projFinLoc_projFin]; exact hk'.1 v
    · rw [projArch_ofFin]; exact one_mem _
  · intro τ
    have e : Formalism.IndefR.Eqv.psiT D τ = (Formalism.IndefR.Eqv.thetaC D τ).comp (infPart D) := rfl
    rw [e, RingHom.coe_comp, ← Matrix.map_map, GenTopH.mat_projInf, projInf_ofFin]
    exact Matrix.map_one _ (map_zero _) (map_one _)

end PositivityTheory.Rg.Sw.Glob
