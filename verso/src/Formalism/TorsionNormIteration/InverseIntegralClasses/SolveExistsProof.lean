import Formalism.TorsionNormIteration.InvIntegralOfClass

noncomputable section

universe u v

namespace Formalism.LT.SolveP

open PowerSeries

/- English proof (translation)
Introduce `R _ ι _ f G hf0 hf1 hG0`. Establish `hu : IsUnit (coeff 1 f)` using `by rw [hf1]; exact isUnit_one`. Use `set g := f.substInvOfIsUnit hu with hg`. Establish `hgS : HasSubst g` using `HasSubst.substInvOfIsUnit f hu`. Establish `hGS : HasSubst G` using `HasSubst.of_constantCoeff_zero hG0`.

Use `⟨g.subst G, ?_, ?_⟩` and prove the remaining obligations. Conclude with `constantCoeff_subst_eq_zero hG0 g (constantCoeff_substInvOfIsUnit f hu)`. Rewrite using `[← subst_comp_subst_apply hgS hGS, subst_substInvOfIsUnit_right f hf0 hu, subst_X hGS]`.
-/
theorem SolveExists_proof : Formalism.LT.SolveExists.{u, v} := by
  intro R _ ι _ f G hf0 hf1 hG0
  have hu : IsUnit (coeff 1 f) := by rw [hf1]; exact isUnit_one
  set g := f.substInvOfIsUnit hu with hg
  have hgS : HasSubst g := HasSubst.substInvOfIsUnit f hu
  have hGS : HasSubst G := HasSubst.of_constantCoeff_zero hG0
  refine ⟨g.subst G, ?_, ?_⟩
  · exact constantCoeff_subst_eq_zero hG0 g (constantCoeff_substInvOfIsUnit f hu)
  · rw [← subst_comp_subst_apply hgS hGS, subst_substInvOfIsUnit_right f hf0 hu, subst_X hGS]

end Formalism.LT.SolveP

/- English proof (translation)
The claim follows from `Formalism.LT.SolveP.SolveExists_proof`.
-/
theorem Formalism.LT.SolveExists_proof : Formalism.LT.SolveExists.{u, v} := Formalism.LT.SolveP.SolveExists_proof
