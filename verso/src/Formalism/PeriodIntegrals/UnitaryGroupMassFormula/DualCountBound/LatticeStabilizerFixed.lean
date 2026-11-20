import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.DualCount

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK y`. Unfold `Model.R`. Consider the cases of `h : M.split with`. Consider the case `none`. Conclude with `(M.L.O_def _).2 (isIntegral_algebraMap (x := y))`.

Consider the case `some g`. Rewrite using `[Subring.mem_comap]`. Use `⟨(y, y), RingHom.mem_eqLocus.2 rfl, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((y : F), (y : F)) = g.e (algebraMap F E (y : F))`. Rewrite using `[g.e.commutes]`.

Both sides reduce to the same expression.
-/
theorem lattice_membership_ring : InR := by
  intro F _ _ _ E _ _ _ _ M hOK y
  unfold Model.R
  cases h : M.split with
  | none =>
    exact (M.L.O_def _).2 (isIntegral_algebraMap (x := y))
  | some g =>
    rw [Subring.mem_comap]
    refine ⟨(y, y), RingHom.mem_eqLocus.2 rfl, ?_⟩
    change ((y : F), (y : F)) = g.e (algebraMap F E (y : F))
    rw [g.e.commutes]
    rfl

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK x hx`. Unfold `Model.modK`. Establish `hsub : (fun y => x * y) '' (M.R : Set E) ⊆ (M.R : Set E)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `M.R.mul_mem hx hy`.

Establish `h1 : M.mu ((fun y => x * y) '' (M.R : Set E)) ≤ 1`. Rewrite using `[← hOK.haar.volR]`. Conclude with `MeasureTheory.measure_mono hsub`. Conclude with `ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)`.
-/
theorem lattice_index_modulus_le : ModLe := by
  intro F _ _ _ E _ _ _ _ M hOK x hx
  unfold Model.modK
  have hsub : (fun y => x * y) '' (M.R : Set E) ⊆ (M.R : Set E) := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.R.mul_mem hx hy
  have h1 : M.mu ((fun y => x * y) '' (M.R : Set E)) ≤ 1 := by
    rw [← hOK.haar.volR]; exact MeasureTheory.measure_mono hsub
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)

end PI.NGStepBBW
