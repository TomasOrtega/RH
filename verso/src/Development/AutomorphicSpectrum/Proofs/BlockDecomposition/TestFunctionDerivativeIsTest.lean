import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

/- English proof (translation)
Set `L : Lie E a →ₗ[ℝ] Lie E a` to `{ toFun := fun w => toL (Matrix.of w * Matrix.of X) map_add' := fun w v => by`. Simplify using `only [toL]`. Conclude with `congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))`. Use the proof step `map_smul' := fun c w => by`. Simplify using `only [toL, RingHom.id_apply]`.

Conclude with `congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }`. Conclude with `(LinearMap.toContinuousLinearMap L).contDiff`.
-/
theorem contDiff_mulRight {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) :
    ContDiff ℝ ∞ (fun w : Lie E a => toL (Matrix.of w * Matrix.of X)) := by
  let L : Lie E a →ₗ[ℝ] Lie E a :=
    { toFun := fun w => toL (Matrix.of w * Matrix.of X)
      map_add' := fun w v => by
        simp only [toL]
        exact congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))
      map_smul' := fun c w => by
        simp only [toL, RingHom.id_apply]
        exact congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }
  exact (LinearMap.toContinuousLinearMap L).contDiff

/- English proof (translation)
Use `(closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))` and prove the remaining obligations. Rewrite `hw`, the goal using `[Function.mem_support]`. Introduce `h`. Apply `hw` to reduce the goal to its premises. Simplify using `[dTest, h]`.
-/
theorem tsupport_dTest_subset {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) (β : Lie E a → ℂ) :
    tsupport (dTest X β) ⊆ tsupport β := by
  refine (closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  simp [dTest, h]

/- English proof (translation)
Establish `hfd` using `(contDiff_infty_iff_fderiv.mp hβ.contDiff).2`. Use `IsTest.mk ?_ ?_ ?_` and prove the remaining obligations. Conclude with `hfd.clm_apply (contDiff_mulRight X)`. Conclude with `hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))`. Conclude with `(tsupport_dTest_subset X β).trans hβ.support`.
-/
theorem isTest_dTest (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ)
    (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := by
  have hfd := (contDiff_infty_iff_fderiv.mp hβ.contDiff).2
  refine IsTest.mk ?_ ?_ ?_
  · exact hfd.clm_apply (contDiff_mulRight X)
  · exact hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))
  · exact (tsupport_dTest_subset X β).trans hβ.support

end GlobalTheory.CompanionTheory.SmoothRep
