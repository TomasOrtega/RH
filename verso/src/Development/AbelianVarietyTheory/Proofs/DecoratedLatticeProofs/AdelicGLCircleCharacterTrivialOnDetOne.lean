import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvectionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmFieldStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

/- English proof (translation)
Take `⟨w, hw⟩` from `h2`. Set `f : Fin n → R` to `Function.update 1 i 2`. Set `g : Fin n → R` to `Function.update 1 i (↑w⁻¹ : R)`. Establish `hfg : ∀ k, f k * g k = 1`. Introduce `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[f, g, ← hw]`. Simplify using `[f, g, hk]`. Establish `hgf : ∀ k, g k * f k = 1` using `fun k => by rw [mul_comm]; exact hfg k`.

Set `d : GL (Fin n) R` to `⟨Matrix.diagonal f, Matrix.diagonal g, by rw [Matrix.diagonal_mul_diagonal]; simp [hfg], by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩`. Establish `hcomm : d * u = u * u * d`. Apply `Units.ext` to reduce the goal to its premises. Establish `hfi : f i = 2` using `by simp [f]`. Establish `hfj : f j = 1` using `by simp [f, hij.symm]`.

Express the relevant statement in the definitionally equal form `Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f`. Rewrite using `[hu, Matrix.transvection_mul_transvection_same _ _ hij]`. Use extensionality with `a b`. Simplify using `only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, Matrix.diagonal_apply, Matrix.one_apply]`. Use `clear_value f g d`.

Use `clear hfg hgf`. Apply the tactic sequence `split_ifs <;> subst_vars <;> simp_all <;> ring`. Establish `h` using `congrArg α hcomm`. Simplify using `only [map_mul] at h`. Establish `h' : α d * α u = α d * (α u * α u)` using `by rw [h]; exact mul_comm _ _ |>.trans (by rfl)`.

Establish `h''` using `mul_left_cancel h'`. Conclude with `(mul_eq_left.mp h''.symm)`.
-/
theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

/- English proof (translation)
Introduce `D n α _ a ha`. Establish `h2 : IsUnit (2 : AE D)`. Establish `h` using `(IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))`. Rewrite `h` using `[map_ofNat]`. Then use the resulting hypothesis. Use `GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha` as an intermediate fact.

Conclude with `MonoidHom.mem_ker.mp this`.
-/
theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
