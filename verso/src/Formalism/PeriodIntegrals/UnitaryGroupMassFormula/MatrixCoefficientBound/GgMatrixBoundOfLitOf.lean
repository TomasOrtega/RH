import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

/- English proof (translation)
Introduce `ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd`. Take `⟨hA, hAt⟩` from `hM ι Fq k ψ X hfree d hd`. Use `set A := LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) with hAdef`. Establish `hherm : A.IsHermitian` using `hH ι Fq k ψ X`. Establish `hspec` using `hS X A _ hherm (fun w μ hw hAw => hE hC hR ι Fq k ψ hψ hq (X → ℂ) (permRep (∀ v, GL (Fin k) (Fq v)) X) w μ hw (by rw [← hAw, hAdef, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']))`.

Rewrite using `[hAt, hA]`. Conclude with `⟨hspec.1.transpose, hspec.2⟩`.
-/
theorem ggMatrixBound_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hC : ConvScalar) (hR : GenericRatio) : GGMatrixBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd
  obtain ⟨hA, hAt⟩ := hM ι Fq k ψ X hfree d hd
  set A := LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) with hAdef
  have hherm : A.IsHermitian := hH ι Fq k ψ X
  have hspec := hS X A _ hherm (fun w μ hw hAw =>
    hE hC hR ι Fq k ψ hψ hq (X → ℂ) (permRep (∀ v, GL (Fin k) (Fq v)) X) w μ hw
      (by rw [← hAw, hAdef, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']))
  rw [hAt, hA]
  exact ⟨hspec.1.transpose, hspec.2⟩

/- English proof (translation)
Introduce `hGG hMB` and use `ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)`.
-/
theorem ggMatrixBoundOfLit_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit :=
  fun hGG hMB => ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)

end PI.GGMatBoundW
