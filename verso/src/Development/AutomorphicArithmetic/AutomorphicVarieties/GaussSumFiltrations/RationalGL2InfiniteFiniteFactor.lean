import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.RatPts

/- English proof (translation)
Use function extensionality and compare the values at `v`. Conclude with `InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)`.
-/
theorem pInf_algebraMap (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) = rhom x := by
  funext v
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)

/- English proof (translation)
Use extensionality with `i j v`. Conclude with `congrFun (pInf_algebraMap F (γ i j)) v`.
-/
theorem pInf_ratGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) = toInf γ := by
  ext i j v
  exact congrFun (pInf_algebraMap F (γ i j)) v

/- English proof (translation)
Introduce `F _ _ _ γ`. Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[← pInf_ratGL]`. Conclude with `(TR.infGL_mul_finGL (ratGL F 2 γ)).symm`. Take `⟨τ, hτ⟩` from `GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h`.

Use `⟨τ, fun v => ?_⟩` and prove the remaining obligations. Establish `e` using `hτ v`. Rewrite `e` using `[MonoidHom.comp_apply, pInf_ratGL]`. Then use the resulting hypothesis.
-/
theorem ratGL_real_fin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F),
    ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧
      ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  intro F _ _ _ γ
  refine ⟨?_, fun h => ?_⟩
  · rw [← pInf_ratGL]
    exact (TR.infGL_mul_finGL (ratGL F 2 γ)).symm
  · obtain ⟨τ, hτ⟩ := GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h
    refine ⟨τ, fun v => ?_⟩
    have e := hτ v
    rwa [MonoidHom.comp_apply, pInf_ratGL] at e

end GlobalTheory.HilbertThetaSeries.RatPts

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | exact GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | (intros; apply GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rational_GL2_infinite_finite_factor : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F), ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | exact GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | (intros; apply GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin <;> assumption)
