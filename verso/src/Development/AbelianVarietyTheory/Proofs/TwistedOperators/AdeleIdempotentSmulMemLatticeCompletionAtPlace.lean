import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPlLoc

/- English proof (translation)
Introduce `D S 𝔞 L v z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hαi, -, a, ha, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `mul_mem (ePl_int _ w) (hαi w)`. Rewrite using `[map_mul, evalV_ePl, if_neg hw, zero_mul]`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`.

Unfold `idem`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ h h' => rw [smul_add]`.

Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem idem_smul_mem_latMul_at : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  intro D S 𝔞 L v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]
      exact mul_mem (ePl_int _ w) (hαi w)
    · rw [map_mul, evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.FinPlLoc
