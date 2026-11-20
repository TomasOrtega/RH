import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RConvFExistsPfAbs

noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

/- English proof (translation)
Introduce `I μf _ _ hright hsc hborel fund hfund R hR f hf`. Use `haveI := hsc`. Use `haveI := hborel`. Use `haveI : μf.IsMulRightInvariant := hright`. Use `haveI : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf`.

Use `haveI : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf`. Use `haveI : (I.muA μf).IsMulRightInvariant := rr_muA_right I μf`. Establish `hfd` using `rr_FD_of I μf fund hfund`. Establish `hreg` using `rr_IsReg_of I μf fund R hR`. Establish `hemb : Measurable (fun g : I.Gf => ((1, g) : I.GA))` using `by fun_prop`.

Take `⟨T, hT⟩` from `wk_exists (μ := μf) (U := fun g => R (1, g)) (fun g z => (rr_norm hfd hreg (1, g) z).le) (fun x y => ((rr_weak_meas hfd hreg x y).comp_measurable hemb).aestronglyMeasurable) hf`. Conclude with `⟨T, hf, hT⟩`.
-/
theorem convergent_reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RConvFExists := by
  intro I μf _ _ hright hsc hborel fund hfund R hR f hf
  haveI := hsc
  haveI := hborel
  haveI : μf.IsMulRightInvariant := hright
  haveI : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf
  haveI : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  haveI : (I.muA μf).IsMulRightInvariant := rr_muA_right I μf
  have hfd := rr_FD_of I μf fund hfund
  have hreg := rr_IsReg_of I μf fund R hR

  have hemb : Measurable (fun g : I.Gf => ((1, g) : I.GA)) := by fun_prop
  obtain ⟨T, hT⟩ := wk_exists (μ := μf) (U := fun g => R (1, g))
    (fun g z => (rr_norm hfd hreg (1, g) z).le)
    (fun x y => ((rr_weak_meas hfd hreg x y).comp_measurable hemb).aestronglyMeasurable) hf
  exact ⟨T, hf, hT⟩

end Formalism.L2.SG.Pf.RConvFExistsPf
