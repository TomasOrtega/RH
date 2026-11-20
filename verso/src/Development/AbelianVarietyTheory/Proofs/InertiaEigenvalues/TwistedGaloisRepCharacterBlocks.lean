import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMulLeftDvr
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.Pass

/- English proof (translation)
Introduce `D i r ρ hr π hd Xs hπ`. Take `⟨e, he⟩` from `hd`. Conclude with `subTw_blocks D i r ρ hr π e he Xs hπ`.
-/
theorem stepSub_holds : StepSub := by
  intro D i r ρ hr π hd Xs hπ
  obtain ⟨e, he⟩ := hd
  exact subTw_blocks D i r ρ hr π e he Xs hπ

end GlobalTheory.Pass
