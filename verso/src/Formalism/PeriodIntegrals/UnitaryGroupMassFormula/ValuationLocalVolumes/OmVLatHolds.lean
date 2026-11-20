import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩`.
-/
theorem isCMExt_sig : IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig :=
  ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

/- English proof (translation)
Use `⟨fun i j => ?_, X.B.I.J_det⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun X.B.I.J_herm i) j`. Conclude with `h`.
-/
theorem isHermND_J : IsHermND X.B.I.cm.sig X.B.I.J := by
  refine ⟨fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  exact h

/- English proof (translation)
Introduce `h1 h2` and use `⟨isCMExt_sig X, isHermND_J X, h1, h2⟩`.
-/
theorem omVStd_holds : OmVStd X ψ := fun h1 h2 => ⟨isCMExt_sig X, isHermND_J X, h1, h2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩`.
-/
theorem omVLat_holds : OmVLat X := ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
