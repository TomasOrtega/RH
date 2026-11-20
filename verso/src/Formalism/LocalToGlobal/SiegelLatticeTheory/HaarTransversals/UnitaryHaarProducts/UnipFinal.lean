import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.PrincipalCongruenceMemLevel
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLatStepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `UnipB.noCocompactC_of UnipB.latStepC_holds`.
-/
theorem noCocompactC_holds : NOCocompactC := UnipB.noCocompactC_of UnipB.latStepC_holds

/- English proof (translation)
Take `⟨C, hC, hcov⟩` from `noCocompactC_holds D X u`. Establish `hfin` using `(haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (UnipB.ninf_closed X u) (X.muN u) (X.muN_haar u)).2.1`. Conclude with `⟨C, hC.isClosed.measurableSet, hfin C hC, hcov⟩`.
-/
theorem noCofinite_holds {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : NOCofinite X u := by
  obtain ⟨C, hC, hcov⟩ := noCocompactC_holds D X u
  have hfin := (haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (UnipB.ninf_closed X u) (X.muN u)
    (X.muN_haar u)).2.1
  exact ⟨C, hC.isClosed.measurableSet, hfin C hC, hcov⟩

/- English proof (translation)
Introduce `_ X u` and use `noCofinite_holds X u`.
-/
theorem noCofiniteC_holds : NOCofiniteC := fun _ X u => noCofinite_holds X u

end Formalism.L2.SG.Pf
