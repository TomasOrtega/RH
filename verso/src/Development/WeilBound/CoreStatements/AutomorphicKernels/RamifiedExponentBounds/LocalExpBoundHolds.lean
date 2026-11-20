import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalSpreadOfLocalExpBound
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

namespace PositivityTheory.JsR

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem localExpBound_holds : LocalExpBound := by
  intro k _ _ _ _ _ N V _ _ π hs hi hu hg
  obtain ⟨h, δ, Δ, s, hΔ, hc, hb, hd⟩ := PositivityTheory.RgUd.Exp.genUnitCCOf PositivityTheory.RgUd.expBound GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds
    k N V π hs hi hu hg
  exact ⟨h, δ, Δ, s, hΔ, fun j _ hω z => PositivityTheory.RgUd.UOrder.log_norm_centralChar_u (hΔ j) (hc j) hω z, hb, hd⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localSpread_holds : LocalSpread := localSpread_of_localExpBound localExpBound_holds

end PositivityTheory.JsR
