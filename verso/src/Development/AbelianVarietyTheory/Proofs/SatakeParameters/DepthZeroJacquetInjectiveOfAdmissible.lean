import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
