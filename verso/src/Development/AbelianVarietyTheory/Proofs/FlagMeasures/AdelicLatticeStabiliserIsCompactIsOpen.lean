import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `I`. Take `⟨h1, h2, -, h4, h5, -⟩` from `GlobalTheory.CongTop.adelic_topology I`. Conclude with `⟨h4, h5, h2, h1⟩`.
-/
theorem adelicStab_isCompact_isOpen :
    ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  intro I
  obtain ⟨h1, h2, -, h4, h5, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨h4, h5, h2, h1⟩

end GlobalTheory
