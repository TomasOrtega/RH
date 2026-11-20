import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocTheoryTied

open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
