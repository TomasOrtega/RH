import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TraceSum
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.InducedCmType
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext

/- English proof (translation)
Introduce `τ τ' h`. Establish `h1` using `(factEmb D.R D.host).1.1 h`. Conclude with `D.eTau.injective (Subtype.ext h1)`.
-/
theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

/- English proof (translation)
Establish `h1` using `Module.finrank_mul_finrank ℚ D.host.K D.host.E`. Rewrite `h1` using `[Formalism.MainNotions.Ext.finrank_K D.host, Formalism.MainNotions.StandardLattice.finrank_host D]`. Rewrite using `[D.what₂.card_Tau]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_Tau_eq (D : D7) : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  have h1 := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.MainNotions.Ext.finrank_K D.host, Formalism.MainNotions.StandardLattice.finrank_host D] at h1
  rw [D.what₂.card_Tau]
  omega

/- English proof (translation)
The claim follows from `H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D) (card_Tau_eq D)`.
-/
theorem trace_sum_over_letters (H : TraceSum) (D : D7) : StandardLatticesGL3.TraceMapNormalisation D :=
  H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D) (card_Tau_eq D)

/- English proof (translation)
Introduce `M ρ hK hM` and use `H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D) (card_Tau_eq D) M ρ hK hM`.
-/
theorem embedding_permutes_letters (H : PermEmb) (D : D7) : StandardLatticesGL3.EmbeddingPermutesTypes D :=
  fun M ρ hK hM => H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D)
    (card_Tau_eq D) M ρ hK hM

end Formalism.MainNotions.Ext
