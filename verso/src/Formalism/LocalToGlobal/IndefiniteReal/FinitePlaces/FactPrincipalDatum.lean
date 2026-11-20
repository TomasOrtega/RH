import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

noncomputable section

open Formalism.BasicNotions NumberField FractionalIdeal

namespace Formalism.IndefR.Fin

/- English proof (translation)
Introduce `R H`. Take `⟨β, hβ, heq⟩` from `Formalism.MainNotions.UnusedSlot33.HK.diffK_holds H`. Rewrite using `[heq, coeIdeal_span_singleton]`. Use `congr 1`.
-/
theorem diffKPrincipal : Formalism.BasicNotions.DiffKPrincipal := by
  intro R H
  obtain ⟨β, hβ, heq⟩ := Formalism.MainNotions.UnusedSlot33.HK.diffK_holds H
  rw [heq, coeIdeal_span_singleton]
  congr 1

/- English proof (translation)
Introduce `R H`. Rewrite using `[← coeIdeal_mul]`. Establish `h` using `Formalism.MainNotions.UnusedSlot33.HK.normK_holds H H.ccK H.ccK_ne_bot`. Rewrite using `[show (H.ccE : Ideal (𝓞 H.E)) = Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK from rfl, h, coeIdeal_span_singleton, map_natCast]`.
-/
theorem ccNorm : Formalism.BasicNotions.CcNorm := by
  intro R H
  rw [← coeIdeal_mul]
  have h := Formalism.MainNotions.UnusedSlot33.HK.normK_holds H H.ccK H.ccK_ne_bot
  rw [show (H.ccE : Ideal (𝓞 H.E)) = Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK from rfl, h,
    coeIdeal_span_singleton, map_natCast]

/- English proof (translation)
The claim follows from `Formalism.BasicNotions.factPrincipalDatum_of diffKPrincipal ccNorm`.
-/
theorem factPrincipalDatum : Formalism.BasicNotions.FactPrincipalDatum :=
  Formalism.BasicNotions.factPrincipalDatum_of diffKPrincipal ccNorm

end Formalism.IndefR.Fin

end
