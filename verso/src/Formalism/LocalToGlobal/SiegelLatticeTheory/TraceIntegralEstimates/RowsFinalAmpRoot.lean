import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRelAtPt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootJac
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootHaar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpOrbQuot
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

namespace Formalism.MainNotions.S.Pv.LemmaJ

/- English proof (translation)
The claim follows from `(show PI.AmpRoot.RelAtPt ↔ RelAtPt from Iff.rfl).mp _root_.amplifier_relation_at_point`.
-/
theorem relAtPt_holds : RelAtPt := (show PI.AmpRoot.RelAtPt ↔ RelAtPt from Iff.rfl).mp _root_.amplifier_relation_at_point

/- English proof (translation)
The claim follows from `(show PI.AmpRoot.RootJac ↔ RootJac from Iff.rfl).mp _root_.amplifier_root_jacobian`.
-/
theorem rootJac_holds : RootJac := (show PI.AmpRoot.RootJac ↔ RootJac from Iff.rfl).mp _root_.amplifier_root_jacobian

/- English proof (translation)
The claim follows from `(show PI.AmpRootH.RootHaar ↔ RootHaar from Iff.rfl).mp _root_.amplifier_root_haar`.
-/
theorem rootHaar_holds : RootHaar := (show PI.AmpRootH.RootHaar ↔ RootHaar from Iff.rfl).mp _root_.amplifier_root_haar

/- English proof (translation)
The claim follows from `(show PI.AmpOrbQ.OrbQuotEx ↔ OrbQuotEx from Iff.rfl).mp (_root_.orbQuotEx_of_haarLieN (show PI.AmpOrbQ.HaarLieN from Formalism.MainNotions.BridgeCSB.haarLieN))`.
-/
theorem exists_orbQuot₂ : OrbQuotEx := (show PI.AmpOrbQ.OrbQuotEx ↔ OrbQuotEx from Iff.rfl).mp (_root_.orbQuotEx_of_haarLieN (show PI.AmpOrbQ.HaarLieN from Formalism.MainNotions.BridgeCSB.haarLieN))

end Formalism.MainNotions.S.Pv.LemmaJ
