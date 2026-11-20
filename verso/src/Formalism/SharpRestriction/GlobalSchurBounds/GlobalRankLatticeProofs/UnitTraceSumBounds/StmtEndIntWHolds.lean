import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpInertOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OkpInert
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime

namespace Formalism.MainNotions.Ext

/- English proof (translation)
The claim follows from `integers_inert_prime`.
-/
theorem okpInertG_holds : OkpInertG := integers_inert_prime

/- English proof (translation)
The claim follows from `isPrime_span_of_jacobi_neg_one`.
-/
theorem inertPrime_holds : InertPrime := isPrime_span_of_jacobi_neg_one

/- English proof (translation)
The claim follows from `okpInert_of okpInertG_holds inertPrime_holds D`.
-/
theorem okpInert_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.okpInert D := okpInert_of okpInertG_holds inertPrime_holds D

/- English proof (translation)
The claim follows from `stmt_endIntW_of_okp D (okpInert_holds D)`.
-/
theorem stmt_endIntW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementEndomorphismIntegralWitt D := stmt_endIntW_of_okp D (okpInert_holds D)

end Formalism.MainNotions.Ext
