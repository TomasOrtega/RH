import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ModFIotaFinitePlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormIndex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.CardQuotientEqAbsNorm

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem normLoc_of (hI : IndexFormula) (hC : CardStep) : St.NormLoc :=
  fun _F _ _ p _K _ _ _ _ ι hd hv z => modF_iota_finitePlace p ι hI hC hd hv z

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normLoc_of_card (hC : CardStep) : St.NormLoc := normLoc_of modulus_mul_card_quotient hC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modulus_eq_finitePlace : St.NormLoc := normLoc_of_card card_quotient_eq_absNorm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modF_localization_eq_adicAbv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = NumberField.HeightOneSpectrum.adicAbv F p z :=
  modF_locAt modulus_mul_card_quotient card_quotient_eq_absNorm L z

end PI.ProdFormulaE
