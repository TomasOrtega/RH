import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsNonarchimedeanLocalField
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.UnitsPowers
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Introduce `K L _ _ _`. Take `⟨vr, top, hloc, -⟩` from `GlobalTheory.LocFieldOfDVR.exists_isNonarchimedeanLocalField K.O K.E`. Take `⟨vrL, topL, hlocL, -⟩` from `GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L`. Use `haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective`. Conclude with `GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero`.
-/
theorem UQ.finite_units_mod_sq : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L],
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  intro K L _ _ _
  obtain ⟨vr, top, hloc, -⟩ := GlobalTheory.LocFieldOfDVR.exists_isNonarchimedeanLocalField K.O K.E
  obtain ⟨vrL, topL, hlocL, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

end GlobalTheory.UnitLemma
