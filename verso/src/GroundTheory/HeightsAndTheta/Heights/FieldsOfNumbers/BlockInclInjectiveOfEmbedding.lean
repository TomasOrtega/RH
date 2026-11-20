import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractBlocksSplitPrime
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameHilbFn
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRelevantPrimeDimGe
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PFContracted.natCast_lt_withBotWithTop {a b : ℕ} (h : a < b) :
    ((a : ℕ) : WithBot (WithTop ℤ)) < ((b : ℕ) : WithBot (WithTop ℤ)) := by
  show (((a : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((b : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by exact_mod_cast h))

/- English proof (translation)
Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Both sides reduce to the same expression.
-/
theorem PFContracted.blockIncl_injective_of_embedding {K K' : Type} (j : K ↪ K') (ι' : K' → Type) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨k₁, x₁⟩ ⟨k₂, x₂⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  cases j.injective h1
  cases eq_of_heq h2
  rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
