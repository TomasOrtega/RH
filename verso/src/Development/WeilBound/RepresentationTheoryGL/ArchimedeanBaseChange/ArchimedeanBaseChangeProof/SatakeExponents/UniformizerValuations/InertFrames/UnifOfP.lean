import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace UniformizerOfValuationOne

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem v_of_ordL_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (hx0 : x ≠ 0) (hx : ordL x = 1) :
    Valued.v x = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := by
    intro h
    exact hx0 ((Valuation.zero_iff _).mp h)
  unfold ordL at hx
  rw [dif_neg h0] at hx
  have hu : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    omega
  rw [← WithZero.coe_unzero h0, hu]

end UniformizerOfValuationOne

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem unifOf : UnifOf := by
  intro E _ _ _ hU w hw ϖ hϖ
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨ϖ₀, q, hI, -⟩ := (h4 hw).2.1
  refine ⟨q, hI.1, hI.2.1, hϖ.2, ?_, hI.2.2.2.2⟩
  exact UniformizerOfValuationOne.v_of_ordL_eq_one (Units.ne_zero ϖ) hϖ.1

end PositivityTheory.Rg.BcB.F.Inert

end
