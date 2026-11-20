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
Establish `h0 : Valued.v x ≠ 0`. Introduce `h`. Conclude with `hx0 ((Valuation.zero_iff _).mp h)`. Unfold `ordL at hx`. Rewrite `hx` using `[dif_neg h0]`.

Establish `hu : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ)`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using `only [toAdd_ofAdd]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← WithZero.coe_unzero h0, hu]`.
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
Introduce `E _ _ _ hU w hw ϖ hϖ`. Take `⟨-, -, -, h4, -⟩` from `GlobalTheory.T.placeConjugation_properties_cmField E hU w`. Take `⟨ϖ₀, q, hI, -⟩` from `(h4 hw).2.1`. Use `⟨q, hI.1, hI.2.1, hϖ.2, ?_, hI.2.2.2.2⟩` and prove the remaining obligations. Conclude with `UniformizerOfValuationOne.v_of_ordL_eq_one (Units.ne_zero ϖ) hϖ.1`.
-/
theorem unifOf : UnifOf := by
  intro E _ _ _ hU w hw ϖ hϖ
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨ϖ₀, q, hI, -⟩ := (h4 hw).2.1
  refine ⟨q, hI.1, hI.2.1, hϖ.2, ?_, hI.2.2.2.2⟩
  exact UniformizerOfValuationOne.v_of_ordL_eq_one (Units.ne_zero ϖ) hϖ.1

end PositivityTheory.Rg.BcB.F.Inert

end
