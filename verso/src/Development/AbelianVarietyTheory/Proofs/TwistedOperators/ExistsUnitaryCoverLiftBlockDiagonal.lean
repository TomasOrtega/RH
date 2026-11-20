import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem exists_lift_blocks (p q : ℕ) (T : GrpData p q) :
    ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  intro U hU V hV
  have hU1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hU2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hV2 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [star_eq_conjTranspose] at hU1 hU2 hV1 hV2
  let g : GL (Ix p q) ℂ :=
    ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
      by simp [Matrix.fromBlocks_multiply, hU1, hV1],
      by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V
      = Formalism.UG.Jpq p q
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det
    (show 0 < 2 by norm_num)
  have hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by
    unfold matG; rw [hk]
  refine ⟨k, ?_, hm⟩
  show IsKC (matG T k)
  rw [hm]
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

end GlobalTheory.PolarU
