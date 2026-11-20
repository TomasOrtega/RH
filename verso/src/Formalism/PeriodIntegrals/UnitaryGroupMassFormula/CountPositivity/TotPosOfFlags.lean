import Mathlib
import Formalism.PeriodIntegrals.CntLocalParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.LeadingMinorFullEqProd

noncomputable section

namespace PI.CntNotPosW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem totPos_of_flags (D : Formalism.BasicNotions.D7) {T T' : ℕ} (F : FlagG (VS D) D.R.rS (T : D.host.E))
    (F' : FlagG (VS D) D.R.rS (T' : D.host.E)) (hG : Gflag F F' ≠ 0) : TotPos (Gflag F F') := by
  unfold TotPos
  intro τ
  haveI := D.host.isCMField_hostE
  refine gflag_pos (p' := ((VS D).sig (embS D τ)).1) (q' := ((VS D).sig (embS D τ)).2) F F' (embS D τ)
    (fun a => NumberField.IsCMField.complexEmbedding_complexConj _ (embS D τ) a) (D.sp.Y_sig 0 (embS D τ)) ?_ hG
  rw [D.sp.baseSpace_signature_eq]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem notPosAll : PI.CntLocalParts.NotPosAll := by
  intro D δ M hA L u u' hT F0 what₂ hR Z hZ
  have hE : ∀ Λ, EZ (Tn u') F0 Λ Z = ∅ := by
    intro Λ
    ext F'
    simp only [EZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hG⟩, _, _, _, hZ'⟩
    apply hZ
    have h1 : GZ (Tn u) (Tn u') Z = Gflag F0 F'.fl := by rw [← hZ']; rfl
    rw [h1]
    exact totPos_of_flags D F0 F'.fl hG
  have hc : ∀ Λ, cntE (Tn u') F0 Λ Z = 0 := by
    intro Λ
    simp only [cntE, hE Λ, Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
      Set.encard_empty]
  simp [Formalism.L2.SG.CntLocal.nu, hc]

end PI.CntNotPosW
