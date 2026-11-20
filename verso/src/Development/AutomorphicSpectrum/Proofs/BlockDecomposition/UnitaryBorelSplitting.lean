import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BorelSplit

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem borelSplitU : PositivityTheory.SphericalProduct.BorelSplitU := by
  intro L _ _ σ n _ b hb
  have hbT : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    (Formalism.UG.P.spherical_upper_iff _).1 hb
  let qb : GlobalTheory.LGrp.blockQ L (id : Fin n → Fin n) := ⟨(b : GL (Fin n) L), hbT⟩
  have htG : GlobalTheory.LGrp.blockProj id qb ∈ GU σ n :=
    GlobalTheory.LGrp.blockProj_mem_GU σ (GlobalTheory.LGrp.selfDualBlocks_id n) qb b.2
  let t : GU σ n := ⟨GlobalTheory.LGrp.blockProj id qb, htG⟩
  have hdiag : ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    show (GlobalTheory.LGrp.blockProj id qb).val i i = _
    rw [GlobalTheory.LGrp.blockProj_val]
    simp [GlobalTheory.LGrp.blockPart, qb]
  have hoff : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    show (GlobalTheory.LGrp.blockProj id qb).val i j = _
    rw [GlobalTheory.LGrp.blockProj_val]
    simp [GlobalTheory.LGrp.blockPart, hij]
  have htT : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    fun i j h => hoff i j (ne_of_gt h)
  have htiT := Formalism.UG.P.spherical_upper_inv _ htT
  refine ⟨t, t⁻¹ * b, hoff, ⟨?_, ?_⟩, by group⟩
  · refine (Formalism.UG.P.spherical_upper_iff _).2 ?_
    show ((((t : GL (Fin n) L))⁻¹ * (b : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id
    exact Formalism.UG.P.spherical_upper_mul _ _ htiT hbT
  · intro i
    show ((((t : GL (Fin n) L))⁻¹ * (b : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1
    have h1 : ((((t : GL (Fin n) L))⁻¹ * (t : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Formalism.UG.P.spherical_diag_mul _ _ htiT hbT, ← hdiag]
    rwa [Units.val_mul, Formalism.UG.P.spherical_diag_mul _ _ htiT htT] at h1

end GlobalTheory.CompanionTheory.BorelSplit
