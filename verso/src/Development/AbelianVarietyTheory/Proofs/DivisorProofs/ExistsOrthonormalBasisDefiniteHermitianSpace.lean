import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteFrame

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_unitary_frame : ∀ (D : D7) (V : HSp D), V.SigOK → (∀ τ, V.sig τ = (V.rank, 0)) →
    ∃ fr : GL (Fin V.rank) D.host.E, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 := by
  intro D V hs hp
  obtain ⟨b, hli, horth⟩ := GlobalTheory.DefiniteOrthonormal.landherrHasse D V hs hp
  have hsp : Submodule.span D.host.E (Set.range b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli]
    simp [V.rank_eq]
  let B : Module.Basis (Fin V.rank) D.host.E V.V := Module.Basis.mk hli (by rw [hsp])
  have hB : ∀ a, B a = b a := fun a => by simp [B]
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := V.frame.toMatrix B
  let M' : Matrix (Fin V.rank) (Fin V.rank) D.host.E := B.toMatrix V.frame
  let fr : GL (Fin V.rank) D.host.E :=
    ⟨M, M', Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨fr, ?_⟩
  ext a c
  have key : V.hT (b a) (b c) = ∑ i, ∑ j, star (M i a) * V.gram i j * M j c := by
    rw [← hB a, ← hB c]
    conv_lhs => rw [← V.frame.sum_repr (B a), ← V.frame.sum_repr (B c)]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum, M, Module.Basis.toMatrix_apply, Formalism.BasicNotions.HSpace.gram]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply]
    ring
  have lhs : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1) a c
      = ∑ i, ∑ j, star (M i a) * V.gram i j * M j c := by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [lhs, ← key, horth, Matrix.one_apply]

end GlobalTheory.DefiniteFrame
