import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem crdOf_mem {y : (VS D).V} (hy : y ∈ (VS D).L0) : crdOf X.B.I X.ιE X.bas y ∈ abelian₂ X := by
  show crdOf X.B.I X.ιE X.bas y ∈ X.B.I.L
  rw [X.L_eq]
  simp only [crdOf, RingEquiv.apply_symm_apply]
  rw [X.bas.sum_repr]
  exact hy

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frame_vector_mem_base_lattice : X.zu u' ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u'))

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem yTup_z_mem (v : PlX X) : yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  have hs : scl X v (zi (D := D)) = 1 := by
    simp only [scl, zi, Fin.append_left]; exact alp_last v D.R.rS
  have h1 : yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by
    funext i
    change sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _
    rw [hs]
    simp only [sc, ← Algebra.TensorProduct.one_def, one_mul]
    rfl
  rw [h1, tupH_eq]
  refine Submodule.subset_span ⟨_, crdOf_mem X ?_, rfl⟩
  simp only [hv, zi, Fin.append_left, Fin.snoc_last]
  exact frame_vector_mem_base_lattice X u'

def OmVMemEF : Prop :=
  ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), i ≠ zi (D := D) → yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem omVMem_of (h : OmVMemEF X u') : OmVMem X u' := by
  intro v i
  by_cases hi : i = zi (D := D)
  · subst hi; exact yTup_z_mem X u' v
  · exact h v i hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
