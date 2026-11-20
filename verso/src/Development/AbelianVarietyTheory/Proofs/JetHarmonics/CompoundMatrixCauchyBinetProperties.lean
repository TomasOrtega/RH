import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem compound_mul {n : ℕ} (l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h := by
  ext I J
  have e : (g * h).submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)
      = g.submatrix (I.1.orderEmbOfFin I.2) id * h.submatrix id (J.1.orderEmbOfFin J.2) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  unfold BranchingSupport.cmp
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem compound_conjTranspose {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ := by
  ext I J
  rw [Matrix.conjTranspose_apply]
  unfold BranchingSupport.cmp
  rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]

/- English proof (translation)
By extensionality, compare the relevant components. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem compound_one (n l : ℕ) : BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I J
  unfold BranchingSupport.cmp
  by_cases hIJ : I = J
  · subst hIJ
    rw [Matrix.submatrix_one _ (I.1.orderEmbOfFin I.2).injective, Matrix.det_one, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hIJ]
    have hne : ¬ I.1 ⊆ J.1 := fun hs =>
      hIJ (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [I.2, J.2])))
    obtain ⟨x, hxI, hxJ⟩ := Finset.not_subset.mp hne
    have hx : x ∈ Set.range (I.1.orderEmbOfFin I.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hxI
    obtain ⟨a, ha⟩ := hx
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro hab
    apply hxJ
    rw [← ha, hab]
    exact Finset.orderEmbOfFin_mem _ _ _

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem compound_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  ext I
  have e : (Matrix.of fun a b : Fin l => (g *ᵥ f b) (I.1.orderEmbOfFin I.2 a))
      = g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun (c : Fin n) (b : Fin l) => f b c) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold BranchingSupport.wedge
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  unfold Matrix.mulVec dotProduct BranchingSupport.cmp
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem compound_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ),
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h ∧ BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ ∧
      BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧
      ∀ f : Fin l → Fin n → ℂ, BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) :=
  fun n l g h => ⟨compound_mul l g h, compound_conjTranspose l g, compound_one n l, compound_mulVec_wedge g⟩

end GlobalTheory
