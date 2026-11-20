import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

def noTraitZero {X : Scheme.{0}} (M : LB X) : M.Sec := ⟨fun _ => 0, by simp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem noTrait_gs_zero {Y X : Scheme.{0}} (r : Y ⟶ X) (y : Y) (U : X.Opens) : gs r y U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem lin_noTraitZero {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (c : Fin n → Γ(T'.left, ⊤)) : GlobalTheory.LN.Lin G L N h (fun _ => noTraitZero _) c (noTraitZero _) := by
  intro z J _
  refine (noTrait_gs_zero _ _ _).trans (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (congrArg _ (noTrait_gs_zero _ _ _)).trans (mul_zero _)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem noTrait_exists_gl_det_eq {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n) (u : Rˣ) :
    ∃ M : GL (Fin n) R, Matrix.GeneralLinearGroup.det M = u := by
  have hd : (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) ⟨0, hn⟩ u.val)).det = u.val := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hd]; exact u.isUnit), Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hd

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem hasFrames_rank_of_isEmpty (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ)
    (hn : 1 ≤ n') (hZ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z))
    (h : HasFrames G L N A n r s) : HasFrames G L N A n' r s := by
  obtain ⟨th, b, h₁, -⟩ := h
  refine ⟨th, fun _ _ => noTraitZero _, fun i j => ?_, fun i W _ _ _ hW χ _ => ((hZ W hW).false (χ ≫ (A.U i).ι)).elim⟩
  obtain ⟨c, M, h₂, -, h₃⟩ := h₁ i j
  obtain ⟨M', hM⟩ := noTrait_exists_gl_det_eq hn (Matrix.GeneralLinearGroup.det M)
  exact ⟨c, M', h₂, fun k => ⟨noTraitZero _, lin_noTraitZero G L N _ _, lin_noTraitZero G L N _ _⟩, by rw [hM]; exact h₃⟩

end GlobalTheory.ModelSum
