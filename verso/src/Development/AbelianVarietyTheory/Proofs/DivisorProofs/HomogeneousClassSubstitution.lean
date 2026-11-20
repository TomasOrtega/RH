import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

namespace GlobalTheory.EZ

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem fc_succ_eq_delta (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min (n + 1) (if (j : ℕ) < i then (j : ℕ) else j + 1) = ((Fin.succAbove i j : Fin (n+2)) : ℕ)
  rcases lt_or_ge (j : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h] <;> omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp [show ¬ (j : ℕ) < i by omega] <;> omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ev_map_dD_eq_diagCx_d {C : Type u} [Category.{v} C] [Preadditive C]
    (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) :
    (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  refine Eq.trans ?_ (AlternatingFaceMapComplex.obj_d_eq (diag.obj Y) n).symm
  rw [dD, if_pos rfl, Functor.map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Functor.map_zsmul, ev_map_bop, fc_succ_eq_delta]
  rfl

end GlobalTheory.EZ
