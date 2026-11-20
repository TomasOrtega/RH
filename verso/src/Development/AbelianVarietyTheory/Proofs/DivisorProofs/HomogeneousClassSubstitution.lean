import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

namespace GlobalTheory.EZ

/- English proof (translation)
Use extensionality with `j`. Establish `hj : (j : ℕ) < n + 1` using `j.isLt`. Simplify using `only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]`. Express the relevant statement in the definitionally equal form `min (n + 1) (if (j : ℕ) < i then (j : ℕ) else j + 1) = ((Fin.succAbove i j : Fin (n+2)) : ℕ)`. Break down `lt_or_ge (j : ℕ) i with h | h` into its components or cases.

Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]`. Apply the tactic sequence `simp [h] <;> omega`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]`. Apply the tactic sequence `simp [show ¬ (j : ℕ) < i by omega] <;> omega`.
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
Use `Eq.trans ?_ (AlternatingFaceMapComplex.obj_d_eq (diag.obj Y) n).symm` and prove the remaining obligations. Rewrite using `[dD, if_pos rfl, Functor.map_sum, ← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Functor.map_zsmul, ev_map_bop, fc_succ_eq_delta]`. Both sides reduce to the same expression.
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
