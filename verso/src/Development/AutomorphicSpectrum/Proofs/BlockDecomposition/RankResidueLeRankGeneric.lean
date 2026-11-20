import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype

namespace GlobalTheory.CompanionTheory.Jp

/- English proof (translation)
Introduce `O L _ _ _ _ _ _ n T`. Take `⟨S, τ, hdet⟩` from `GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O) (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl`. Establish `hres : IsLocalRing.residue O (T.submatrix S τ).det = ((T.map (IsLocalRing.residue O)).submatrix S τ).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hfrac : algebraMap O L (T.submatrix S τ).det = ((T.map (algebraMap O L)).submatrix S τ).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `hO : (T.submatrix S τ).det ≠ 0`. Introduce `h`.

Apply `hdet` to reduce the goal to its premises. Rewrite using `[← hres, h, map_zero]`. Establish `hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0`. Rewrite using `[← hfrac]`. Introduce `h`.

Conclude with `hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)), Fintype.card_fin]`. Use `_ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _`.
-/
theorem rank_residue_map_le_rank_fraction_map :
    ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L]
      [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O),
      (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  intro O L _ _ _ _ _ _ n T
  obtain ⟨S, τ, hdet⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O)
    (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl
  have hres : IsLocalRing.residue O (T.submatrix S τ).det =
      ((T.map (IsLocalRing.residue O)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hfrac : algebraMap O L (T.submatrix S τ).det =
      ((T.map (algebraMap O L)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hO : (T.submatrix S τ).det ≠ 0 := by
    intro h
    apply hdet
    rw [← hres, h, map_zero]
  have hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0 := by
    rw [← hfrac]
    intro h
    exact hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))
  calc (T.map (IsLocalRing.residue O)).rank
      = ((T.map (algebraMap O L)).submatrix S τ).rank := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)),
          Fintype.card_fin]
    _ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _

end GlobalTheory.CompanionTheory.Jp
