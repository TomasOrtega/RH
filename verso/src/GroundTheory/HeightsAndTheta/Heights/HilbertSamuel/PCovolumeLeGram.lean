import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

/- English proof (translation)
Introduce `n L _ _ ι _ _ x hxL hx hcard`. Establish `hcard' : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin n))`. Rewrite using `[hcard, finrank_euclideanSpace_fin]`. Set `B : Basis ι ℝ (EuclideanSpace ℝ (Fin n))` to `basisOfLinearIndependentOfCardEqFinrank' x hx hcard'`. Establish `hB : ⇑B = x` using `coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _`.

Establish `hML : Submodule.span ℤ (Set.range B) ≤ L` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; rw [hB]; exact hxL i)`. Establish `hcovM : ZLattice.covolume (Submodule.span ℤ (Set.range B)) = Real.sqrt (Matrix.gram ℝ x).det`. Rewrite using `[GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram _ (B.restrictScalars ℤ)]`. Use `congr 3`. Use function extensionality and compare the values at `i`.

Simplify using `[Basis.restrictScalars_apply, hB]`. Establish `hdiv` using `ZLattice.covolume_div_covolume_eq_relIndex' _ L hML`. Establish `hposM` using `ZLattice.covolume_pos (Submodule.span ℤ (Set.range B))`. Establish `hposL` using `ZLattice.covolume_pos L`. Establish `hne : (Submodule.span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0`.

Introduce `h`. Rewrite `hdiv` using `[h, Nat.cast_zero]`. Conclude with `(div_pos hposM hposL).ne' hdiv`. Establish `h1 : (1 : ℝ) ≤ ZLattice.covolume (Submodule.span ℤ (Set.range B)) / ZLattice.covolume L`. Rewrite using `[hdiv]`.

Conclude with `Nat.one_le_iff_ne_zero.2 hne` after adjusting the coercions. Rewrite using `[← hcovM]`. Rewrite `h1` using `[le_div_iff₀ hposL, one_mul]`. Then use the resulting hypothesis.
-/
theorem CovolumeLeGram.proof : CovolumeLeGram.Statement := by
  intro n L _ _ ι _ _ x hxL hx hcard
  have hcard' : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hcard, finrank_euclideanSpace_fin]
  let B : Basis ι ℝ (EuclideanSpace ℝ (Fin n)) := basisOfLinearIndependentOfCardEqFinrank' x hx hcard'
  have hB : ⇑B = x := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hML : Submodule.span ℤ (Set.range B) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; rw [hB]; exact hxL i)
  have hcovM : ZLattice.covolume (Submodule.span ℤ (Set.range B)) = Real.sqrt (Matrix.gram ℝ x).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram _ (B.restrictScalars ℤ)]
    congr 3
    funext i
    simp [Basis.restrictScalars_apply, hB]
  have hdiv := ZLattice.covolume_div_covolume_eq_relIndex' _ L hML
  have hposM := ZLattice.covolume_pos (Submodule.span ℤ (Set.range B))
  have hposL := ZLattice.covolume_pos L
  have hne : (Submodule.span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hdiv
    exact (div_pos hposM hposL).ne' hdiv
  have h1 : (1 : ℝ) ≤ ZLattice.covolume (Submodule.span ℤ (Set.range B)) / ZLattice.covolume L := by
    rw [hdiv]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  rw [← hcovM]
  rwa [le_div_iff₀ hposL, one_mul] at h1

end GroundTheory.Heights₂.Heights.HilbertSamuel
