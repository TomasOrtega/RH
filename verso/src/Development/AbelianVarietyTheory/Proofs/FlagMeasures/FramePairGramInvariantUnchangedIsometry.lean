import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

/- English proof (translation)
Use `symm`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `a _ ha`. Apply `hg` to reduce the goal to its premises.

Assume the negation of the conclusion as `hlt`. Conclude with `ha (Finset.mem_map.2 ⟨⟨(a : ℕ), Nat.lt_of_not_le hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
private theorem sum_castLE_lemma {M : Type} [AddCommMonoid M] {l N : ℕ} (h : l ≤ N) (g : Fin N → M)
    (hg : ∀ a : Fin N, l ≤ (a : ℕ) → g a = 0) :
    ∑ a, g a = ∑ a : Fin l, g (Fin.castLE h a) := by
  symm
  calc ∑ a : Fin l, g (Fin.castLE h a) = ∑ x ∈ Finset.univ.map (Fin.castLEEmb h), g x :=
        (Finset.sum_map Finset.univ (Fin.castLEEmb h) g).symm
    _ = ∑ a, g a := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        apply hg
        by_contra hlt
        exact ha (Finset.mem_map.2 ⟨⟨(a : ℕ), Nat.lt_of_not_le hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Establish `hz : ∀ i j : Fin N, j < i → U i j = 0` using `fun i j hij => (hU i j).1 hij`. Establish `hz' : ∀ i j : Fin N, j < i → U' i j = 0` using `fun i j hij => (hU' i j).1 hij`. Unfold `leadMinorE`. Distinguish the cases in `h : l ≤ N`. Rewrite using `[dif_pos h, dif_pos h]`.

Establish `key : (U.transpose * Z * U').submatrix (Fin.castLE h) (Fin.castLE h) = (U.submatrix (Fin.castLE h) (Fin.castLE h)).transpose * Z.submatrix (Fin.castLE h) (Fin.castLE h) * U'.submatrix (Fin.castLE h) (Fin.castLE h)`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]`. Rewrite using `[sum_castLE_lemma h]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations.

Rewrite using `[sum_castLE_lemma h]`. Introduce `a ha`. Establish `hi` using `i.isLt`. Rewrite using `[hz a (Fin.castLE h i) (by rw [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]`. Introduce `b hb`.

Establish `hj` using `j.isLt`. Rewrite using `[hz' b (Fin.castLE h j) (by rw [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]`. Establish `t1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id`. Introduce `a b hab`. Conclude with `(hU (Fin.castLE h a) (Fin.castLE h b)).1 hab`.

Establish `t2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id`. Introduce `a b hab`. Conclude with `(hU' (Fin.castLE h a) (Fin.castLE h b)).1 hab`. Establish `d1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular t1]`.

Conclude with `Finset.prod_eq_one (fun a _ => (hU (Fin.castLE h a) (Fin.castLE h a)).2 rfl)`. Establish `d2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular t2]`. Conclude with `Finset.prod_eq_one (fun a _ => (hU' (Fin.castLE h a) (Fin.castLE h a)).2 rfl)`. Rewrite using `[key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, d1, d2, one_mul, mul_one]`.

Rewrite using `[dif_neg h, dif_neg h]`.
-/
theorem leadMinorE_unitri_both {E : Type} [Field E] {N : ℕ} (Z U U' : Matrix (Fin N) (Fin N) E)
    (hU : IsUpUni U) (hU' : IsUpUni U') (l : ℕ) :
    leadMinorE (U.transpose * Z * U') l = leadMinorE Z l := by
  have hz : ∀ i j : Fin N, j < i → U i j = 0 := fun i j hij => (hU i j).1 hij
  have hz' : ∀ i j : Fin N, j < i → U' i j = 0 := fun i j hij => (hU' i j).1 hij
  unfold leadMinorE
  by_cases h : l ≤ N
  · rw [dif_pos h, dif_pos h]
    have key : (U.transpose * Z * U').submatrix (Fin.castLE h) (Fin.castLE h) =
        (U.submatrix (Fin.castLE h) (Fin.castLE h)).transpose * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
          U'.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [sum_castLE_lemma h]
      · refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [sum_castLE_lemma h]
        intro a ha
        have hi := i.isLt
        rw [hz a (Fin.castLE h i) (by rw [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
      · intro b hb
        have hj := j.isLt
        rw [hz' b (Fin.castLE h j) (by rw [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
    have t1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have t2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU' (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have d1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t1]
      exact Finset.prod_eq_one (fun a _ => (hU (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    have d2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t2]
      exact Finset.prod_eq_one (fun a _ => (hU' (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, d1, d2, one_mul, mul_one]
  · rw [dif_neg h, dif_neg h]

/- English proof (translation)
Introduce `D T T' F0 F F0' F' ρ U U' h`. Take `⟨hρ, hU, hU', hF, hF'⟩` from `h`. Establish `hiso : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y` using `hρ`. Establish `hstar : IsUpUni (U.map star)`. Use `fun i j => ⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.map_apply, (hU i j).1 hij, star_zero]`. Rewrite using `[Matrix.map_apply, (hU i j).2 hij, star_one]`. Establish `hZ : Formalism.MainNotions.S.Zhat F.fl F'.fl = (U.map star).transpose * Formalism.MainNotions.S.Zhat F0.fl F0'.fl * U'`. Use extensionality with `a b`. Simplify using `only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]`.

Rewrite using `[← hiso (F.fl.fvec a) (F'.fl.fvec b), hF a, hF' b]`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, frame, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `show Formalism.MainNotions.S.Gflag F.fl F'.fl = Formalism.MainNotions.S.Gflag F0.fl F0'.fl`.

Unfold `Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl`. Rewrite using `[hZ, leadMinorE_unitri_both _ _ _ hstar hU', leadMinorE_unitri_both _ _ _ hstar hU']`.
-/
theorem gval_eq_of_movesTo : ∀ (D : D7) {T T' : D.host.E} (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F F0' F' ρ U U' h
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hiso : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  have hstar : IsUpUni (U.map star) := by
    refine fun i j => ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [Matrix.map_apply, (hU i j).1 hij, star_zero]
    · rw [Matrix.map_apply, (hU i j).2 hij, star_one]
  have hZ : Formalism.MainNotions.S.Zhat F.fl F'.fl = (U.map star).transpose * Formalism.MainNotions.S.Zhat F0.fl F0'.fl * U' := by
    ext a b
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← hiso (F.fl.fvec a) (F'.fl.fvec b), hF a, hF' b]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, frame, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    ring
  show Formalism.MainNotions.S.Gflag F.fl F'.fl = Formalism.MainNotions.S.Gflag F0.fl F0'.fl
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [hZ, leadMinorE_unitri_both _ _ _ hstar hU', leadMinorE_unitri_both _ _ _ hstar hU']

end GlobalTheory.HL
