import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UniChange

/- English proof (translation)
Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `c hc`. Apply `hf` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`.

Conclude with `hc ⟨⟨c.val, by omega⟩, rfl⟩`.
-/
theorem sum_castLE {R : Type} [AddCommMonoid R] {l N : ℕ} (h : l ≤ N) (f : Fin N → R)
    (hf : ∀ c : Fin N, l ≤ c.val → f c = 0) :
    ∑ c, f c = ∑ i : Fin l, f (Fin.castLE h i) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro c hc
  apply hf
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, rfl⟩

/- English proof (translation)
Unfold `leadMinorE`. Use `split_ifs with h`. Use `set e := Fin.castLE h with he`. Establish `hsub : (L * Z * A).submatrix e e = L.submatrix e e * Z.submatrix e e * A.submatrix e e`. Use extensionality with `i j`.

Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[sum_castLE h]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[sum_castLE h]`.

Introduce `c hc`. Rewrite using `[hL0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), zero_mul]`. Introduce `d hd`. Rewrite using `[hA0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), mul_zero]`. Establish `hLd : (L.submatrix e e).det = 1`.

Rewrite using `[Matrix.det_of_lowerTriangular]`. Conclude with `Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hL1 _)`. Introduce `i j hij`. Simplify using `only [Matrix.submatrix_apply]`. Apply `hL0` to reduce the goal to its premises.

Rewrite using `[Fin.lt_def]`. Conclude with `(show (i:ℕ) < j from OrderDual.toDual_lt_toDual.mp hij)`. Establish `hAd : (A.submatrix e e).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular]`. Conclude with `Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hA1 _)`.

Introduce `i j hij`. Simplify using `only [Matrix.submatrix_apply]`. Apply `hA0` to reduce the goal to its premises. Rewrite using `[Fin.lt_def]`. Conclude with `(show (j:ℕ) < i from hij)`.

Rewrite using `[hsub, Matrix.det_mul, Matrix.det_mul, hLd, hAd, one_mul, mul_one]`. Both sides reduce to the same expression.
-/
theorem leadMinorE_mul_uni {K : Type} [Field K] {N : ℕ} (L Z A : Matrix (Fin N) (Fin N) K)
    (hL0 : ∀ a b : Fin N, a < b → L a b = 0) (hL1 : ∀ a : Fin N, L a a = 1)
    (hA0 : ∀ a b : Fin N, b < a → A a b = 0) (hA1 : ∀ a : Fin N, A a a = 1) (l : ℕ) :
    leadMinorE (L * Z * A) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · set e := Fin.castLE h with he
    have hsub : (L * Z * A).submatrix e e =
        L.submatrix e e * Z.submatrix e e * A.submatrix e e := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [sum_castLE h]
      · refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        rw [sum_castLE h]
        intro c hc
        rw [hL0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), zero_mul]
      · intro d hd
        rw [hA0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), mul_zero]
    have hLd : (L.submatrix e e).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hL1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hL0
        rw [Fin.lt_def]
        exact (show (i:ℕ) < j from OrderDual.toDual_lt_toDual.mp hij)
    have hAd : (A.submatrix e e).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hA1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hA0
        rw [Fin.lt_def]
        exact (show (j:ℕ) < i from hij)
    rw [hsub, Matrix.det_mul, Matrix.det_mul, hLd, hAd, one_mul, mul_one]
  · rfl

end GlobalTheory.UniChange

open GlobalTheory.UniChange in
/- English proof (translation)
Introduce `D T T' F G F' G' A A' hA hA' hZ`. Establish `key : ∀ l, leadMinorE (ZhatL G G') l = leadMinorE (ZhatL F F') l`. Introduce `l`. Rewrite using `[hZ]`. Use `leadMinorE_mul_uni _ _ _ ?_ ?_ hA'.1 hA'.2 l` and prove the remaining obligations.

Introduce `a b hab`. Simplify using `[Matrix.map_apply, Matrix.transpose_apply, hA.1 b a hab]`. Introduce `a`. Simplify using `[Matrix.map_apply, Matrix.transpose_apply, hA.2 a]`. Establish `k1` using `key (D.R.rS + 1)`.

Establish `k2` using `key D.R.rS`. Simplify using `only [Gval, Gflag, Dl]`. Simplify using `only [ZhatL] at k1 k2`. Rewrite using `[k1, k2]`.
-/
theorem GlobalTheory.LocOver.gval_uni_change : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Uni A' → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' → Gval G G' = Gval F F' := by
  intro D T T' F G F' G' A A' hA hA' hZ
  have key : ∀ l, leadMinorE (ZhatL G G') l = leadMinorE (ZhatL F F') l := by
    intro l
    rw [hZ]
    refine leadMinorE_mul_uni _ _ _ ?_ ?_ hA'.1 hA'.2 l
    · intro a b hab
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 b a hab]
    · intro a
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 a]
  have k1 := key (D.R.rS + 1)
  have k2 := key D.R.rS
  simp only [Gval, Gflag, Dl]
  simp only [ZhatL] at k1 k2
  rw [k1, k2]
