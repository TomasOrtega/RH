import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobRowIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

/- English proof (translation)
Introduce `l _ K bk τ hτ N d ρ F`. Take `⟨hU, -⟩` from `GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ`. Establish `hφt : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ`. Rewrite using `[frobW_inclW, hτ.1, map_mul]`. Both sides reduce to the same expression.

Establish `he : IsUnit (bk.evW bk.E)`. Establish `h` using `hU.map (frobW l)`. Rewrite `h` using `[hφt]`. Conclude with `isUnit_of_mul_isUnit_left h`. Establish `hdet : IsUnit F.T.det` using `(Matrix.isUnit_iff_isUnit_det _).1 F.unit`.

Establish `hTTi : F.T * F.T⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Establish `hTiT : F.T⁻¹ * F.T = 1` using `Matrix.nonsing_inv_mul _ hdet`. Establish `hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l)` using `fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)`. Establish `h1 : F.T⁻¹.map (frobW l) * F.T.map (frobW l) = 1`. Rewrite using `[← hmapmul, hTiT]`.

Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hAA : F.A.map bk.evW * F.A'.map bk.evW = bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))`. Rewrite using `[← Matrix.map_mul, F.A_mul]`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hφTi : bk.evW bk.E ^ N • F.T⁻¹.map (frobW l) = F.A'.map bk.evW * F.T⁻¹`. Establish `k1 : (bk.evW bk.E ^ N • F.T.map (frobW l)) * F.A'.map bk.evW * F.T⁻¹ = bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))`. Rewrite using `[F.φ, Matrix.mul_assoc F.T, hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTTi]`. Establish `k2` using `congrArg (fun M => F.T⁻¹.map (frobW l) * M) k1`.

Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one] at k2`. Establish `k3 : bk.evW bk.E ^ N • (bk.evW bk.E ^ N • F.T⁻¹.map (frobW l)) = bk.evW bk.E ^ N • (F.A'.map bk.evW * F.T⁻¹)`. Rewrite using `[smul_smul, ← pow_add, show N + N = 2 * N by ring, ← k2]`. Conclude with `(he.pow N).smul_left_cancel.1 k3`. Establish `hY : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T i j = inclW l a`.

Introduce `i`. Use `GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun j => inclW l τ ^ N * F.T i j) (fun k j => bk.ev (F.A k j)) ?_` and prove the remaining obligations. Introduce `j`. Establish `e1` using `congrFun (congrFun F.φ i) j`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1`.

Rewrite using `[map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Both sides reduce to the same expression. Establish `hY' : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T⁻¹ i j = inclW l a`.

Introduce `i j`. Use `GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun k => inclW l τ ^ N * F.T⁻¹ k j) (fun k i => bk.ev (F.A' i k)) ?_ i` and prove the remaining obligations. Introduce `i`. Establish `e1` using `congrFun (congrFun hφTi i) j`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1`.

Rewrite using `[map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (bk.evW (F.A' i k)), mul_assoc]`. Both sides reduce to the same expression. Use `choose Y hYe using hY`.

Use `choose Y' hY'e using hY'`. Use `⟨Matrix.of Y, Matrix.of Y', ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[Matrix.smul_apply, hYe]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Apply `inclW_injective` to reduce the goal to its premises. Establish `e2` using `congrFun (congrFun hTTi i) j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at e2 ⊢`. Simplify using `only [← hYe, ← hY'e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `_ = _ := by rw [e2]; split_ifs <;> simp [map_pow]`.
-/
theorem pre_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ), ∃ Y Y' : Matrix (Fin d) (Fin d) (Ainf l), Y.map (inclW l) = inclW l τ ^ N • F.T ∧ Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ N d ρ F
  classical
  obtain ⟨hU, -⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hφt : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
    rw [frobW_inclW, hτ.1, map_mul]; rfl
  have he : IsUnit (bk.evW bk.E) := by
    have h := hU.map (frobW l)
    rw [hφt] at h
    exact isUnit_of_mul_isUnit_left h
  have hdet : IsUnit F.T.det := (Matrix.isUnit_iff_isUnit_det _).1 F.unit
  have hTTi : F.T * F.T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hTiT : F.T⁻¹ * F.T = 1 := Matrix.nonsing_inv_mul _ hdet
  have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
    fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
  have h1 : F.T⁻¹.map (frobW l) * F.T.map (frobW l) = 1 := by
    rw [← hmapmul, hTiT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hAA : F.A.map bk.evW * F.A'.map bk.evW = bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, F.A_mul]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hφTi : bk.evW bk.E ^ N • F.T⁻¹.map (frobW l) = F.A'.map bk.evW * F.T⁻¹ := by
    have k1 : (bk.evW bk.E ^ N • F.T.map (frobW l)) * F.A'.map bk.evW * F.T⁻¹ =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [F.φ, Matrix.mul_assoc F.T, hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTTi]
    have k2 := congrArg (fun M => F.T⁻¹.map (frobW l) * M) k1
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one] at k2
    have k3 : bk.evW bk.E ^ N • (bk.evW bk.E ^ N • F.T⁻¹.map (frobW l)) =
        bk.evW bk.E ^ N • (F.A'.map bk.evW * F.T⁻¹) := by
      rw [smul_smul, ← pow_add, show N + N = 2 * N by ring, ← k2]
    exact (he.pow N).smul_left_cancel.1 k3
  have hY : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T i j = inclW l a := by
    intro i
    refine GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun j => inclW l τ ^ N * F.T i j)
      (fun k j => bk.ev (F.A k j)) ?_
    intro j
    have e1 := congrFun (congrFun F.φ i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1
    rw [map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]; rfl
  have hY' : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T⁻¹ i j = inclW l a := by
    intro i j
    refine GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun k => inclW l τ ^ N * F.T⁻¹ k j)
      (fun k i => bk.ev (F.A' i k)) ?_ i
    intro i
    have e1 := congrFun (congrFun hφTi i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1
    rw [map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (bk.evW (F.A' i k)), mul_assoc]; rfl
  choose Y hYe using hY
  choose Y' hY'e using hY'
  refine ⟨Matrix.of Y, Matrix.of Y', ?_, ?_⟩
  · ext i j
    simp [Matrix.smul_apply, hYe]
  · refine Matrix.ext fun i j => ?_
    apply inclW_injective
    have e2 := congrFun (congrFun hTTi i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at e2 ⊢
    simp only [← hYe, ← hY'e]
    calc ∑ k, inclW l τ ^ N * F.T i k * (inclW l τ ^ N * F.T⁻¹ k j)
        = inclW l τ ^ (2 * N) * ∑ k, F.T i k * F.T⁻¹ k j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = _ := by rw [e2]; split_ifs <;> simp [map_pow]

end GlobalTheory.BKLim
