import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.DegMoveProof

namespace GlobalTheory.CompanionTheory.DegRightProof

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem frame_right {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ} (x h : GA E n)
    (M : Matrix (Fin n) (Fin k) (Ad E)) :
    h.val * (((x * h)⁻¹ : GA E n).val * M) = (x⁻¹ : GA E n).val * M := by
  rw [← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem degRight_of : MulF → MulI → SzFin → FinSupp → DegRight := by
  intro hF hI hSz hFS E _ _ _ n
  have hb : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), by positivity,
    fun x h W => ?_⟩
  obtain ⟨hLI, -⟩ := lin_basisMat W
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have hY : (N.map (algebraMap E (Ad E)) * (x * h : GA E n).val) *
      (((x * h)⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (x * h : GA E n).val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn h _ _ hY
  rw [frame_right] at hc
  have e1 : deg (x * h) W = degG (x * h) (basisMat W) := rfl
  have e2 : deg x W = degG x (basisMat W) := rfl
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg h.val
  have hS' := logSizeM_nonneg (h⁻¹ : GA E n).val
  have hsz : logSize h = logSizeM h.val + logSizeM (h⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM h.val = S at *
  generalize logSizeM (h⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hpos : 0 ≤ (n : ℝ) * (S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegRightProof

end
