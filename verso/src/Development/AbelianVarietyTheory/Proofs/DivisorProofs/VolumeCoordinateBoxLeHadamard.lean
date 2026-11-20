import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
open MeasureTheory

namespace GlobalTheory.CoordBox

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem volume_coordBox_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (K : Type) [Fintype K]
    (w : K → V) (t : ℝ) (ht : 0 ≤ t) (hK : Fintype.card K = Module.finrank ℝ V) :
    MeasureTheory.volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
  classical
  set n := Fintype.card K with hn
  let o : OrthonormalBasis K ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hK).symm
  let v : K → V := fun k => (2 * t) • w k
  let a : V := -∑ k, t • w k
  have hsub : {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ⊆ (fun x => x + a) '' parallelepiped v := by
    rintro y ⟨c, hc, rfl⟩
    set s : K → ℝ := fun k => (c k + t) / (2 * t) with hs
    have hkey : ∀ k, s k * (2 * t) = c k + t := by
      intro k
      rcases ht.eq_or_lt with h0 | hpos
      · have hck : c k = 0 := by
          have := hc k
          rw [← h0] at this
          exact abs_nonpos_iff.mp this
        simp [hs, ← h0, hck]
      · simp only [hs]
        field_simp
    refine ⟨∑ k, s k • v k, ?_, ?_⟩
    · rw [mem_parallelepiped_iff]
      refine ⟨s, ?_, rfl⟩
      constructor
      · intro k
        have h1 := (abs_le.mp (hc k)).1
        exact div_nonneg (by linarith) (by linarith)
      · intro k
        have h2 := (abs_le.mp (hc k)).2
        exact div_le_one_of_le₀ (by linarith) (by linarith)
    · simp only [v, a, smul_smul, hkey, add_smul, Finset.sum_add_distrib]
      abel
  have hvol : volume (parallelepiped v) = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := by
    rw [← o.addHaar_eq_volume, MeasureTheory.Measure.addHaar_parallelepiped]
    congr 1
    have hsm : o.toBasis.det v = (∏ _k : K, (2 * t)) • o.toBasis.det w :=
      o.toBasis.det.toMultilinearMap.map_smul_univ (fun _ => 2 * t) w
    rw [hsm, Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * t)]
  have hdet : |o.toBasis.det w| ≤ ∏ k, ‖w k‖ := by
    have := GlobalTheory.Hadamard.norm_orthonormalBasis_det_le (𝕜 := ℝ) o w
    simpa [Real.norm_eq_abs] using this
  calc volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ≤ volume ((fun x => x + a) '' parallelepiped v) := measure_mono hsub
    _ = volume (parallelepiped v) := by
        rw [Set.image_add_right, measure_preimage_add_right]
    _ = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := hvol
    _ ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hdet (pow_nonneg (by linarith) _)

end GlobalTheory.CoordBox
