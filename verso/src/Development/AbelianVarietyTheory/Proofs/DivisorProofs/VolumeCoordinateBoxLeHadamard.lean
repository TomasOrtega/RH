import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
open MeasureTheory

namespace GlobalTheory.CoordBox

/- English proof (translation)
Use `set n := Fintype.card K with hn`. Set `o : OrthonormalBasis K ℝ V` to `(stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hK).symm`. Set `v : K → V` to `fun k => (2 * t) • w k`. Set `a : V` to `-∑ k, t • w k`. Establish `hsub : {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} ⊆ (fun x => x + a) '' parallelepiped v`.

Introduce and unpack `y ⟨c, hc, rfl⟩`. Use `set s : K → ℝ := fun k => (c k + t) / (2 * t) with hs`. Establish `hkey : ∀ k, s k * (2 * t) = c k + t`. Introduce `k`. Break down `ht.eq_or_lt with h0 | hpos` into its components or cases.

Establish `hck : c k = 0`. Use `hc k` as an intermediate fact. Rewrite `this` using `[← h0]`. Conclude with `abs_nonpos_iff.mp this`. Simplify using `[hs, ← h0, hck]`.

Simplify using `only [hs]`. Clear the denominators using the available nonvanishing facts. Use `⟨∑ k, s k • v k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_parallelepiped_iff]`. Use `⟨s, ?_, rfl⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `k`. Establish `h1` using `(abs_le.mp (hc k)).1`. Conclude with `div_nonneg (by linarith) (by linarith)`. Introduce `k`.

Establish `h2` using `(abs_le.mp (hc k)).2`. Conclude with `div_le_one_of_le₀ (by linarith) (by linarith)`. Simplify using `only [v, a, smul_smul, hkey, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Establish `hvol : volume (parallelepiped v) = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|)`.

Rewrite using `[← o.addHaar_eq_volume, MeasureTheory.Measure.addHaar_parallelepiped]`. Use `congr 1`. Establish `hsm : o.toBasis.det v = (∏ _k : K, (2 * t)) • o.toBasis.det w` using `o.toBasis.det.toMultilinearMap.map_smul_univ (fun _ => 2 * t) w`. Rewrite using `[hsm, Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * t)]`. Establish `hdet : |o.toBasis.det w| ≤ ∏ k, ‖w k‖`.

Use `GlobalTheory.Hadamard.norm_orthonormalBasis_det_le (𝕜 := ℝ) o w` as an intermediate fact. Simplify `this` using `[Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.image_add_right, measure_preimage_add_right]`. Use `_ = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := hvol`.

Use `_ ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left hdet (pow_nonneg (by linarith) _)`.
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
