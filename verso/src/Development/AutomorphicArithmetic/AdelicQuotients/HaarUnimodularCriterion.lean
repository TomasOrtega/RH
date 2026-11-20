import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal NNReal

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c : ℝ≥0, μ.inv = c • μ` from `⟨Measure.haarScalarFactor μ.inv μ, Measure.isMulLeftInvariant_eq_smul _ _⟩`. Establish `hinv : μ.inv.inv = μ` using `Measure.inv_inv μ`. Establish `hsq : μ = (c * c) • μ`. Combine the equalities or inequalities in the displayed calculation. Establish `K : TopologicalSpace.PositiveCompacts G` using `Classical.arbitrary _`.

Establish `hpos : μ K ≠ 0` using `((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le (measure_mono interior_subset)).ne'`. Establish `hfin : μ K ≠ ∞` using `K.isCompact.measure_lt_top.ne`. Establish `h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K`. Rewrite using `[one_mul]`. Use `conv_rhs => rw [hsq]`.

Simplify using the standard rewrite rules. Establish `h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hpos hfin).1 h3`. Establish `h5 : c = 1`. Rewrite `h4` using `[ENNReal.coe_eq_one, ← pow_two]`. Conclude with `(pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4`.

Rewrite using `[hc, h5, one_smul]`.
-/
private theorem haar_inv_eq_self {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.inv = μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.inv = c • μ :=
    ⟨Measure.haarScalarFactor μ.inv μ, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hinv : μ.inv.inv = μ := Measure.inv_inv μ
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := hinv.symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by simp only [Measure.inv_def, Measure.map_smul]
      _ = c • (c • μ) := by rw [hc]
      _ = (c * c) • μ := by rw [smul_smul]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hpos : μ K ≠ 0 :=
    ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [hsq]
    simp
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one, ← pow_two] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ hμ`. Establish `key : μ.IsMulRightInvariant → Uni μ` using `fun hr => ⟨hμ, ⟨haar_inv_eq_self μ⟩⟩`. Use `⟨key, fun hcomm => key ⟨fun g => ?_⟩⟩` and prove the remaining obligations. Establish `h : (fun x : G => x * g) = fun x => g * x` using `funext fun x => hcomm x g`. Rewrite using `[h]`.

Conclude with `map_mul_left_eq_self μ g`.
-/
theorem UpperTheory.haar_unimodular_criterion :
    UniOf := by
  intro G _ _ _ _ _ _ _ _ μ hμ
  have key : μ.IsMulRightInvariant → Uni μ := fun hr => ⟨hμ, ⟨haar_inv_eq_self μ⟩⟩
  refine ⟨key, fun hcomm => key ⟨fun g => ?_⟩⟩
  have h : (fun x : G => x * g) = fun x => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g
