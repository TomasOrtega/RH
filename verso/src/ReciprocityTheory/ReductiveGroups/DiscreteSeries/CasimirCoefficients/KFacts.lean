import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFactsA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

instance kf_isHaar (ε : Fin n → Bool) : (muK ε).IsHaarMeasure := by
  unfold muK; infer_instance

/- English proof (translation)
Establish `hc : IsCompact (Kset ε)`. Establish `hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1))`. Introduce `g hg i _ j _`. Simplify `entry_norm_bound_of_unitary hg.1 i j` using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `(isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_Kset ε) hsub`.

Establish `hK : IsCompact ((KG ε : Set (UJ ε)))` using `(isClosedEmbedding_toM ε).isCompact_preimage hc`. Conclude with `isCompact_iff_compactSpace.mp hK`.
-/
theorem compactSpace_KG (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hc : IsCompact (Kset ε) := by
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hg.1 i j
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_Kset ε) hsub
  have hK : IsCompact ((KG ε : Set (UJ ε))) :=
    (isClosedEmbedding_toM ε).isCompact_preimage hc
  exact isCompact_iff_compactSpace.mp hK

/- English proof (translation)
Use `haveI := compactSpace_KG ε`. Unfold `muK`. Conclude with `ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ Set.univ_nonempty) (isCompact_univ.measure_lt_top).ne`.
-/
theorem muK_univ_pos (ε : Fin n → Bool) : 0 < (muK ε Set.univ).toReal := by
  haveI := compactSpace_KG ε
  unfold muK
  exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    (isCompact_univ.measure_lt_top).ne

/- English proof (translation)
Use `compactSpace_KG ε` as an intermediate fact. Use `⟨fun k => ?_⟩` and prove the remaining obligations. Use `set ν := Measure.map (fun x => x * k) (muK ε) with hν`. Establish `: IsFiniteMeasure (muK ε)` using `⟨isCompact_univ.measure_lt_top⟩`. Establish `: IsFiniteMeasure ν` using `Measure.isFiniteMeasure_map _ _`.

Establish `h` using `Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)`. Establish `hu : ν Set.univ = muK ε Set.univ`. Rewrite using `[hν, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ]`. Establish `hpos : muK ε Set.univ ≠ 0` using `(isOpen_univ.measure_pos (muK ε) Set.univ_nonempty).ne'`. Establish `htop : muK ε Set.univ ≠ ⊤` using `(isCompact_univ.measure_lt_top).ne`.

Rewrite `hu` using `[h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `hc : (Measure.haarScalarFactor ν (muK ε) : ℝ≥0∞) = 1`. Use `(ENNReal.mul_eq_right hpos htop).mp hu` as an intermediate fact. Conclude with `this`. Rewrite using `[h, ENNReal.coe_eq_one.mp hc, one_smul]`.
-/
theorem muK_rightInvariant (ε : Fin n → Bool) : (muK ε).IsMulRightInvariant := by
  have := compactSpace_KG ε
  refine ⟨fun k => ?_⟩
  set ν := Measure.map (fun x => x * k) (muK ε) with hν
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have hu : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ]
  have hpos : muK ε Set.univ ≠ 0 := (isOpen_univ.measure_pos (muK ε) Set.univ_nonempty).ne'
  have htop : muK ε Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  have hc : (Measure.haarScalarFactor ν (muK ε) : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_eq_right hpos htop).mp hu
    exact this
  rw [h, ENNReal.coe_eq_one.mp hc, one_smul]

/- English proof (translation)
Conclude with `⟨kfaKG ε hY, kfa_continuous ε hY, kfa_toMK ε hY, kfa_add ε hY⟩`.
-/
theorem exists_oneParam (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ∃ γ : ℝ → KG ε, Continuous γ ∧ (∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) ∧
      ∀ s t, γ (s + t) = γ s * γ t := by
  exact ⟨kfaKG ε hY, kfa_continuous ε hY, kfa_toMK ε hY, kfa_add ε hY⟩

/- English proof (translation)
Unfold `inK IsBlock inG`. Establish `hJJ : Jm ε * Jm ε = 1`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hcomm : Y * Jm ε = Jm ε * Y ↔ ∀ a b, ε a ≠ ε b → Y a b = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h a b hab`.

Establish `h1` using `congrFun (congrFun h a) b`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1`. Apply the tactic sequence `have hdb : (if ε b then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Establish `hda : (if ε a then (1 : ℂ) else -1) = -(if ε b then (1 : ℂ) else -1)`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all`.

Rewrite `h1` using `[hda]`. Establish `h5 : 2 * (Y a b * (if ε b then (1 : ℂ) else -1)) = 0` using `by linear_combination h1`. Conclude with `(mul_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left two_ne_zero)).resolve_right hdb`. Introduce `h`. Use extensionality with `a b`.

Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hab : ε a = ε b`. Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h a b hab]`.

Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, hcomm.mp h2⟩` and prove the remaining obligations. Establish `h3 : Yᴴ * Jm ε = -(Y * Jm ε)`.

Rewrite using `[h2]`. Conclude with `eq_neg_of_add_eq_zero_left h1`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨h1, h2⟩`. Establish `h4` using `hcomm.mpr h2`.

Use `⟨?_, h4⟩` and prove the remaining obligations. Rewrite using `[h1, Matrix.neg_mul, h4, neg_add_cancel]`.
-/
theorem inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  unfold inK IsBlock inG
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hcomm : Y * Jm ε = Jm ε * Y ↔ ∀ a b, ε a ≠ ε b → Y a b = 0 := by
    constructor
    · intro h a b hab
      have h1 := congrFun (congrFun h a) b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      have hdb : (if ε b then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      have hda : (if ε a then (1 : ℂ) else -1) = -(if ε b then (1 : ℂ) else -1) := by
        cases ha : ε a <;> cases hb : ε b <;> simp_all
      rw [hda] at h1
      have h5 : 2 * (Y a b * (if ε b then (1 : ℂ) else -1)) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left two_ne_zero)).resolve_right hdb
    · intro h
      ext a b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hab : ε a = ε b
      · rw [hab]
        ring
      · rw [h a b hab]
        ring
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, hcomm.mp h2⟩
    have h3 : Yᴴ * Jm ε = -(Y * Jm ε) := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(Y * Jm ε) * Jm ε := by rw [h3]
      _ = -Y := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  · rintro ⟨h1, h2⟩
    have h4 := hcomm.mpr h2
    refine ⟨?_, h4⟩
    rw [h1, Matrix.neg_mul, h4, neg_add_cancel]

end ReciprocityTheory.ChartRestriction.DS.S7
