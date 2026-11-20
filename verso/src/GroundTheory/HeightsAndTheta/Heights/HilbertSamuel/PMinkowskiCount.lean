import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Module Metric
open scoped ENNReal

noncomputable section

namespace MinkowskiCount

section Count

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in

/- English proof (translation)
Establish `h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V)`. Use extensionality with `x`. Simplify using `[and_comm]`. Rewrite using `[h]`. Use `Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_` and prove the remaining obligations.

Rewrite using `[← Submodule.coe_toAddSubgroup]`. Conclude with `AddSubgroup.isClosed_of_discrete`.
-/
theorem finite_latticePoints (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by
  have h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V) := by
    ext x; simp [and_comm]
  rw [h]
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

/- English proof (translation)
The claim follows from `ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne`.
-/
theorem unitBallVolume_pos (R : ℕ) : 0 < unitBallVolume R :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/- English proof (translation)
Rewrite using `[unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage measurableSet_ball.nullMeasurableSet]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem volume_ball_one :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by
  rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage
      measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

/- English proof (translation)
Establish `: MeasurableVAdd La V` using `(inferInstance : MeasurableVAdd La.toAddSubgroup V)`. Establish `: VAddInvariantMeasure La V volume` using `(inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)`. Establish `: Countable La` using `inferInstance`. Use `set S := ball (0 : V) (ρ / 2) with hSdef`. Use `set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef`.

Establish `hS : MeasurableSet S` using `measurableSet_ball`. Establish `key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞)`. Introduce `y`. Use `set T : Set La := {g | (g : V) + y ∈ S} with hTdef`. Establish `h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) = ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g`.

Use `congr 1`. Rewrite using `[h1, ← tsum_subtype]`. Simplify using `only [Pi.one_apply]`. Rewrite using `[ENNReal.tsum_set_one]`. Establish `hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞)`.

Rewrite using `[← (finite_latticePoints La ρ).cast_ncard_eq]`. Both sides reduce to the same expression. Rewrite using `[hA]`. Use `ENat.toENNReal_le.mpr ?_` and prove the remaining obligations. Break down `T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩` into its components or cases.

Simplify using `[hT]`. Use `Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_` and prove the remaining obligations. Introduce `g hg`. Use `⟨La.sub_mem g.2 g₀.2, ?_⟩` and prove the remaining obligations. Establish `hg' : ‖(g : V) + y‖ < ρ / 2` using `by simpa [T, S] using hg`.

Establish `hg₀' : ‖(g₀ : V) + y‖ < ρ / 2` using `by simpa [T, S] using hg₀`. Establish `: (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y)` using `by abel`. Use `show ‖(g : V) - g₀‖ ≤ ρ`. Rewrite using `[this]`. Combine the linear relations using `[norm_sub_le ((g : V) + y) ((g₀ : V) + y)]`.

Introduce `g _ g' _ h`. Conclude with `Subtype.ext (sub_left_injective h)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem volume_ball_half_le (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  have : Countable La := inferInstance
  set S := ball (0 : V) (ρ / 2) with hSdef
  set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef
  have hS : MeasurableSet S := measurableSet_ball
  have key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞) := by
    intro y
    set T : Set La := {g | (g : V) + y ∈ S} with hTdef
    have h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞) := by
      rw [← (finite_latticePoints La ρ).cast_ncard_eq]; rfl
    rw [hA]
    refine ENat.toENNReal_le.mpr ?_
    rcases T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩
    · simp [hT]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hg' : ‖(g : V) + y‖ < ρ / 2 := by simpa [T, S] using hg
      have hg₀' : ‖(g₀ : V) + y‖ < ρ / 2 := by simpa [T, S] using hg₀
      have : (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y) := by abel
      show ‖(g : V) - g₀‖ ≤ ρ
      rw [this]
      linarith [norm_sub_le ((g : V) + y) ((g₀ : V) + y)]
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc volume S = ∫⁻ z, S.indicator 1 z := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, (A.ncard : ℝ≥0∞) := lintegral_mono fun z => key z
    _ = A.ncard * volume F := setLIntegral_const _ _

/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℤ La`. Establish `fund` using `ZLattice.isAddFundamentalDomain b (volume : Measure V)`. Establish `hcov` using `ZLattice.covolume_eq_measure_fundamentalDomain La volume fund`. Establish `hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤` using `(ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne`. Establish `hle` using `volume_ball_half_le La ρ fund`.

Rewrite `hle` using `[Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one]`. Establish `hle'` using `ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle`. Rewrite `hle'` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def, ← hcov]`. Establish `hcpos` using `ZLattice.covolume_pos La volume`. Establish `hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ)`.

Establish `: 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard` using `(Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩`. Conclude with `this` after adjusting the coercions. Establish `hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤ ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ)` using `(div_le_iff₀ hcpos).mpr hle'`. Establish `hlog` using `Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv`. Rewrite `hlog` using `[Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne', Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_count (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La volume fund
  have hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hle := volume_ball_half_le La ρ fund
  rw [Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one] at hle
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def,
    ← hcov] at hle'
  have hcpos := ZLattice.covolume_pos La volume
  have hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
    have : 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard :=
      (Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩
    exact_mod_cast this
  have hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := (div_le_iff₀ hcpos).mpr hle'
  have hlog := Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv
  rw [Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne',
    Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow] at hlog
  linarith

end Count

/- English proof (translation)
Use `set a := 1 / Real.sqrt R with ha_def`. Establish `ha : 0 ≤ a` using `by positivity`. Establish `hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹' (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1`. Introduce `x hx`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx`.

Rewrite using `[mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]`. Break down `Nat.eq_zero_or_pos R with rfl | hR` into its components or cases. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_eq_abs, sq_abs]`.

Conclude with `sq_lt_sq' (hx i).1 (hx i).2`. Use `_ = 1 := by`. Establish `hR' : (0 : ℝ) < R` using `by exact_mod_cast hR`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def, div_pow, one_pow, Real.sq_sqrt hR'.le]`. Clear the denominators using the available nonvanishing facts.

Establish `hvol` using `measure_mono (μ := volume) hsub`. Rewrite `hvol` using `[(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]`. Simplify using `only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol`. Establish `h` using `ENNReal.toReal_mono measure_ball_lt_top.ne hvol`. Rewrite `h` using `[ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]`.

Establish `h2 : 2 / Real.sqrt R = a + a` using `by rw [ha_def]; ring`. Rewrite using `[h2]`. Conclude with `h`.
-/
theorem cube_le_unitBallVolume (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by
  set a := 1 / Real.sqrt R with ha_def
  have ha : 0 ≤ a := by positivity
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹'
      (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin R, a ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hR⟩, Finset.mem_univ _⟩ fun i _ => by
              rw [Real.norm_eq_abs, sq_abs]
              exact sq_lt_sq' (hx i).1 (hx i).2
        _ = 1 := by
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def,
            div_pow, one_pow, Real.sq_sqrt hR'.le]
          field_simp
  have hvol := measure_mono (μ := volume) hsub
  rw [(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    at hvol
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol
  have h := ENNReal.toReal_mono measure_ball_lt_top.ne hvol
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  have h2 : 2 / Real.sqrt R = a + a := by rw [ha_def]; ring
  rw [h2]
  exact h

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ _ _ _ La _ _ ρ hρ => log_count La ρ hρ, cube_le_unitBallVolume⟩`.
-/
theorem proof : MinkowskiCount.Statement :=
  ⟨fun _ _ _ _ _ _ La _ _ ρ hρ => log_count La ρ hρ, cube_le_unitBallVolume⟩

end MinkowskiCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
