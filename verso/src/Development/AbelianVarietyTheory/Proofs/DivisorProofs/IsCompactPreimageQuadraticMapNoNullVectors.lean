import Mathlib
open Matrix Polynomial

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

/- English proof (translation)
Use `haveI : ProperSpace (Matrix (Fin m) (Fin m) K) := FiniteDimensional.proper K _`. Take `⟨c₀, hc₀⟩` from `NormedField.exists_one_lt_norm K`. Establish `hc₀pos : 0 < ‖c₀‖` using `lt_trans one_pos hc₀`. Take `⟨R, hR⟩` from `hQ.isBounded.subset_closedBall 0`. Use `set Sh : Set (Matrix (Fin m) (Fin m) K) := (S : Set _) ∩ {w | 1 / ‖c₀‖ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hShdef`.

Establish `hSclosed : IsClosed (S : Set (Matrix (Fin m) (Fin m) K))` using `Submodule.closed_of_finiteDimensional S`. Establish `hShc : IsCompact Sh`. Use `(isCompact_closedBall (0 : Matrix (Fin m) (Fin m) K) 1).of_isClosed_subset ?_ ?_` and prove the remaining obligations. Use `hSclosed.inter ?_` and prove the remaining obligations. Conclude with `(isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)`.

Introduce `w hw`. Simplify `hw.2.2` using `[Metric.mem_closedBall, dist_zero_right]`. Establish `hresc : ∀ w ∈ S, w ≠ 0 → ∃ d : K, d ≠ 0 ∧ d • w ∈ Sh ∧ ‖d • w‖ < 1`. Introduce `w hwS hw0`. Take `⟨d, hd0, hlt, hge, -⟩` from `rescale_to_shell hc₀ one_pos hw0`.

Conclude with `⟨d, hd0, ⟨S.smul_mem d hwS, hge, hlt.le⟩, hlt⟩`. Distinguish the cases in `hne : Sh.Nonempty`. Take `⟨w₀, hw₀, hmin⟩` from `hShc.exists_isMinOn hne (f := fun w => ‖q w‖) (continuous_norm.comp hq).continuousOn set μ := ‖q w₀‖ with hμ`. Establish `hμpos : 0 < μ`. Rewrite using `[hμ, norm_pos_iff]`.

Introduce `h0`. Use `hnull w₀ hw₀.1 h0` as an intermediate fact. Establish `h1` using `hw₀.2.1`. Rewrite `h1` using `[this, norm_zero]`. Conclude with `absurd h1 (not_le.mpr (by positivity))`.

Use `⟨Metric.closedBall 0 (max 1 (R / μ)), isCompact_closedBall _ _, ?_⟩` and prove the remaining obligations. Introduce `w hwS hwQ`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Distinguish the cases in `hw0 : w = 0`. Rewrite using `[hw0, norm_zero]`.

Conclude with `le_trans zero_le_one (le_max_left _ _)`. Take `⟨d, hd0, hdSh, hdlt⟩` from `hresc w hwS hw0`. Establish `hqw : ‖q w‖ ≤ R`. Use `hR hwQ` as an intermediate fact. Rewrite `this` using `[Metric.mem_closedBall, dist_zero_right]`. Then use the resulting hypothesis.

Establish `hmu_le : μ ≤ ‖d‖ ^ 2 * ‖q w‖`. Establish `h` using `isMinOn_iff.mp hmin _ hdSh`. Rewrite `h` using `[hhom, norm_smul, norm_mul, hstar]`. Use polynomial arithmetic with `[h]`. Establish `hdw : ‖d‖ * ‖w‖ < 1` using `by rwa [norm_smul] at hdlt`.

Establish `hd2 : ‖d‖ ^ 2 * ‖w‖ ^ 2 ≤ 1`. Establish `h0 : 0 ≤ ‖d‖ * ‖w‖` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `key : μ * ‖w‖ ^ 2 ≤ R`. Establish `hq0 : 0 ≤ ‖q w‖` using `norm_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `h1 : ‖w‖ ≤ 1`. Conclude with `le_trans h1 (le_max_left _ _)`. Use `push_neg at h1`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations.

Rewrite using `[le_div_iff₀ hμpos]`. Establish `h2 : ‖w‖ * μ ≤ ‖w‖ ^ 2 * μ`. Apply `mul_le_mul_of_nonneg_right _ hμpos.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨{0}, isCompact_singleton, ?_⟩` and prove the remaining obligations. Introduce `w hwS _`. Assume the negation of the conclusion as `hw0`. Take `⟨d, -, hdSh, -⟩` from `hresc w hwS hw0`. Conclude with `hne ⟨_, hdSh⟩`.
-/
theorem quadratic_preimage_compact_on_subspace
    (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K]
    (hstar : ∀ x : K, ‖star x‖ = ‖x‖) (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K))
    (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K) (hq : Continuous q)
    (hhom : ∀ (c : K) w, q (c • w) = (c * star c) • q w) (hnull : ∀ w ∈ S, q w = 0 → w = 0)
    (Q : Set (Matrix (Fin m) (Fin m) K)) (hQ : IsCompact Q) :
    ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by
  haveI : ProperSpace (Matrix (Fin m) (Fin m) K) := FiniteDimensional.proper K _
  obtain ⟨c₀, hc₀⟩ := NormedField.exists_one_lt_norm K
  have hc₀pos : 0 < ‖c₀‖ := lt_trans one_pos hc₀
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall 0
  set Sh : Set (Matrix (Fin m) (Fin m) K) :=
    (S : Set _) ∩ {w | 1 / ‖c₀‖ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hShdef
  have hSclosed : IsClosed (S : Set (Matrix (Fin m) (Fin m) K)) :=
    Submodule.closed_of_finiteDimensional S
  have hShc : IsCompact Sh := by
    refine (isCompact_closedBall (0 : Matrix (Fin m) (Fin m) K) 1).of_isClosed_subset ?_ ?_
    · refine hSclosed.inter ?_
      exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw
      simpa [Metric.mem_closedBall, dist_zero_right] using hw.2.2

  have hresc : ∀ w ∈ S, w ≠ 0 → ∃ d : K, d ≠ 0 ∧ d • w ∈ Sh ∧ ‖d • w‖ < 1 := by
    intro w hwS hw0
    obtain ⟨d, hd0, hlt, hge, -⟩ := rescale_to_shell hc₀ one_pos hw0
    exact ⟨d, hd0, ⟨S.smul_mem d hwS, hge, hlt.le⟩, hlt⟩
  by_cases hne : Sh.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hShc.exists_isMinOn hne
      (f := fun w => ‖q w‖) (continuous_norm.comp hq).continuousOn
    set μ := ‖q w₀‖ with hμ
    have hμpos : 0 < μ := by
      rw [hμ, norm_pos_iff]
      intro h0
      have := hnull w₀ hw₀.1 h0
      have h1 := hw₀.2.1
      rw [this, norm_zero] at h1
      exact absurd h1 (not_le.mpr (by positivity))
    refine ⟨Metric.closedBall 0 (max 1 (R / μ)), isCompact_closedBall _ _, ?_⟩
    intro w hwS hwQ
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hw0 : w = 0
    · rw [hw0, norm_zero]; exact le_trans zero_le_one (le_max_left _ _)
    obtain ⟨d, hd0, hdSh, hdlt⟩ := hresc w hwS hw0
    have hqw : ‖q w‖ ≤ R := by
      have := hR hwQ
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hmu_le : μ ≤ ‖d‖ ^ 2 * ‖q w‖ := by
      have h := isMinOn_iff.mp hmin _ hdSh
      rw [hhom, norm_smul, norm_mul, hstar] at h
      nlinarith [h]
    have hdw : ‖d‖ * ‖w‖ < 1 := by rwa [norm_smul] at hdlt
    have hd2 : ‖d‖ ^ 2 * ‖w‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖d‖ * ‖w‖ := by positivity
      nlinarith
    have key : μ * ‖w‖ ^ 2 ≤ R := by
      have hq0 : 0 ≤ ‖q w‖ := norm_nonneg _
      calc μ * ‖w‖ ^ 2 ≤ ‖d‖ ^ 2 * ‖q w‖ * ‖w‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hmu_le (by positivity)
        _ = (‖d‖ ^ 2 * ‖w‖ ^ 2) * ‖q w‖ := by ring
        _ ≤ 1 * ‖q w‖ := mul_le_mul_of_nonneg_right hd2 hq0
        _ ≤ R := by linarith
    by_cases h1 : ‖w‖ ≤ 1
    · exact le_trans h1 (le_max_left _ _)
    · push_neg at h1
      refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hμpos]
      have h2 : ‖w‖ * μ ≤ ‖w‖ ^ 2 * μ := by
        apply mul_le_mul_of_nonneg_right _ hμpos.le
        nlinarith
      linarith
  · refine ⟨{0}, isCompact_singleton, ?_⟩
    intro w hwS _
    by_contra hw0
    obtain ⟨d, -, hdSh, -⟩ := hresc w hwS hw0
    exact hne ⟨_, hdSh⟩

end GlobalTheory
