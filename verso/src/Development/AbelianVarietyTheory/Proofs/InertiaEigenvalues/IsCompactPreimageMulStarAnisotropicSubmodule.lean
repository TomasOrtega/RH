import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ hU r V hV B hB`. Use `letI : NormedAddCommGroup (Matrix (Fin r) (Fin r) E) := Matrix.normedAddCommGroup`. Use `letI : NormedSpace E (Matrix (Fin r) (Fin r) E) := Matrix.normedSpace`. Use `haveI : LocallyCompactSpace E := hU.lcE`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`.

Use `haveI : ProperSpace (Matrix (Fin r) (Fin r) E) := FiniteDimensional.proper E _`. Establish `hsE : Continuous (star : E → E)` using `AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1 (fun x => by simp [hU.norm_star])`. Use `haveI : ContinuousStar E := ⟨hsE⟩`. Establish `hQc : Continuous fun z : Matrix (Fin r) (Fin r) E => z * star z` using `continuous_id.mul continuous_star`. Establish `hQs : ∀ (d : E) (z : Matrix (Fin r) (Fin r) E), (d • z) * star (d • z) = (d * star d) • (z * star z)`.

Introduce `d z`. Rewrite using `[star_smul, smul_mul_smul_comm]`. Establish `hnd : ∀ d : E, ‖d * star d‖ = ‖d‖ ^ 2`. Introduce `d`. Rewrite using `[norm_mul, hU.norm_star, sq]`.

Establish `hVc : IsClosed (V : Set (Matrix (Fin r) (Fin r) E))` using `Submodule.closed_of_finiteDimensional V`. Take `⟨k, hk⟩` from `NormedField.exists_one_lt_norm E`. Use `set A : Set (Matrix (Fin r) (Fin r) E) := {w | w ∈ V ∧ ‖k‖⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hA`. Establish `hAc : IsCompact A`. Apply `Metric.isCompact_of_isClosed_isBounded` to reduce the goal to its premises.

Conclude with `hVc.inter ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))`. Conclude with `(Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := 1)).subset (fun w hw => by simpa using hw.2.2)`. Establish `hkpos : 0 < ‖k‖⁻¹` using `inv_pos.mpr (lt_trans one_pos hk)`. Establish `hA0 : ∀ w ∈ A, 0 < ‖w * star w‖`. Introduce `w hw`.

Apply `norm_pos_iff.mpr` to reduce the goal to its premises. Introduce `h0`. Use `hV w hw.1 h0` as an intermediate fact. Establish `h1` using `hw.2.1`. Rewrite `h1` using `[this, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ A, c ≤ ‖w * star w‖ := by`. Break down `A.eq_empty_or_nonempty with he | hne` into its components or cases. Conclude with `⟨1, one_pos, by simp [he]⟩`. Take `⟨w₀, hw₀, hmin⟩` from `hAc.exists_isMinOn hne (hQc.norm.continuousOn)`.

Conclude with `⟨_, hA0 w₀ hw₀, fun w hw => hmin hw⟩`. Take `⟨R, hR⟩` from `(hB.isBounded).subset_closedBall 0`. Apply `Metric.isCompact_of_isClosed_isBounded` to reduce the goal to its premises. Conclude with `hVc.inter (hB.isClosed.preimage hQc)`. Apply `(Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := Real.sqrt (|R| / c))).subset` to reduce the goal to its premises.

Introduce `z hz`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Establish `hQR : ‖z * star z‖ ≤ |R|`. Use `hR hz.2` as an intermediate fact. Rewrite `this` using `[Metric.mem_closedBall, dist_zero_right]`.

Conclude with `this.trans (le_abs_self R)`. Distinguish the cases in `hz0 : z = 0`. Rewrite using `[hz0, norm_zero]`. Conclude with `Real.sqrt_nonneg _`. Take `⟨d, hd0, hd1, hd2, -⟩` from `rescale_to_shell hk one_pos hz0`.

Establish `hdA : d • z ∈ A` using `⟨V.smul_mem d hz.1, by simpa using hd2, hd1.le⟩`. Establish `h1` using `hc _ hdA`. Rewrite `h1` using `[hQs, norm_smul, hnd]`. Rewrite `hd1` using `[norm_smul]`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises.

Rewrite using `[le_div_iff₀ hc0]`. Establish `hzpos : 0 < ‖z‖` using `norm_pos_iff.mpr hz0`. Establish `hdpos : 0 < ‖d‖` using `norm_pos_iff.mpr hd0`. Establish `hdz : (‖d‖ * ‖z‖) ^ 2 ≤ 1`. Establish `: 0 ≤ ‖d‖ * ‖z‖` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hQ0 : 0 ≤ ‖z * star z‖` using `norm_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]`.
-/
theorem mul_star_anisotropic_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  intro F E _ _ _ _ hU r V hV B hB
  letI : NormedAddCommGroup (Matrix (Fin r) (Fin r) E) := Matrix.normedAddCommGroup
  letI : NormedSpace E (Matrix (Fin r) (Fin r) E) := Matrix.normedSpace
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : ProperSpace (Matrix (Fin r) (Fin r) E) := FiniteDimensional.proper E _
  have hsE : Continuous (star : E → E) :=
    AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1 (fun x => by simp [hU.norm_star])
  haveI : ContinuousStar E := ⟨hsE⟩
  have hQc : Continuous fun z : Matrix (Fin r) (Fin r) E => z * star z :=
    continuous_id.mul continuous_star
  have hQs : ∀ (d : E) (z : Matrix (Fin r) (Fin r) E), (d • z) * star (d • z) = (d * star d) • (z * star z) := by
    intro d z
    rw [star_smul, smul_mul_smul_comm]
  have hnd : ∀ d : E, ‖d * star d‖ = ‖d‖ ^ 2 := by
    intro d; rw [norm_mul, hU.norm_star, sq]
  have hVc : IsClosed (V : Set (Matrix (Fin r) (Fin r) E)) := Submodule.closed_of_finiteDimensional V
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm E
  set A : Set (Matrix (Fin r) (Fin r) E) := {w | w ∈ V ∧ ‖k‖⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hA
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hVc.inter ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    · exact (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := 1)).subset
        (fun w hw => by simpa using hw.2.2)
  have hkpos : 0 < ‖k‖⁻¹ := inv_pos.mpr (lt_trans one_pos hk)
  have hA0 : ∀ w ∈ A, 0 < ‖w * star w‖ := by
    intro w hw
    apply norm_pos_iff.mpr
    intro h0
    have := hV w hw.1 h0
    have h1 := hw.2.1
    rw [this, norm_zero] at h1
    linarith
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ A, c ≤ ‖w * star w‖ := by
    rcases A.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hAc.exists_isMinOn hne (hQc.norm.continuousOn)
      exact ⟨_, hA0 w₀ hw₀, fun w hw => hmin hw⟩
  obtain ⟨R, hR⟩ := (hB.isBounded).subset_closedBall 0
  apply Metric.isCompact_of_isClosed_isBounded
  · exact hVc.inter (hB.isClosed.preimage hQc)
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := Real.sqrt (|R| / c))).subset
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hQR : ‖z * star z‖ ≤ |R| := by
      have := hR hz.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact Real.sqrt_nonneg _
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hz0
    have hdA : d • z ∈ A := ⟨V.smul_mem d hz.1, by simpa using hd2, hd1.le⟩
    have h1 := hc _ hdA
    rw [hQs, norm_smul, hnd] at h1
    rw [norm_smul] at hd1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc0]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0

    have hdz : (‖d‖ * ‖z‖) ^ 2 ≤ 1 := by
      have : 0 ≤ ‖d‖ * ‖z‖ := by positivity
      nlinarith
    have hQ0 : 0 ≤ ‖z * star z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]

end GlobalTheory
