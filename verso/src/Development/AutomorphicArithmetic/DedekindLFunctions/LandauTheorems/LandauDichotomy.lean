import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Establish `hD0 : 0 ≤ D` using `dist_nonneg.trans h1`. Rewrite `h1` using `[Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im]`. Establish `hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ D ^ 2`. Establish `hs` using `Real.sq_sqrt (by positivity : (0:ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)`. Establish `h0` using `Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `him : w.im = 0` using `by nlinarith [sq_nonneg w.im]`. Establish `hre : w.re = σ - D` using `by nlinarith [sq_nonneg w.im]`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_re]`.

Conclude with `hre`. Rewrite using `[Complex.ofReal_im]`. Conclude with `him`.
-/
theorem eq_ofReal_sub_of_dist_le_of_le_sub_re {w : ℂ} {σ D : ℝ} (h1 : dist w (σ : ℂ) ≤ D) (h2 : D ≤ σ - w.re) :
    w = ((σ - D : ℝ) : ℂ) := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h1
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at h1
  have hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ D ^ 2 := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    have h0 := Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    nlinarith
  have him : w.im = 0 := by nlinarith [sq_nonneg w.im]
  have hre : w.re = σ - D := by nlinarith [sq_nonneg w.im]
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact hre
  · rw [Complex.ofReal_im]; exact him

/- English proof (translation)
Establish `hfin : (Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)).Finite` using `landau_finite hiso (by rw [Complex.ofReal_re]; linarith)`. Use `set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ) with hFdef`. Break down `F.eq_empty_or_nonempty with hF | hF` into its components or cases. Use `left`. Use `⟨σ - θ, le_rfl, ?_, ρ₀, h₀, by linarith⟩` and prove the remaining obligations.

Introduce `w hw hb`. Establish `hwF : w ∈ F` using `⟨hw, Metric.ball_subset_closedBall hb⟩`. Rewrite `hwF` using `[hF]`. Conclude with `hwF`. Take `⟨ρs, hρsF, hmin⟩` from `Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF`.

Establish `hdle : dist ρs (σ : ℂ) ≤ σ - θ` using `Metric.mem_closedBall.mp hρsF.2`. Establish `hball : ∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) (dist ρs (σ : ℂ))`. Introduce `w hw hb`. Rewrite `hb` using `[Metric.mem_ball]`. Establish `hwF : w ∈ F` using `⟨hw, Metric.mem_closedBall.mpr (by linarith)⟩`.

Use `hmin w hwF` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hex : ∃ ρ₁ ∈ Z, σ - ρ₁.re < dist ρs (σ : ℂ)`. Use `left`. Conclude with `⟨dist ρs (σ : ℂ), hdle, hball, hex⟩`.

Use `right push_neg at hex set d := dist ρs (σ : ℂ) with hd`. Establish `hreal : ∀ w ∈ F, dist w (σ : ℂ) = d → w = ((σ - d : ℝ) : ℂ)` using `fun w hw he => eq_ofReal_sub_of_dist_le_of_le_sub_re (le_of_eq he) (hex w hw.1)`. Establish `hρs` using `hreal ρs hρsF rfl`. Establish `hdlt : d < σ - θ`. Break down `lt_or_eq_of_le hdle with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Use `hex ρ₀ h₀` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨σ - d, hρs ▸ hρsF.1, by linarith, ?_⟩` and prove the remaining obligations.

Establish `hT : ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, d < dist t (σ : ℂ)`. Introduce `t ht`. Establish `hm : d ≤ dist t (σ : ℂ)` using `hmin t ht.1`. Break down `lt_or_eq_of_le hm with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd (hreal t ht.1 h.symm) ht.2`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr, hrT⟩ : ∃ r, d < r ∧ ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, r ≤ dist t (σ : ℂ) := by`. Break down `(F \ {((σ - d : ℝ) : ℂ)}).eq_empty_or_nonempty with hTe | hTne` into its components or cases. Use `⟨d + 1, by linarith, ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Rewrite `ht` using `[hTe]`. Conclude with `absurd ht (Set.notMem_empty t)`. Take `⟨t₀, ht₀, htmin⟩` from `Set.exists_min_image (F \ {((σ - d : ℝ) : ℂ)}) (fun w => dist w (σ : ℂ)) (hfin.subset Set.diff_subset) hTne`. Conclude with `⟨dist t₀ (σ : ℂ), hT t₀ ht₀, htmin⟩`. Use `⟨min r (σ - θ), ?_, min_le_right _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_sub_cancel]`. Conclude with `lt_min hr hdlt`. Introduce `w hw hb`. Rewrite `hb` using `[Metric.mem_ball]`. Establish `hwF : w ∈ F` using `⟨hw, Metric.mem_closedBall.mpr (le_trans hb.le (min_le_right _ _))⟩`.

Assume the negation of the conclusion as `hne`. Establish `h3` using `hrT w ⟨hwF, hne⟩`. Establish `h4` using `min_le_left r (σ - θ)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem landau_dichotomy {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ θ : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hθ : 0 < θ) (hθσ : θ < σ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    (∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) D) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ r : ℝ, σ - β < r ∧ r ≤ σ - θ ∧
      ∀ w ∈ Z, w ∈ Metric.ball (σ : ℂ) r → w = β) := by
  have hfin : (Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)).Finite :=
    landau_finite hiso (by rw [Complex.ofReal_re]; linarith)
  set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ) with hFdef
  rcases F.eq_empty_or_nonempty with hF | hF
  · left
    refine ⟨σ - θ, le_rfl, ?_, ρ₀, h₀, by linarith⟩
    intro w hw hb
    have hwF : w ∈ F := ⟨hw, Metric.ball_subset_closedBall hb⟩
    rw [hF] at hwF
    exact hwF
  · obtain ⟨ρs, hρsF, hmin⟩ := Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF
    have hdle : dist ρs (σ : ℂ) ≤ σ - θ := Metric.mem_closedBall.mp hρsF.2
    have hball : ∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) (dist ρs (σ : ℂ)) := by
      intro w hw hb
      rw [Metric.mem_ball] at hb
      have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (by linarith)⟩
      have := hmin w hwF
      linarith
    by_cases hex : ∃ ρ₁ ∈ Z, σ - ρ₁.re < dist ρs (σ : ℂ)
    · left
      exact ⟨dist ρs (σ : ℂ), hdle, hball, hex⟩
    · right
      push_neg at hex
      set d := dist ρs (σ : ℂ) with hd
      have hreal : ∀ w ∈ F, dist w (σ : ℂ) = d → w = ((σ - d : ℝ) : ℂ) :=
        fun w hw he => eq_ofReal_sub_of_dist_le_of_le_sub_re (le_of_eq he) (hex w hw.1)
      have hρs := hreal ρs hρsF rfl
      have hdlt : d < σ - θ := by
        rcases lt_or_eq_of_le hdle with h | h
        · exact h
        · exfalso
          have := hex ρ₀ h₀
          linarith
      refine ⟨σ - d, hρs ▸ hρsF.1, by linarith, ?_⟩
      have hT : ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, d < dist t (σ : ℂ) := by
        intro t ht
        have hm : d ≤ dist t (σ : ℂ) := hmin t ht.1
        rcases lt_or_eq_of_le hm with h | h
        · exact h
        · exact absurd (hreal t ht.1 h.symm) ht.2
      obtain ⟨r, hr, hrT⟩ : ∃ r, d < r ∧ ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, r ≤ dist t (σ : ℂ) := by
        rcases (F \ {((σ - d : ℝ) : ℂ)}).eq_empty_or_nonempty with hTe | hTne
        · refine ⟨d + 1, by linarith, ?_⟩
          intro t ht
          rw [hTe] at ht
          exact absurd ht (Set.notMem_empty t)
        · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {((σ - d : ℝ) : ℂ)})
            (fun w => dist w (σ : ℂ)) (hfin.subset Set.diff_subset) hTne
          exact ⟨dist t₀ (σ : ℂ), hT t₀ ht₀, htmin⟩
      refine ⟨min r (σ - θ), ?_, min_le_right _ _, ?_⟩
      · rw [sub_sub_cancel]
        exact lt_min hr hdlt
      · intro w hw hb
        rw [Metric.mem_ball] at hb
        have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (le_trans hb.le (min_le_right _ _))⟩
        by_contra hne
        have h3 := hrT w ⟨hwF, hne⟩
        have h4 := min_le_left r (σ - θ)
        linarith

end Deduction

end
