import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem exists_unit_mul_eq_abs (u : ℝ) : ∃ s : ℝ, |s| = 1 ∧ s * u = |u| := by
  by_cases h : 0 ≤ u
  · exact ⟨1, by simp, by rw [one_mul, abs_of_nonneg h]⟩
  · exact ⟨-1, by simp, by rw [abs_of_neg (not_le.1 h)]; ring⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Chain the equalities or inequalities of the calculation. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem expDecay_of_midpoint : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type)
    [TopologicalSpace T] (φ : ℝ × ℝ → T → X) (S : Set (ℝ × ℝ)),
    (∀ a ∈ S, ∀ g : T, ∃ r : ℝ, 0 < r ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - a.1| ≤ r → |x.2 - a.2| ≤ r →
      ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t)) →
    (∀ x : ℝ × ℝ, ∃ a ∈ S, ∃ b ∈ S, x = midpoint ℝ a b) → ExpDecay φ := by
  intro X _ _ T _ φ S hS hmid x₀ g
  obtain ⟨a, ha, b, hb, hx₀⟩ := hmid x₀
  obtain ⟨ra, hra, Ua, hUa, Ma, hMa⟩ := hS a ha g
  obtain ⟨rb, hrb, Ub, hUb, Mb, hMb⟩ := hS b hb g
  have hm1 : a.1 + b.1 = 2 * x₀.1 := by rw [hx₀]; simp [midpoint_eq_smul_add]; ring
  have hm2 : a.2 + b.2 = 2 * x₀.2 := by rw [hx₀]; simp [midpoint_eq_smul_add]; ring
  refine ⟨min ra rb / 2, by positivity, Ua ∩ Ub, Filter.inter_mem hUa hUb, max (max Ma Mb) 0, ?_⟩
  intro x hx1 hx2 g' hg' t
  set ε := min ra rb / 2 with hε
  have hεa : 2 * ε ≤ ra := by rw [hε]; linarith [min_le_left ra rb]
  have hεb : 2 * ε ≤ rb := by rw [hε]; linarith [min_le_right ra rb]
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  obtain ⟨s1, hs1, hst1⟩ := exists_unit_mul_eq_abs t.1
  obtain ⟨s2, hs2, hst2⟩ := exists_unit_mul_eq_abs t.2
  have close : ∀ c d s : ℝ, |s| = 1 → |d| ≤ ε → |c + d + ε * s - c| ≤ 2 * ε := by
    intro c d s hs hd
    have hcd : c + d + ε * s - c = d + ε * s := by ring
    rw [hcd]
    calc |d + ε * s| ≤ |d| + |ε * s| := abs_add_le _ _
      _ = |d| + ε := by rw [abs_mul, hs, mul_one, abs_of_nonneg hε0]
      _ ≤ 2 * ε := by linarith
  have hA := hMa (a.1 + (x.1 - x₀.1) + ε * s1, a.2 + (x.2 - x₀.2) + ε * s2)
    ((close _ _ s1 hs1 hx1).trans hεa) ((close _ _ s2 hs2 hx2).trans hεa) g' hg'.1 t
  have hB := hMb (b.1 + (x.1 - x₀.1) + ε * s1, b.2 + (x.2 - x₀.2) + ε * s2)
    ((close _ _ s1 hs1 hx1).trans hεb) ((close _ _ s2 hs2 hx2).trans hεb) g' hg'.2 t
  set A := rdot (a.1 + (x.1 - x₀.1) + ε * s1, a.2 + (x.2 - x₀.2) + ε * s2) t with hAdef
  set B := rdot (b.1 + (x.1 - x₀.1) + ε * s1, b.2 + (x.2 - x₀.2) + ε * s2) t with hBdef
  have hsum : A + B = 2 * (rdot x t + ε * (|t.1| + |t.2|)) := by
    rw [hAdef, hBdef, ← hst1, ← hst2]
    simp only [rdot]
    linear_combination t.1 * hm1 + t.2 * hm2
  have hM0 : 0 ≤ max (max Ma Mb) 0 := le_max_right _ _
  have hR : max (max Ma Mb) 0 * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|)) =
      max (max Ma Mb) 0 * Real.exp (-((A + B) / 2)) := by
    rw [mul_assoc, ← Real.exp_add, hsum]
    congr 2
    ring
  rw [hR]
  rcases le_total B A with h | h
  · calc ‖φ t g'‖ ≤ Ma * Real.exp (-A) := hA
      _ ≤ max (max Ma Mb) 0 * Real.exp (-A) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) (Real.exp_pos _).le
      _ ≤ max (max Ma Mb) 0 * Real.exp (-((A + B) / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hM0
  · calc ‖φ t g'‖ ≤ Mb * Real.exp (-B) := hB
      _ ≤ max (max Ma Mb) 0 * Real.exp (-B) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) (Real.exp_pos _).le
      _ ≤ max (max Ma Mb) 0 * Real.exp (-((A + B) / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hM0

end GlobalTheory.CompanionTheory.TubeFourier
