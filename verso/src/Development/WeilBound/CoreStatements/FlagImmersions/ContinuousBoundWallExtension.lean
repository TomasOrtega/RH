import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

/- English proof (translation)
Break down `lt_trichotomy x 0 with hx | hx | hx` into its components or cases. Take `⟨q, h1, h2⟩` from `exists_rat_btwn (show x < min (x + δ) 0 from lt_min (by linarith) hx)`. Establish `m1` using `min_le_left (x + δ) 0`. Establish `m2` using `min_le_right (x + δ) 0`. Use `⟨q, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[abs_of_neg hx, abs_of_nonpos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Conclude with `⟨0, by simp [hx], by simp [hx, hδ.le]⟩`.

Take `⟨q, h1, h2⟩` from `exists_rat_btwn (show max (x - δ) 0 < x from max_lt (by linarith) hx)`. Establish `m1` using `le_max_left (x - δ) 0`. Establish `m2` using `le_max_right (x - δ) 0`. Use `⟨q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_of_pos hx, abs_of_nonneg (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem exists_rat_near_le (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ∃ q : ℚ, |(q : ℝ)| ≤ |x| ∧ |(q : ℝ) - x| ≤ δ := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x < min (x + δ) 0 from lt_min (by linarith) hx)
    have m1 := min_le_left (x + δ) 0
    have m2 := min_le_right (x + δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_neg hx, abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith
  · exact ⟨0, by simp [hx], by simp [hx, hδ.le]⟩
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max (x - δ) 0 < x from max_lt (by linarith) hx)
    have m1 := le_max_left (x - δ) 0
    have m2 := le_max_right (x - δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_pos hx, abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith

/- English proof (translation)
Introduce `Ψ _ _ N j c₀ b τ₀ Φ hj hjN hc hΦ hrat lam hlam`. Establish `hex : ∀ n : ℕ, ∀ x : ℝ, ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ) - x| ≤ c₀ / 4 * (1 / ((n:ℝ) + 1))` using `fun n x => exists_rat_near_le _ (by positivity) x`. Use `choose F hF1 hF2 using hex`. Set `A : ℕ → Wt Ψ N` to `fun n τ i => (F n (lam τ i) : ℝ)`. Establish `hδ : ∀ n : ℕ, c₀ / 4 * (1 / ((n:ℝ) + 1)) ≤ c₀ / 4`.

Introduce `n`. Establish `h1 : 1 / ((n:ℝ) + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Combine the linear relations using `[(n.cast_nonneg : (0:ℝ) ≤ n)]`. Conclude with `mul_le_of_le_one_right (by positivity) h1`.

Establish `hent : ∀ n τ k, k < N → ent (A n) τ k = (F n (ent lam τ k) : ℝ)`. Introduce `n τ k hk`. Simplify using `[ent, hk, A]`. Establish `hclose : ∀ n τ k, k < N → |ent (A n) τ k - ent lam τ k| ≤ c₀ / 4`. Introduce `n τ k hk`.

Rewrite using `[hent n τ k hk]`. Conclude with `(hF2 n _).trans (hδ n)`. Establish `hin : ∀ n, InWall j τ₀ (c₀ / 2) (A n)`. Introduce `n`. Take `⟨hn, hg0, hgτ, hcg⟩` from `hlam`.

Establish `hj1 : j - 1 < N` using `by omega`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun τ => (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_` and prove the remaining obligations. Establish `h1 : ‖lam τ i‖ ≤ 1 / 2` using `(norm_le_pi_norm (lam τ) i).trans ((norm_le_pi_norm lam τ).trans hn)`. Simplify using `only [Real.norm_eq_abs, A] at h1 ⊢`.

Conclude with `(hF1 n _).trans h1`. Simplify using `only [gap] at hg0 ⊢`. Rewrite using `[hent n τ₀ _ hj1, hent n τ₀ _ hjN, show ent lam τ₀ (j - 1) = ent lam τ₀ j by linarith]`. Expand and normalize the polynomial expressions, which then agree. Introduce `τ hτ`.

Establish `h` using `hgτ τ hτ`. Simplify using `only [gap] at h ⊢`. Establish `a1` using `abs_le.1 (hclose n τ _ hj1)`. Establish `a2` using `abs_le.1 (hclose n τ _ hjN)`. Combine the linear relations using `[a1.1, a1.2, a2.1, a2.2]`.

Introduce `τ i hi hij`. Establish `h` using `hcg τ i hi hij`. Establish `a1` using `abs_le.1 (hclose n τ i (by omega))`. Establish `a2` using `abs_le.1 (hclose n τ (i + 1) hi)`. Combine the linear relations using `[a1.1, a1.2, a2.1, a2.2]`.

Establish `hAr : ∀ n, IsRatWt (A n)` using `fun n τ i => ⟨F n (lam τ i), rfl⟩`. Establish `htend : Tendsto A atTop (𝓝 lam)`. Rewrite using `[tendsto_pi_nhds]`. Introduce `τ`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `i`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hlim : Tendsto (fun n : ℕ => c₀ / 4 * (1 / ((n:ℝ) + 1))) atTop (𝓝 0)`. Simplify using `using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (c₀ / 4)`. Use `squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim` and prove the remaining obligations.

Simplify using `only [A, Real.norm_eq_abs]`. Conclude with `hF2 n _`. Establish `hΦt : Tendsto (fun n => |Φ (A n)|) atTop (𝓝 |Φ lam|)` using `(continuous_abs.tendsto _).comp ((hΦ.tendsto lam).comp htend)`. Conclude with `le_of_tendsto' hΦt fun n => hrat _ (hAr n) (hin n)`.
-/
theorem continuous_bound_wall_extension : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  intro Ψ _ _ N j c₀ b τ₀ Φ hj hjN hc hΦ hrat lam hlam
  have hex : ∀ n : ℕ, ∀ x : ℝ, ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ) - x| ≤ c₀ / 4 * (1 / ((n:ℝ) + 1)) :=
    fun n x => exists_rat_near_le _ (by positivity) x
  choose F hF1 hF2 using hex
  let A : ℕ → Wt Ψ N := fun n τ i => (F n (lam τ i) : ℝ)
  have hδ : ∀ n : ℕ, c₀ / 4 * (1 / ((n:ℝ) + 1)) ≤ c₀ / 4 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact mul_le_of_le_one_right (by positivity) h1
  have hent : ∀ n τ k, k < N → ent (A n) τ k = (F n (ent lam τ k) : ℝ) := by
    intro n τ k hk
    simp [ent, hk, A]
  have hclose : ∀ n τ k, k < N → |ent (A n) τ k - ent lam τ k| ≤ c₀ / 4 := by
    intro n τ k hk
    rw [hent n τ k hk]
    exact (hF2 n _).trans (hδ n)
  have hin : ∀ n, InWall j τ₀ (c₀ / 2) (A n) := by
    intro n
    obtain ⟨hn, hg0, hgτ, hcg⟩ := hlam
    have hj1 : j - 1 < N := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun τ =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      have h1 : ‖lam τ i‖ ≤ 1 / 2 := (norm_le_pi_norm (lam τ) i).trans ((norm_le_pi_norm lam τ).trans hn)
      simp only [Real.norm_eq_abs, A] at h1 ⊢
      exact (hF1 n _).trans h1
    · simp only [gap] at hg0 ⊢
      rw [hent n τ₀ _ hj1, hent n τ₀ _ hjN, show ent lam τ₀ (j - 1) = ent lam τ₀ j by linarith]
      ring
    · intro τ hτ
      have h := hgτ τ hτ
      simp only [gap] at h ⊢
      have a1 := abs_le.1 (hclose n τ _ hj1)
      have a2 := abs_le.1 (hclose n τ _ hjN)
      linarith [a1.1, a1.2, a2.1, a2.2]
    · intro τ i hi hij
      have h := hcg τ i hi hij
      have a1 := abs_le.1 (hclose n τ i (by omega))
      have a2 := abs_le.1 (hclose n τ (i + 1) hi)
      linarith [a1.1, a1.2, a2.1, a2.2]
  have hAr : ∀ n, IsRatWt (A n) := fun n τ i => ⟨F n (lam τ i), rfl⟩
  have htend : Tendsto A atTop (𝓝 lam) := by
    rw [tendsto_pi_nhds]
    intro τ
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => c₀ / 4 * (1 / ((n:ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (c₀ / 4)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    simp only [A, Real.norm_eq_abs]
    exact hF2 n _
  have hΦt : Tendsto (fun n => |Φ (A n)|) atTop (𝓝 |Φ lam|) :=
    (continuous_abs.tendsto _).comp ((hΦ.tendsto lam).comp htend)
  exact le_of_tendsto' hΦt fun n => hrat _ (hAr n) (hin n)

end RootFieldNumerics
