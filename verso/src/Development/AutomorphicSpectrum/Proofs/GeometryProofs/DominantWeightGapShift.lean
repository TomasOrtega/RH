import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.WtShift

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

/- English proof (translation)
Simplify using `only [ent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ent_sub_smul (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) (i : ℕ) :
    ent (lam - s • nu) τ i = ent lam τ i - s * ent nu τ i := by
  simp only [ent]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [ent]`. Use `split_ifs with h`. Rewrite using `[← Real.norm_eq_abs]`. Conclude with `(norm_le_pi_norm (nu τ) _).trans (norm_le_pi_norm nu τ)`. Simplify using the standard rewrite rules.
-/
theorem abs_ent_le (nu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent nu τ i| ≤ ‖nu‖ := by
  simp only [ent]
  split_ifs with h
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (nu τ) _).trans (norm_le_pi_norm nu τ)
  · simp

/- English proof (translation)
Introduce `τ a b hab`. Establish `key : ∀ k i, i + k < N → ent mu τ (i + k) ≤ ent mu τ i`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i _`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `i hi`. Conclude with `(h τ (i + k) (by omega)).trans (ih i (by omega))`. Establish `hab' : (a : ℕ) ≤ b` using `hab`.

Establish `hk` using `key ((b : ℕ) - a) a (by omega)`. Rewrite `hk` using `[Nat.add_sub_cancel' hab']`. Simplify `hk` using `[ent, a.2, b.2]`.
-/
theorem dominant_of_step (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → ent mu τ (i + 1) ≤ ent mu τ i) : Dominant mu := by
  intro τ a b hab
  have key : ∀ k i, i + k < N → ent mu τ (i + k) ≤ ent mu τ i := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      exact (h τ (i + k) (by omega)).trans (ih i (by omega))
  have hab' : (a : ℕ) ≤ b := hab
  have hk := key ((b : ℕ) - a) a (by omega)
  rw [Nat.add_sub_cancel' hab'] at hk
  simpa [ent, a.2, b.2] using hk

/- English proof (translation)
Introduce `Ψ _ _ N j nu c₀ hj hjN hc₀`. Establish `hM0 : 0 ≤ ‖nu‖` using `norm_nonneg _`. Use `⟨min 1 (min (1 / (4 * (‖nu‖ + 1))) (c₀ / (2 * (‖nu‖ + 1)))), by positivity, min_le_left _ _, ?_⟩` and prove the remaining obligations. Introduce `lam θ hlam hθ hθ₀ hgap hcg`. Establish `hθ1 : θ ≤ 1` using `hθ₀.trans (min_le_left _ _)`.

Establish `hA' : θ ≤ 1 / (4 * (‖nu‖ + 1))` using `hθ₀.trans ((min_le_right _ _).trans (min_le_left _ _))`. Establish `hB' : θ ≤ c₀ / (2 * (‖nu‖ + 1))` using `hθ₀.trans ((min_le_right _ _).trans (min_le_right _ _))`. Establish `hA` using `(le_div_iff₀ (by positivity)).1 hA'`. Establish `hB` using `(le_div_iff₀ (by positivity)).1 hB'`. Establish `hθM : θ * ‖nu‖ ≤ 1 / 4` using `by nlinarith`.

Establish `hθM' : θ * ‖nu‖ ≤ c₀ / 2` using `by nlinarith`. Establish `hdiff : ∀ τ i i', ent nu τ i - ent nu τ i' ≤ 2 * ‖nu‖` using `fun τ i i' => by`. Establish `h1` using `abs_le.1 (abs_ent_le nu τ i)`. Establish `h2` using `abs_le.1 (abs_ent_le nu τ i')`. Combine the linear relations using `[h1.2, h2.1]`.

Establish `hsq : θ ^ 2 * (2 * ‖nu‖) ≤ θ / 2` using `by nlinarith`. Establish `hsq2 : θ ^ 2 * (2 * ‖nu‖) ≤ c₀` using `by nlinarith`. Use `⟨dominant_of_step _ fun τ i hi => ?_, ?_, fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[ent_sub_smul, ent_sub_smul]`. Establish `hd` using `mul_le_mul_of_nonneg_left (hdiff τ i (i + 1)) (sq_nonneg θ)`.

Distinguish the cases in `hij : i + 1 = j`. Substitute `hij` using the available equality. Establish `hg` using `hgap τ`. Simplify using `only [gap, Nat.add_sub_cancel] at hg`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hc` using `hcg τ i hi hij`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Establish `hg` using `hgap τ`. Establish `hd` using `mul_le_mul_of_nonneg_left (hdiff τ (j - 1) j) (sq_nonneg θ)`.

Simplify using `only [gap] at hg ⊢`. Rewrite using `[ent_sub_smul, ent_sub_smul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sub_small_dominant : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N →
    0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) →
      CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧
        ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  intro Ψ _ _ N j nu c₀ hj hjN hc₀
  have hM0 : 0 ≤ ‖nu‖ := norm_nonneg _
  refine ⟨min 1 (min (1 / (4 * (‖nu‖ + 1))) (c₀ / (2 * (‖nu‖ + 1)))), by positivity, min_le_left _ _, ?_⟩
  intro lam θ hlam hθ hθ₀ hgap hcg
  have hθ1 : θ ≤ 1 := hθ₀.trans (min_le_left _ _)
  have hA' : θ ≤ 1 / (4 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB' : θ ≤ c₀ / (2 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA := (le_div_iff₀ (by positivity)).1 hA'
  have hB := (le_div_iff₀ (by positivity)).1 hB'
  have hθM : θ * ‖nu‖ ≤ 1 / 4 := by nlinarith
  have hθM' : θ * ‖nu‖ ≤ c₀ / 2 := by nlinarith
  have hdiff : ∀ τ i i', ent nu τ i - ent nu τ i' ≤ 2 * ‖nu‖ := fun τ i i' => by
    have h1 := abs_le.1 (abs_ent_le nu τ i)
    have h2 := abs_le.1 (abs_ent_le nu τ i')
    linarith [h1.2, h2.1]
  have hsq : θ ^ 2 * (2 * ‖nu‖) ≤ θ / 2 := by nlinarith
  have hsq2 : θ ^ 2 * (2 * ‖nu‖) ≤ c₀ := by nlinarith
  refine ⟨dominant_of_step _ fun τ i hi => ?_, ?_, fun τ => ?_⟩
  · rw [ent_sub_smul, ent_sub_smul]
    have hd := mul_le_mul_of_nonneg_left (hdiff τ i (i + 1)) (sq_nonneg θ)
    by_cases hij : i + 1 = j
    · subst hij
      have hg := hgap τ
      simp only [gap, Nat.add_sub_cancel] at hg
      nlinarith
    · have hc := hcg τ i hi hij
      nlinarith
  · calc ‖lam - θ ^ 2 • nu‖ ≤ ‖lam‖ + ‖θ ^ 2 • nu‖ := norm_sub_le _ _
      _ = ‖lam‖ + θ ^ 2 * ‖nu‖ := by rw [norm_smul, Real.norm_of_nonneg (sq_nonneg θ)]
      _ ≤ 2 := by nlinarith
  · have hg := hgap τ
    have hd := mul_le_mul_of_nonneg_left (hdiff τ (j - 1) j) (sq_nonneg θ)
    simp only [gap] at hg ⊢
    rw [ent_sub_smul, ent_sub_smul]
    nlinarith

end GlobalTheory.CompanionTheory.Ar.WtShift
