import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Introduce `β h1 h2` and use `hc β (by linarith) h2`.
-/
private theorem noExc_mono {c c' : ℝ} (h : c' ≤ c) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hc : NoExc c χ) : NoExc c' χ :=
  fun β h1 h2 => hc β (by linarith) h2

/- English proof (translation)
Distinguish the cases in `hχ : χ = 1`. Conclude with `⟨1, one_pos, fun h => absurd hχ h⟩`. Establish `hcont : Continuous (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ))` using `(DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal`. Establish `h1 : (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 ≠ 0`. Simplify using `using DirichletCharacter.LFunction_apply_one_ne_zero hχ`.

Establish `hev` using `hcont.continuousAt.eventually_ne h1`. Take `⟨c, hc, h⟩` from `Metric.eventually_nhds_iff.1 hev`. Use `⟨c, hc, fun _ β hb1 hb2 => h ?_⟩` and prove the remaining obligations. Rewrite using `[Real.dist_eq, abs_lt]`. Apply the tactic sequence `constructor <;> linarith`.
-/
private theorem noExc_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ c : ℝ, 0 < c ∧ (χ ≠ 1 → NoExc c χ) := by
  by_cases hχ : χ = 1
  · exact ⟨1, one_pos, fun h => absurd hχ h⟩
  have hcont : Continuous (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
  have h1 : (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hev := hcont.continuousAt.eventually_ne h1
  obtain ⟨c, hc, h⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨c, hc, fun _ β hb1 hb2 => h ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/- English proof (translation)
Use `choose c hc h using fun χ : DirichletCharacter ℂ N => noExc_one χ`. Take `⟨χ₀, hχ₀⟩` from `Finite.exists_min c`. Conclude with `⟨c χ₀, hc χ₀, fun χ hχ => noExc_mono (hχ₀ χ) (h χ hχ)⟩`.
-/
private theorem noExc_level (N : ℕ) [NeZero N] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → NoExc c χ := by
  classical
  choose c hc h using fun χ : DirichletCharacter ℂ N => noExc_one χ
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_min c
  exact ⟨c χ₀, hc χ₀, fun χ hχ => noExc_mono (hχ₀ χ) (h χ hχ)⟩

/- English proof (translation)
Introduce `N₀`. Proceed by induction on `N₀ with`. Consider the case `zero`. Conclude with `⟨1, one_pos, fun N _ χ hN _ => absurd (Nat.le_zero.1 hN) (NeZero.ne N)⟩`. Consider the case `succ n ih`.

Take `⟨c, hc, h⟩` from `ih`. Take `⟨c', hc', h'⟩` from `noExc_level (n + 1)`. Use `⟨min c c', lt_min hc hc', fun N _ χ hN hχ => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_eq_of_le hN with hlt | heq` into its components or cases. Conclude with `noExc_mono (min_le_left _ _) (h N χ (Nat.lt_succ_iff.1 hlt) hχ)`.

Substitute `heq` using the available equality. Conclude with `noExc_mono (min_le_right _ _) (h' χ hχ)`.
-/
theorem small_zeros :
    ∀ N₀ : ℕ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N ≤ N₀ → χ ≠ 1 → NoExc c₀ χ := by
  intro N₀
  induction N₀ with
  | zero =>
    exact ⟨1, one_pos, fun N _ χ hN _ => absurd (Nat.le_zero.1 hN) (NeZero.ne N)⟩
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := noExc_level (n + 1)
    refine ⟨min c c', lt_min hc hc', fun N _ χ hN hχ => ?_⟩
    rcases Nat.lt_or_eq_of_le hN with hlt | heq
    · exact noExc_mono (min_le_left _ _) (h N χ (Nat.lt_succ_iff.1 hlt) hχ)
    · subst heq
      exact noExc_mono (min_le_right _ _) (h' χ hχ)

end QH
