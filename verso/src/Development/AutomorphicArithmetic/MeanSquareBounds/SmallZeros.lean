import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (authored)
Reducing the width narrows the interval of real arguments under consideration. Nonvanishing on the original interval therefore gives nonvanishing on the smaller interval.
-/
private theorem noExc_mono {c c' : ℝ} (h : c' ≤ c) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hc : NoExc c χ) : NoExc c' χ :=
  fun β h1 h2 => hc β (by linarith) h2

/- English proof (authored)
For a nonprincipal character the L-function is continuous at one and its value there is nonzero. Thus it stays nonzero on a sufficiently small real neighborhood of one. Choose a positive width whose one-sided interval is contained in this neighborhood. For a principal character the conditional assertion is vacuous.
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

/- English proof (authored)
There are finitely many characters at the fixed modulus. Take the minimum of their positive widths. It remains positive, and each character's nonvanishing interval contains the interval with that minimum width.
-/
private theorem noExc_level (N : ℕ) [NeZero N] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → NoExc c χ := by
  classical
  choose c hc h using fun χ : DirichletCharacter ℂ N => noExc_one χ
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_min c
  exact ⟨c χ₀, hc χ₀, fun χ hχ => noExc_mono (hχ₀ χ) (h χ hχ)⟩

/- English proof (authored)
Induct on the modulus bound. At zero there are no allowed moduli. In the successor step take the minimum of the width already obtained for smaller moduli and the width for the new modulus alone. Nonvanishing survives restriction to this smaller width in both cases.
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
