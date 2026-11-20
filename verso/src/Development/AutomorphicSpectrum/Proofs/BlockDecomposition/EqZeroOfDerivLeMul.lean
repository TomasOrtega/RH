import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.GronwallZero

/- English proof (translation)
Introduce `e e' K t ht hd hle hnn h0`. Establish `hg : ∀ s, HasDerivAt (fun s => e s * Real.exp (-K * s)) ((e' s - K * e s) * Real.exp (-K * s)) s`. Introduce `s`. Establish `h1 : HasDerivAt (fun s : ℝ => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s`. Establish `h2 : HasDerivAt (fun s : ℝ => -K * s) (-K) s`.

Simplify using `using (hasDerivAt_id s).const_mul (-K)`. Conclude with `h2.exp`. Establish `h5 : HasDerivAt (fun s => e s * Real.exp (-K * s)) (e' s * Real.exp (-K * s) + e s * (Real.exp (-K * s) * (-K))) s` using `(hd s).mul h1`. Conclude with `h5.congr_deriv (by ring)`. Establish `hanti : Antitone (fun s => e s * Real.exp (-K * s))`.

Apply `antitone_of_deriv_nonpos` to reduce the goal to its premises. Conclude with `fun s => (hg s).differentiableAt`. Introduce `s`. Rewrite using `[(hg s).deriv]`. Conclude with `mul_nonpos_of_nonpos_of_nonneg (by linarith [hle s]) (Real.exp_pos _).le`.

Establish `h3 : e t * Real.exp (-K * t) ≤ e 0 * Real.exp (-K * 0)` using `hanti ht`. Rewrite `h3` using `[h0, zero_mul]`. Establish `h4 : e t ≤ 0`. Assume the negation of the conclusion as `hc`. Conclude with `absurd h3 (not_le.mpr (mul_pos (not_le.mp hc) (Real.exp_pos _)))`.

Conclude with `le_antisymm h4 (hnn t)`.
-/
theorem eq_zero_of_deriv_le_mul :
    ∀ (e e' : ℝ → ℝ) (K t : ℝ), 0 ≤ t → (∀ s, HasDerivAt e (e' s) s) →
      (∀ s, e' s ≤ K * e s) → (∀ s, 0 ≤ e s) → e 0 = 0 → e t = 0 := by
  intro e e' K t ht hd hle hnn h0
  have hg : ∀ s, HasDerivAt (fun s => e s * Real.exp (-K * s))
      ((e' s - K * e s) * Real.exp (-K * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s := by
      have h2 : HasDerivAt (fun s : ℝ => -K * s) (-K) s := by
        simpa using (hasDerivAt_id s).const_mul (-K)
      exact h2.exp
    have h5 : HasDerivAt (fun s => e s * Real.exp (-K * s))
        (e' s * Real.exp (-K * s) + e s * (Real.exp (-K * s) * (-K))) s := (hd s).mul h1
    exact h5.congr_deriv (by ring)
  have hanti : Antitone (fun s => e s * Real.exp (-K * s)) := by
    apply antitone_of_deriv_nonpos
    · exact fun s => (hg s).differentiableAt
    · intro s
      rw [(hg s).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle s]) (Real.exp_pos _).le
  have h3 : e t * Real.exp (-K * t) ≤ e 0 * Real.exp (-K * 0) := hanti ht
  rw [h0, zero_mul] at h3
  have h4 : e t ≤ 0 := by
    by_contra hc
    exact absurd h3 (not_le.mpr (mul_pos (not_le.mp hc) (Real.exp_pos _)))
  exact le_antisymm h4 (hnn t)

end GlobalTheory.CompanionTheory.WaveSpd.GronwallZero
