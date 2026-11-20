import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

/- English proof (translation)
Introduce `K _ ι _ Ω _ y 𝕜 _ a s z w hz hw`. Take `⟨dg0, dh0, g0, h0, hg0, hh0, hd0, e0, hne, e1⟩` from `hw`. Establish `key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h`. Introduce `dg dh g h hg hh hd e`. Establish `hdeg : dg0 + dh = dg + dh0`.

Use function extensionality and compare the values at `k`. Establish `h1` using `hd k`. Establish `h2` using `hd0 k`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.

Establish `f1` using `MultiProjectiveCoordinates.Val.mh_mul hg hh0`. Establish `f2` using `MultiProjectiveCoordinates.Val.mh_mul hg0 hh`. Rewrite `f2` using `[hdeg]`. Establish `h3` using `MultiProjectiveCoordinates.Val.form_vanish y hz (MultiProjectiveCoordinates.Val.mh_sub f1 f2) (by`. Rewrite using `[map_sub, map_mul, map_mul, e, e0]`.

Use the proof step `ring)`. Rewrite `h3` using `[map_sub, map_mul, map_mul, e1]`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `h3`. Use `⟨key, ?_⟩` and prove the remaining obligations.

Introduce and unpack `w' ⟨dg, dh, g, h, hg, hh, hd, e, hn, e'⟩`. Use `key dg dh g h hg hh hd e` as an intermediate fact. Conclude with `mul_right_cancel₀ hn (e'.symm.trans this)`.
-/
theorem MultiProjectiveCoordinates.valuation_unique_on_forms : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  intro K _ ι _ Ω _ y 𝕜 _ a s z w hz hw
  obtain ⟨dg0, dh0, g0, h0, hg0, hh0, hd0, e0, hne, e1⟩ := hw
  have key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h := by
    intro dg dh g h hg hh hd e
    have hdeg : dg0 + dh = dg + dh0 := by
      funext k
      have h1 := hd k
      have h2 := hd0 k
      simp only [Pi.add_apply]
      omega
    have f1 := MultiProjectiveCoordinates.Val.mh_mul hg hh0
    have f2 := MultiProjectiveCoordinates.Val.mh_mul hg0 hh
    rw [hdeg] at f2
    have h3 := MultiProjectiveCoordinates.Val.form_vanish y hz (MultiProjectiveCoordinates.Val.mh_sub f1 f2) (by
      rw [map_sub, map_mul, map_mul, e, e0]
      ring)
    rw [map_sub, map_mul, map_mul, e1] at h3
    apply mul_right_cancel₀ hne
    linear_combination h3
  refine ⟨key, ?_⟩
  rintro w' ⟨dg, dh, g, h, hg, hh, hd, e, hn, e'⟩
  have := key dg dh g h hg hh hd e
  exact mul_right_cancel₀ hn (e'.symm.trans this)
