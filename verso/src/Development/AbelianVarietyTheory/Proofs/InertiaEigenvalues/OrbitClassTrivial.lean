import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory

/- English proof (translation)
Introduce `o p f _ho hp hc _ hcl hcov hsh`. Set `g : ℝ → ℕ` to `fun r => if h : ∃ i, 0 < f i r then (Classical.choose h) % o else 0`. Establish `hg : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, 0 < f i r → g r = i % o`. Introduce `r hr i hi`. Establish `h : ∃ i, 0 < f i r` using `⟨i, hi⟩`.

Simplify using `only [g, dif_pos h]`. Conclude with `hcl _ _ r hr (Classical.choose_spec h) hi`. Establish `gcont : ContinuousOn g (Set.Ioc (0 : ℝ) 1)`. Introduce `r hr`. Take `⟨i, hi⟩` from `hcov r hr`.

Rewrite using `[ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]`. Establish `h1 : ∀ᶠ x in nhdsWithin r (Set.Ioc (0 : ℝ) 1), 0 < f i x` using `((hc i) r hr).eventually (lt_mem_nhds hi)`. Use `filter_upwards [h1, self_mem_nhdsWithin] with x hx hxs`. Rewrite using `[hg x hxs i hx, hg r hr i hi]`. Establish `hp0 : 0 < p` using `by linarith`.

Establish `hr1 : 1 / p ∈ Set.Ioc (0 : ℝ) 1` using `⟨by positivity, by rw [div_le_one hp0]; exact hp.le⟩`. Establish `h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1` using `⟨one_pos, le_rfl⟩`. Establish `hconst : g (1 / p) = g 1` using `isPreconnected_Ioc.constant gcont hr1 h1`. Take `⟨i, hi⟩` from `hcov (1 / p) hr1`. Establish `hi1 : 0 < f (i + 1) 1`.

Use `hsh i (1 / p) (by positivity) le_rfl hi` as an intermediate fact. Rewrite `this` using `[mul_one_div_cancel hp0.ne']`. Then use the resulting hypothesis. Establish `hmod : (i + 1) % o = (i + 0) % o`. Rewrite using `[add_zero, ← hg _ hr1 i hi, ← hg _ h1 (i + 1) hi1, hconst]`. Establish `h10 : 1 ≡ 0 [MOD o]` using `Nat.ModEq.add_left_cancel' i hmod`.

Conclude with `Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)`.
-/
theorem orbit_class_trivial : ∀ (o : ℕ) (p : ℝ) (f : ℕ → ℝ → ℝ), 0 < o → 1 < p → (∀ i, ContinuousOn (f i) (Set.Ioc 0 1)) → (∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f i r) → (∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < f i r → 0 < f j r → i % o = j % o) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < f i r) → (∀ i r, 0 < r → r ≤ 1 / p → 0 < f i r → 0 < f (i + 1) (p * r)) → o = 1 := by
  intro o p f _ho hp hc _ hcl hcov hsh
  classical
  let g : ℝ → ℕ := fun r => if h : ∃ i, 0 < f i r then (Classical.choose h) % o else 0
  have hg : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, 0 < f i r → g r = i % o := by
    intro r hr i hi
    have h : ∃ i, 0 < f i r := ⟨i, hi⟩
    simp only [g, dif_pos h]
    exact hcl _ _ r hr (Classical.choose_spec h) hi
  have gcont : ContinuousOn g (Set.Ioc (0 : ℝ) 1) := by
    intro r hr
    obtain ⟨i, hi⟩ := hcov r hr
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    have h1 : ∀ᶠ x in nhdsWithin r (Set.Ioc (0 : ℝ) 1), 0 < f i x :=
      ((hc i) r hr).eventually (lt_mem_nhds hi)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxs
    rw [hg x hxs i hx, hg r hr i hi]
  have hp0 : 0 < p := by linarith
  have hr1 : 1 / p ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hp0]; exact hp.le⟩
  have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hconst : g (1 / p) = g 1 := isPreconnected_Ioc.constant gcont hr1 h1
  obtain ⟨i, hi⟩ := hcov (1 / p) hr1
  have hi1 : 0 < f (i + 1) 1 := by
    have := hsh i (1 / p) (by positivity) le_rfl hi
    rwa [mul_one_div_cancel hp0.ne'] at this
  have hmod : (i + 1) % o = (i + 0) % o := by
    rw [add_zero, ← hg _ hr1 i hi, ← hg _ h1 (i + 1) hi1, hconst]
  have h10 : 1 ≡ 0 [MOD o] := Nat.ModEq.add_left_cancel' i hmod
  exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)

end GlobalTheory
