import Mathlib

/- English proof (translation)
Introduce `O σ inst s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`. Establish `h0 : f = 0`.

Use extensionality with `n`. Simplify using `using hf n (by simp)`. Rewrite using `[h0]`. Conclude with `Ideal.zero_mem _`. Consider the case `insert a t hat ih`.

Introduce `f hf`. Set `g : MvPowerSeries σ O` to `fun n => if n a = 0 then MvPowerSeries.coeff n f else 0`. Establish `hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g = if n a = 0 then MvPowerSeries.coeff n f else 0` using `fun n => rfl`. Establish `h1 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O))`. Apply `ih` to reduce the goal to its premises.

Introduce `n hn`. Rewrite using `[hg]`. Use `split_ifs with h`. Apply `hf` to reduce the goal to its premises. Introduce `i hi`.

Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `h`. Conclude with `hn i hi`. Both sides reduce to the same expression. Establish `h2 : (MvPowerSeries.X a : MvPowerSeries σ O) ∣ f - g`.

Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `m hm`. Rewrite using `[map_sub, hg, if_pos hm, sub_self]`. Establish `h3 : f - g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O))` using `Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)`. Establish `h4` using `Ideal.add_mem _ h3 h1`.

Rewrite `h4` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X :
    ∀ {O σ : Type} [inst : CommRing O] (s : Finset σ)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ), (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ inst s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a t hat ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have h1 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
      apply ih
      intro n hn
      rw [hg]
      split_ifs with h
      · apply hf
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X a : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hg, if_pos hm, sub_self]
    have h3 : f - g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
