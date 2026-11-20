import Mathlib

/- English proof (translation)
Introduce `O σ inst I s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `_ f hf`. Establish `h0 : f = 0`.

Use extensionality with `n`. Rewrite using `[hf n (by simp), map_zero]`. Rewrite using `[h0]`. Conclude with `I.zero_mem`. Consider the case `insert a s ha ih`.

Introduce `hX f hf`. Set `g : MvPowerSeries σ O` to `fun n => if n a = 0 then MvPowerSeries.coeff n f else 0`. Establish `hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g = if n a = 0 then MvPowerSeries.coeff n f else 0` using `fun n => rfl`. Establish `hgI : g ∈ I`. Use `ih (fun i hi => hX i (Finset.mem_insert_of_mem hi)) g ?_` and prove the remaining obligations.

Introduce `n hn`. Rewrite using `[hg]`. Use `split_ifs with h`. Use `hf n ?_` and prove the remaining obligations. Introduce `i hi`.

Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `h`. Conclude with `hn i hi`. Both sides reduce to the same expression. Establish `hd : MvPowerSeries.X a ∣ f - g`.

Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `n hn`. Rewrite using `[map_sub, hg, if_pos hn, sub_self]`. Establish `hfg : f - g ∈ I` using `I.mem_of_dvd hd (hX a (Finset.mem_insert_self a s))`. Use `I.add_mem hfg hgI` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.SpanOfVariable.span_X :
    ∀ {O σ : Type} [inst : CommRing O] (I : Ideal (MvPowerSeries σ O))
    (s : Finset σ),
    (∀ i ∈ s, MvPowerSeries.X i ∈ I) →
      ∀ (f : MvPowerSeries σ O),
        (∀ (n : σ →₀ ℕ),
            (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
          f ∈ I := by
  intro O σ inst I s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ f hf
    have h0 : f = 0 := by
      ext n
      rw [hf n (by simp), map_zero]
    rw [h0]
    exact I.zero_mem
  | insert a s ha ih =>
    intro hX f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have hgI : g ∈ I := by
      refine ih (fun i hi => hX i (Finset.mem_insert_of_mem hi)) g ?_
      intro n hn
      rw [hg]
      split_ifs with h
      · refine hf n ?_
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have hd : MvPowerSeries.X a ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have hfg : f - g ∈ I := I.mem_of_dvd hd (hX a (Finset.mem_insert_self a s))
    have := I.add_mem hfg hgI
    rwa [sub_add_cancel] at this
