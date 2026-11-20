import Mathlib

/- English proof (translation)
Introduce `O σ ι inst e s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`. Establish `h0 : f = 0`.

Use extensionality with `n`. Simplify using `using hf n (by simp)`. Rewrite using `[h0]`. Conclude with `Ideal.zero_mem _`. Consider the case `insert a s _ ih`.

Introduce `f hf`. Set `g : MvPowerSeries σ O` to `fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0`. Establish `hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g = if n (e a) = 0 then MvPowerSeries.coeff n f else 0` using `fun _ => rfl`. Establish `h1 : g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O))`. Use `ih g fun n hn => ?_` and prove the remaining obligations.

Rewrite using `[hg]`. Use `split_ifs with h`. Use `hf n fun i hi => ?_` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `h`.

Conclude with `hn i hi`. Both sides reduce to the same expression. Establish `h2 : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g`. Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `n hn`.

Rewrite using `[map_sub, hg, if_pos hn, sub_self]`. Establish `h3 : f - g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O))` using `Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)`. Establish `h4` using `Ideal.add_mem _ h3 h1`. Rewrite `h4` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X :
    ∀ {O σ ι : Type} [inst : CommRing O] (e : ι → σ) (s : Finset ι)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ),
        (∀ i ∈ s, (n : σ → ℕ) (e i) = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range fun (i : ι) ↦ MvPowerSeries.X (e i)) := by
  intro O σ ι inst e s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a s _ ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g
        = if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have h1 : g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) := by
      refine ih g fun n hn => ?_
      rw [hg]
      split_ifs with h
      · refine hf n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have h3 : f - g ∈ Ideal.span
        (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
