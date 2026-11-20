import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
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
