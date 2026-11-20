import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OddSpanVariable

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X e s`.
-/
private theorem ep_odd_span_X {O σ ι : Type} [CommRing O] (e : ι → σ) (s : Finset ι) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) →
      f ∈ Ideal.span (Set.range fun i => (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X e s

/- English proof (translation)
Introduce `O _ _ R _ _ _ σ P`. Rewrite using `[← P.part 1]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Establish `h1 : f ∈ Ideal.span (Set.range fun i : Fin P.g => (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin P.a ⊕ Fin P.g) O))`. Use `ep_odd_span_X Sum.inr Finset.univ f fun n hn => hf n ?_` and prove the remaining obligations. Establish `: Finsupp.weight (Space.Loc.par P.a P.g) n = 0`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations.

Break down `s with s | s` into its components or cases. Simplify using `[Space.Loc.par]`. Simplify using `[hn s (Finset.mem_univ _)]`. Rewrite using `[this]`. Evaluate the decidable proposition.

Establish `h2` using `Ideal.mem_map_of_mem P.p h1`. Rewrite `h2` using `[Ideal.map_span, ← Set.range_comp]`. Conclude with `h2`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `Ideal.subset_span ⟨MvPowerSeries.X (.inr i), fun n hn => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_X, if_neg]`. Introduce and unpack `rfl`. Apply `hn` to reduce the goal to its premises. Simplify using `[Finsupp.weight_single, Space.Loc.par]`.
-/
theorem UpperTheory.V.Fr.ep_odd :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), Ideal.span (evp σ 1 : Set R) = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) := by
  intro O _ _ R _ _ _ σ P
  classical
  rw [← P.part 1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ Ideal.span (Set.range fun i : Fin P.g =>
        (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin P.a ⊕ Fin P.g) O)) := by
      refine ep_odd_span_X Sum.inr Finset.univ f fun n hn => hf n ?_
      have : Finsupp.weight (Space.Loc.par P.a P.g) n = 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        refine Finset.sum_eq_zero fun s _ => ?_
        rcases s with s | s
        · simp [Space.Loc.par]
        · simp [hn s (Finset.mem_univ _)]
      rw [this]
      decide
    have h2 := Ideal.mem_map_of_mem P.p h1
    rw [Ideal.map_span, ← Set.range_comp] at h2
    exact h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨MvPowerSeries.X (.inr i), fun n hn => ?_, rfl⟩
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply hn
    simp [Finsupp.weight_single, Space.Loc.par]
