import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

/- English proof (translation)
Introduce `k _ d φ hφ g`. Establish `ha : ∀ p : Fin 1 × Fin d, constantCoeff (![φ] p.1 p.2) = 0`. Introduce and unpack `⟨i, j⟩`. Use `fin_cases i`. Simplify using `using hφ j`.

Establish `hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![φ] p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Unfold `ev`. Rewrite using `[MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `e he`.

Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, e p ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Establish `h0 : constantCoeff (e.prod fun s n => (![φ] s.1 s.2) ^ n) = 0`.

Rewrite using `[Finsupp.prod, map_prod]`. Apply `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)` to reduce the goal to its premises. Rewrite using `[map_pow, ha p, zero_pow hp]`. Rewrite using `[h0, smul_zero]`.
-/
theorem constSt : ConstSt := by
  intro k _ d φ hφ g
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff (![φ] p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    simpa using hφ j
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![φ] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h0 : constantCoeff (e.prod fun s n => (![φ] s.1 s.2) ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, ha p, zero_pow hp]
    rw [h0, smul_zero]

open scoped MvPowerSeries.WithPiTopology in

/- English proof (translation)
Use `continuous_pi fun n => ?_` and prove the remaining obligations. Establish `h : (fun f : MvPowerSeries σ R => (pderiv R i f) n) = (fun a : R => a * ((n i : R) + 1)) ∘ ⇑(MvPowerSeries.coeff (n + Finsupp.single i 1))`. Use function extensionality and compare the values at `f`. Conclude with `MvPowerSeries.coeff_pderiv f n`. Rewrite using `[h]`.

Conclude with `continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)`.
-/
theorem continuous_pderiv_disc {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by
  refine continuous_pi fun n => ?_
  have h : (fun f : MvPowerSeries σ R => (pderiv R i f) n) =
      (fun a : R => a * ((n i : R) + 1)) ∘ ⇑(MvPowerSeries.coeff (n + Finsupp.single i 1)) := by
    funext f
    exact MvPowerSeries.coeff_pderiv f n
  rw [h]
  exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)

end ReciprocityTheory.ChartRestriction.G.TB
