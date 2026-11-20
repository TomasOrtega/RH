import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FrequencyIndexing

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
  ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la P hP ξ hξ x hx s hs`. Take `⟨hξΛ, hξ0, -⟩` from `id hξ`. Choose the witnesses or unpack the hypotheses as in `⟨n, ω, hω⟩ : ∃ (n : ℕ) (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)), Submodule.span ℤ (Set.range ω) = perL X la := by`. Set `b` to `(Module.Free.chooseBasis ℤ (perL X la)).reindex (Fintype.equivFin _)`. Conclude with `⟨_, b.ofZLatticeBasis ℝ (perL X la), b.ofZLatticeBasis_span ℝ (perL X la)⟩`.

Establish `hωp : ∀ j, ω j ∈ X.periods la`. Introduce `j`. Establish `h1 : ω j ∈ perL X la`. Rewrite using `[← hω]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.

Conclude with `h1`. Establish `hsurj : ∀ u : X.Ψ → ℂ, ∃ t : Fin n → ℂ, TubeSummability.Lc X ω t = u`. Introduce `u`. Use `⟨fun j => (ω.repr (fun τ => (u τ).re) j : ℂ) + (ω.repr (fun τ => (u τ).im) j : ℂ) * I, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`.

Establish `hre : ∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ = (u τ).re`. Use `congrFun (ω.sum_repr (fun τ => (u τ).re)) τ` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, smul_eq_mul]`. Establish `him : ∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ = (u τ).im`. Use `congrFun (ω.sum_repr (fun τ => (u τ).im)) τ` as an intermediate fact.

Simplify `this` using `[Finset.sum_apply, smul_eq_mul]`. Simplify using `only [TubeSummability.Lc]`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`. Use `_ = u τ := by`. Rewrite using `[hre, him]`. Conclude with `Complex.re_add_im (u τ)`. Take `⟨t, rfl⟩` from `hsurj s`.

Establish `ht : t ∈ tube n (TubeSummability.Om X ξ x ω)` using `(TubeSummability.flow_Lc_mem_dom (ω := ω) hξ0 hx t).mp hs`. Establish `hΩ` using `TubeSummability.Om_open_convex (ξ := ξ) (ω := ω) hx`. Establish `hexp : HasSum (fun k : Fin n → ℤ => fourCoeff (TubeSummability.hline X P ξ x ω) 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * t j)) (P (X.flow ξ (TubeSummability.Lc X ω t) x))` using `(TubeFourierExpansion.tube_expansion (TubeSummability.Om X ξ x ω) (TubeSummability.hline X P ξ x ω) hΩ.1 hΩ.2 (TubeSummability.zero_mem_Om (ω := ω) hξ0 hx) (TubeSummability.hline_diff (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω) hP hξ0 hx) (TubeSummability.hline_period …`. Use `((FrequencyIndexing.νk_injective (ω := ω)).hasSum_iff ?_).mp ?_` and prove the remaining obligations. Introduce `ν hν`.

Establish `hfj : X.fj la ξ ν P x = 0`. Rewrite using `[Data.fj]`. Use `if_neg ?_` and prove the remaining obligations. Introduce `hall`. Apply `hν` to reduce the goal to its premises.

Use `choose k hk using fun j => hall (ω j) (hωp j)`. Conclude with `⟨k, (FrequencyIndexing.eq_νk (ω := ω) ν k hk).symm⟩`. Simplify using `only [hfj, zero_mul]`. Use `hexp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply]`. Use `congr 1`. Conclude with `FlowMeanContinuity.fj_eq_fourCoeff (X := X) (la := la) P hP hξ hx ω hω (FrequencyIndexing.νk ω k) k (FrequencyIndexing.νk_spec (ω := ω) k)`. Use `congr 1`. Establish `key : ∀ j, ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * (ω j τ : ℂ) = (k j : ℂ) / 2`.

Introduce `j`. Establish `h2` using `FrequencyIndexing.νk_spec (ω := ω) k j`. Establish `h3 : ∑ τ, FrequencyIndexing.νk ω k τ * ω j τ = (k j : ℝ) / 2` using `by linarith`. Conclude with `h3` after adjusting the coercions. Establish `hsw : ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * TubeSummability.Lc X ω t τ = ∑ j, t j * ((k j : ℂ) / 2)`.

Simplify using `only [TubeSummability.Lc, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[← key j, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun τ _ => by ring)`.

Rewrite using `[hsw, Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`.
-/
theorem m3bExp_holds : FourierJacobiExpansion (E := E) := by
  classical
  intro r X la P hP ξ hξ x hx s hs
  obtain ⟨hξΛ, hξ0, -⟩ := id hξ

  obtain ⟨n, ω, hω⟩ : ∃ (n : ℕ) (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)),
      Submodule.span ℤ (Set.range ω) = perL X la := by
    let b := (Module.Free.chooseBasis ℤ (perL X la)).reindex (Fintype.equivFin _)
    exact ⟨_, b.ofZLatticeBasis ℝ (perL X la), b.ofZLatticeBasis_span ℝ (perL X la)⟩
  have hωp : ∀ j, ω j ∈ X.periods la := by
    intro j
    have h1 : ω j ∈ perL X la := by
      rw [← hω]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact h1

  have hsurj : ∀ u : X.Ψ → ℂ, ∃ t : Fin n → ℂ, TubeSummability.Lc X ω t = u := by
    intro u
    refine ⟨fun j => (ω.repr (fun τ => (u τ).re) j : ℂ) +
      (ω.repr (fun τ => (u τ).im) j : ℂ) * I, ?_⟩
    funext τ
    have hre : ∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ = (u τ).re := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).re)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    have him : ∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ = (u τ).im := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).im)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    simp only [TubeSummability.Lc]
    calc _ = ((∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ : ℝ) : ℂ) +
          ((∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ : ℝ) : ℂ) * I := by
          push_cast
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = u τ := by
          rw [hre, him]
          exact Complex.re_add_im (u τ)
  obtain ⟨t, rfl⟩ := hsurj s
  have ht : t ∈ tube n (TubeSummability.Om X ξ x ω) :=
    (TubeSummability.flow_Lc_mem_dom (ω := ω) hξ0 hx t).mp hs
  have hΩ := TubeSummability.Om_open_convex (ξ := ξ) (ω := ω) hx
  have hexp : HasSum (fun k : Fin n → ℤ =>
      fourCoeff (TubeSummability.hline X P ξ x ω) 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * t j))
      (P (X.flow ξ (TubeSummability.Lc X ω t) x)) :=
    (TubeFourierExpansion.tube_expansion (TubeSummability.Om X ξ x ω) (TubeSummability.hline X P ξ x ω) hΩ.1 hΩ.2
      (TubeSummability.zero_mem_Om (ω := ω) hξ0 hx) (TubeSummability.hline_diff (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω) hP hξ0 hx)
      (TubeSummability.hline_periodic (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω)
        hP hξΛ hξ0 hx hωp) t ht).2
  refine ((FrequencyIndexing.νk_injective (ω := ω)).hasSum_iff ?_).mp ?_
  · intro ν hν
    have hfj : X.fj la ξ ν P x = 0 := by
      rw [Data.fj]
      refine if_neg ?_
      intro hall
      apply hν
      choose k hk using fun j => hall (ω j) (hωp j)
      exact ⟨k, (FrequencyIndexing.eq_νk (ω := ω) ν k hk).symm⟩
    simp only [hfj, zero_mul]
  · convert hexp using 1
    funext k
    simp only [Function.comp_apply]
    congr 1
    · exact FlowMeanContinuity.fj_eq_fourCoeff (X := X) (la := la) P hP hξ hx ω hω
        (FrequencyIndexing.νk ω k) k (FrequencyIndexing.νk_spec (ω := ω) k)
    · congr 1
      have key : ∀ j, ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * (ω j τ : ℂ) = (k j : ℂ) / 2 := by
        intro j
        have h2 := FrequencyIndexing.νk_spec (ω := ω) k j
        have h3 : ∑ τ, FrequencyIndexing.νk ω k τ * ω j τ = (k j : ℝ) / 2 := by linarith
        exact_mod_cast h3
      have hsw : ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * TubeSummability.Lc X ω t τ =
          ∑ j, t j * ((k j : ℂ) / 2) := by
        simp only [TubeSummability.Lc, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← key j, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun τ _ => by ring)
      rw [hsw, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

end ReciprocityTheory.ChartRestriction.G.FD
