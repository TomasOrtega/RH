import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds

namespace ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients

open NumberField Complex MeasureTheory ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
  ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

/- English proof (translation)
Rewrite using `[← intervalIntegral.integral_of_le zero_le_one]`. Use `split_ifs with hm`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm`.

Establish `hc : (2 * Real.pi * I * (m : ℂ)) ≠ 0`. Establish `: (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `[this, Complex.I_ne_zero, hm']`. Rewrite using `[integral_exp_mul_complex hc]`. Establish `h1 : cexp (2 * Real.pi * I * (m : ℂ) * ((1 : ℝ) : ℂ)) = 1`.

Rewrite using `[show 2 * (Real.pi : ℂ) * I * (m : ℂ) * ((1 : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
lemma ioc_orth (m : ℤ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, cexp (2 * Real.pi * I * (m : ℂ) * (t : ℂ)) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm; simp
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hc : (2 * Real.pi * I * (m : ℂ)) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, Complex.I_ne_zero, hm']
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * Real.pi * I * (m : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * I * (m : ℂ) * ((1 : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]
    simp

/- English proof (translation)
Establish `hprod : ∀ t : Fin n → ℝ, cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) = ∏ j, cexp (2 * Real.pi * I * (m j : ℂ) * (t j : ℂ))`. Introduce `t`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`. Conclude with `Finset.prod_congr rfl fun j _ => by ring_nf`. Repeatedly rewrite using `[hprod]`.

Rewrite using `[show (volume : Measure (Fin n → ℝ)) = Measure.pi fun _ => volume from rfl, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (fun (j : Fin n) (t : ℝ) => cexp (2 * Real.pi * I * (m j : ℂ) * (t : ℂ)))]`. Repeatedly rewrite using `[ioc_orth]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hm]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, m j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hm (funext h)`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)`.
-/
lemma cube_orth {n : ℕ} (m : Fin n → ℤ) :
    ∫ t in Set.univ.pi (fun _ : Fin n => Set.Ioc (0 : ℝ) 1),
      cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) = if m = 0 then 1 else 0 := by
  have hprod : ∀ t : Fin n → ℝ, cexp (2 * Real.pi * I * ∑ j, (m j : ℂ) * (t j : ℂ)) =
      ∏ j, cexp (2 * Real.pi * I * (m j : ℂ) * (t j : ℂ)) := by
    intro t
    rw [Finset.mul_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun j _ => by ring_nf
  simp_rw [hprod]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi fun _ => volume from rfl,
    Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (j : Fin n) (t : ℝ) => cexp (2 * Real.pi * I * (m j : ℂ) * (t : ℂ)))]
  simp_rw [ioc_orth]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra h; push Not at h; exact hm (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `p hp`. Establish `hp' : p ∈ Submodule.span ℤ (Set.range β)` using `by rw [hβ]; exact hp`. Take `⟨c, hc⟩` from `Submodule.mem_span_range_iff_exists_fun ℤ |>.mp hp'`. Use `⟨∑ j, c j * k j, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`.

Use `push_cast`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [zsmul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hk j, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma freq_of_basis {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {n : ℕ}
    (β : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)) (hβ : Submodule.span ℤ (Set.range β) = perL X la)
    (ν : X.Ψ → ℝ) (k : Fin n → ℤ) (hk : ∀ i, 2 * ∑ τ, ν τ * β i τ = k i) :
    ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν τ * p τ = z := by
  intro p hp
  have hp' : p ∈ Submodule.span ℤ (Set.range β) := by rw [hβ]; exact hp
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℤ |>.mp hp'
  refine ⟨∑ j, c j * k j, ?_⟩
  rw [← hc]
  push_cast
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hk j, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/- English proof (translation)
Take `⟨hξΛ, hξh, hξ0⟩` from `hξ`. Take `⟨β, hβ⟩` from `exists_basis X la`. Establish `hβp : ∀ j, β j ∈ X.periods la` using `fun j => by`. Establish `: β j ∈ Submodule.span ℤ (Set.range β)` using `Submodule.subset_span ⟨j, rfl⟩`. Rewrite `this` using `[hβ]`.

Conclude with `this`. Use `set a : (Fin (Fintype.card X.Ψ) → ℤ) → ℂ := fun k' => X.fj la ξ (νk β k') P x with ha`. Take `⟨hΩo, hΩc⟩` from `Om_open_convex (ξ := ξ) (⇑β) hx`. Establish `h0 : (0 : Fin (Fintype.card X.Ψ) → ℝ) ∈ Om X ξ x β` using `zero_mem_Om (⇑β) hξh hx`. Establish `h0t : (0 : Fin (Fintype.card X.Ψ) → ℂ) ∈ tube (Fintype.card X.Ψ) (Om X ξ x β)` using `by show (fun j => ((0 : Fin (Fintype.card X.Ψ) → ℂ) j).im) ∈ Om X ξ x β`.

Use `h0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Take `⟨hsumβ, -⟩` from `tube_expansion _ _ hΩo hΩc h0 (hline_diff X la P ξ x β hP hξh hx) (hline_periodic X la P ξ x β hP hξΛ hξh hx hβp) 0 h0t`. Establish `hak : ∀ k', a k' = fourCoeff (hline X P ξ x β) 0 k'` using `fun k' => fj_eq_fourCoeff X la P hP ⟨hξΛ, hξh, hξ0⟩ hx β hβ (νk β k') k' (νk_spec β k')`.

Establish `hsa : Summable (fun k' => ‖a k'‖)` using `hsumβ.congr fun k' => by`. Rewrite using `[hak k']`. Simplify using the standard rewrite rules. Use `choose mZ hmZ using fun (k' : Fin (Fintype.card X.Ψ) → ℤ) j => freq_of_basis X la β hβ (νk β k') k' (νk_spec β k') (ω j) (hωp j)`. Use `set sR : (Fin (Fintype.card X.Ψ) → ℝ) → X.Ψ → ℝ := fun t τ => ∑ j, t j * ω j τ with hsR`.

Establish `hexp : ∀ t : Fin (Fintype.card X.Ψ) → ℝ, HasSum ((fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * cexp (4 * Real.pi * I * ∑ τ, (ν' τ : ℂ) * ((sR t τ : ℝ) : ℂ))) ∘ νk β) (P (X.flow ξ (fun τ => ((sR t τ : ℝ) : ℂ)) x))`. Introduce `t`. Establish `hdom` using `flow_real_mem_dom X hξh (sR t) x hx`. Establish `hH` using `m3bExp_holds r X la P hP ξ ⟨hξΛ, hξh, hξ0⟩ x hx _ hdom`. Use `(Function.Injective.hasSum_iff (νk_injective β) ?_).mpr hH` and prove the remaining obligations.

Introduce `ν' hν'`. Establish `hnf : ¬ ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν' τ * p τ = z`. Introduce `hfreq`. Apply `hν'` to reduce the goal to its premises. Use `choose k0 hk0 using fun j => hfreq (β j) (hβp j)`.

Conclude with `⟨k0, (eq_νk β ν' k0 hk0).symm⟩`. Rewrite using `[Data.fj, if_neg hnf, zero_mul]`. Use `set F : (Fin (Fintype.card X.Ψ) → ℤ) → (Fin (Fintype.card X.Ψ) → ℝ) → ℂ := fun k' t => a k' * cexp (2 * Real.pi * I * ∑ j, ((mZ k' j - k j : ℤ) : ℂ) * (t j : ℂ)) with hF`. Establish `hexpF : ∀ k' t, ((fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * cexp (4 * Real.pi * I * ∑ τ, (ν' τ : ℂ) * ((sR t τ : ℝ) : ℂ))) ∘ νk β) k' * cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I)) = F k' t`. Introduce `k' t`.

Simplify using `only [Function.comp_apply, hF, ha, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero]`. Rewrite using `[mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Establish `hpair : ∀ j, ∑ τ, ((νk β k' τ : ℝ) : ℂ) * (ω j τ : ℂ) = (mZ k' j : ℂ) / 2`. Introduce `j`.

Establish `h2 : ((2 * ∑ τ, νk β k' τ * ω j τ : ℝ) : ℂ) = (mZ k' j : ℂ)` using `by rw [hmZ k' j]; simp`. Move the coercions through the operations in `at h2`. Take the linear combination `h2 / 2`. Establish `hsum : ∑ τ, ((νk β k' τ : ℝ) : ℂ) * ((sR t τ : ℝ) : ℂ) = (∑ j, (mZ k' j : ℂ) * (t j : ℂ)) / 2`. Simplify using `only [hsR]`.

Use `push_cast`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, Finset.sum_div]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring`. Use `_ = (mZ k' j : ℂ) * (t j : ℂ) / 2 := by rw [hpair j]; ring`. Rewrite using `[hsum]`. Use `push_cast`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∀ t ∈ Set.univ.pi (fun _ : Fin (Fintype.card X.Ψ) => Set.Ioc (0 : ℝ) 1), (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)) (fun j => (t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I) * cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((t j : ℂ) + ((0 : Fin (Fint …`. Introduce `t _`. Establish `harg : X.flow ξ (fun τ => ∑ j, ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I) * (ω j τ : ℂ)) x = X.flow ξ (fun τ => ((sR t τ : ℝ) : ℂ)) x`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Simplify using `[hsR]`. Simplify using `only`. Rewrite using `[harg, ← (hexp t).tsum_eq, ← tsum_mul_right]`. Conclude with `tsum_congr fun k' => hexpF k' t`.

Unfold `fourCoeff`. Rewrite using `[setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) hint]`. Establish `hnormF : ∀ k' t, ‖F k' t‖ = ‖a k'‖`. Introduce `k' t`. Simplify using `only [hF, norm_mul]`.

Rewrite using `[show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_exp_real_I (2 * Real.pi) (fun j => mZ k' j - k j) t, mul_one]`. Establish `hvol : volume (Set.univ.pi fun _ : Fin (Fintype.card X.Ψ) => Set.Ioc (0 : ℝ) 1) = 1`. Rewrite using `[Real.volume_pi_Ioc]`. Simplify using the standard rewrite rules. Establish `hFint : ∀ k', IntegrableOn (F k') (Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1)`.

Introduce `k'`. Use `Measure.integrableOn_of_bounded (M := ‖a k'‖) (by rw [hvol]; exact ENNReal.one_ne_top) ?_ (Filter.Eventually.of_forall fun t => (hnormF k' t).le)` and prove the remaining obligations. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Simplify using `only [hF]`. Use `fun_prop`.

Establish `hFsum : Summable fun k' => ∫ t in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1), ‖F k' t‖`. Use `hsa.congr fun k' => ?_` and prove the remaining obligations. Repeatedly rewrite using `[hnormF]`. Rewrite using `[setIntegral_const, measureReal_def, hvol]`. Simplify using the standard rewrite rules.

Rewrite using `[← integral_tsum_of_summable_integral_norm hFint hFsum]`. Establish `hcoef : ∀ k', ∫ t in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1), F k' t = a k' * (if (fun j => mZ k' j - k j) = 0 then 1 else 0)`. Introduce `k'`. Simplify using `only [hF]`. Rewrite using `[integral_const_mul]`.

Rewrite using `[cube_orth (fun j => mZ k' j - k j)]`. Repeatedly rewrite using `[hcoef]`. Establish `hcard : Fintype.card (Fin (Fintype.card X.Ψ)) = Module.finrank ℝ (X.Ψ → ℝ)`. Simplify using `[Module.finrank_fintype_fun_eq_card]`. Establish `hΨ : Nonempty X.Ψ`.

Take `⟨τ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `h : τ0 ∈ X.Ψ`. Conclude with `⟨⟨τ0, h⟩⟩`. Conclude with `⟨⟨_, by_contra fun hc => h ((X.cmType τ0).mpr hc)⟩⟩`. Establish `: Nonempty (Fin (Fintype.card X.Ψ))` using `Fin.pos_iff_nonempty.mp Fintype.card_pos`.

Use `set ωB := basisOfLinearIndependentOfCardEqFinrank hωi hcard with hωBdef`. Establish `hωB : ∀ j, ωB j = ω j` using `fun j => by simp [hωBdef]`. Establish `hsame : ∀ k', (fun j => mZ k' j - k j) = 0 → νk β k' = ν`. Introduce `k' h`. Establish `hm : ∀ j, mZ k' j = k j` using `fun j => by`.

Use `congrFun h j` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Use linear arithmetic over natural numbers and integers. Establish `e1 : νk β k' = νk ωB k` using `eq_νk ωB (νk β k') k (fun j => by`. Rewrite using `[hωB, hmZ k' j, hm j])`.

Establish `e2 : ν = νk ωB k` using `eq_νk ωB ν k (fun j => by rw [hωB]; exact (hk j).symm)`. Rewrite using `[e1, ← e2]`. Distinguish the cases in `hfreq : ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν τ * p τ = z`. Use `choose k0 hk0 using fun j => hfreq (β j) (hβp j)`. Establish `hν0 : ν = νk β k0` using `eq_νk β ν k0 hk0`.

Establish `huniq : ∀ k', (fun j => mZ k' j - k j) = 0 → k' = k0` using `fun k' h => νk_injective β (by rw [hsame k' h, hν0])`. Establish `hk0z : (fun j => mZ k0 j - k j) = 0`. Use function extensionality and compare the values at `j`. Establish `h1 : (mZ k0 j : ℝ) = k j` using `by rw [← hmZ k0 j, ← hν0, hk j]`. Establish `h2 : mZ k0 j = k j` using `by exact_mod_cast h1`.

Simplify using `only [Pi.zero_apply]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[tsum_eq_single k0 (fun k' hk' => by rw [if_neg (fun h => hk' (huniq k' h)), mul_zero]), if_pos hk0z, mul_one, ha]`. Use `show X.fj la ξ (νk β k0) P x = _`. Rewrite using `[← hν0]`.

Establish `hz : X.fj la ξ ν P x = 0` using `by rw [Data.fj, if_neg hfreq]`. Rewrite using `[hz]`. Establish `hterm : ∀ k', a k' * (if (fun j => mZ k' j - k j) = 0 then (1 : ℂ) else 0) = 0`. Introduce `k'`. Rewrite using `[if_neg, mul_zero]`.

Introduce `h`. Apply `hfreq` to reduce the goal to its premises. Rewrite using `[← hsame k' h]`. Conclude with `freq_of_basis X la β hβ (νk β k') k' (νk_spec β k')`. Simplify using `only [hterm, tsum_zero]`.
-/
theorem subCoeff {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : X.IsSec la P) (ξ : Fin r → E) (hξ : X.IsIso ξ) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) (hωp : ∀ j, ω j ∈ X.periods la)
    (hωi : LinearIndependent ℝ ω) (k : Fin (Fintype.card X.Ψ) → ℤ) (ν : X.Ψ → ℝ)
    (hk : ∀ j, (k j : ℝ) = 2 * ∑ τ, ν τ * ω j τ) :
    fourCoeff (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)) 0 k = X.fj la ξ ν P x := by
  classical
  obtain ⟨hξΛ, hξh, hξ0⟩ := hξ
  obtain ⟨β, hβ⟩ := exists_basis X la
  have hβp : ∀ j, β j ∈ X.periods la := fun j => by
    have : β j ∈ Submodule.span ℤ (Set.range β) := Submodule.subset_span ⟨j, rfl⟩
    rw [hβ] at this; exact this
  set a : (Fin (Fintype.card X.Ψ) → ℤ) → ℂ := fun k' => X.fj la ξ (νk β k') P x with ha

  obtain ⟨hΩo, hΩc⟩ := Om_open_convex (ξ := ξ) (⇑β) hx
  have h0 : (0 : Fin (Fintype.card X.Ψ) → ℝ) ∈ Om X ξ x β := zero_mem_Om (⇑β) hξh hx
  have h0t : (0 : Fin (Fintype.card X.Ψ) → ℂ) ∈ tube (Fintype.card X.Ψ) (Om X ξ x β) := by
    show (fun j => ((0 : Fin (Fintype.card X.Ψ) → ℂ) j).im) ∈ Om X ξ x β
    convert h0 using 1
    funext j
    simp
  obtain ⟨hsumβ, -⟩ := tube_expansion _ _ hΩo hΩc h0 (hline_diff X la P ξ x β hP hξh hx)
    (hline_periodic X la P ξ x β hP hξΛ hξh hx hβp) 0 h0t
  have hak : ∀ k', a k' = fourCoeff (hline X P ξ x β) 0 k' := fun k' =>
    fj_eq_fourCoeff X la P hP ⟨hξΛ, hξh, hξ0⟩ hx β hβ (νk β k') k' (νk_spec β k')
  have hsa : Summable (fun k' => ‖a k'‖) := hsumβ.congr fun k' => by
    rw [hak k']; simp

  choose mZ hmZ using fun (k' : Fin (Fintype.card X.Ψ) → ℤ) j =>
    freq_of_basis X la β hβ (νk β k') k' (νk_spec β k') (ω j) (hωp j)

  set sR : (Fin (Fintype.card X.Ψ) → ℝ) → X.Ψ → ℝ := fun t τ => ∑ j, t j * ω j τ with hsR
  have hexp : ∀ t : Fin (Fintype.card X.Ψ) → ℝ, HasSum
      ((fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x *
        cexp (4 * Real.pi * I * ∑ τ, (ν' τ : ℂ) * ((sR t τ : ℝ) : ℂ))) ∘ νk β)
      (P (X.flow ξ (fun τ => ((sR t τ : ℝ) : ℂ)) x)) := by
    intro t
    have hdom := flow_real_mem_dom X hξh (sR t) x hx
    have hH := m3bExp_holds r X la P hP ξ ⟨hξΛ, hξh, hξ0⟩ x hx _ hdom
    refine (Function.Injective.hasSum_iff (νk_injective β) ?_).mpr hH
    intro ν' hν'
    have hnf : ¬ ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν' τ * p τ = z := by
      intro hfreq
      apply hν'
      choose k0 hk0 using fun j => hfreq (β j) (hβp j)
      exact ⟨k0, (eq_νk β ν' k0 hk0).symm⟩
    rw [Data.fj, if_neg hnf, zero_mul]

  set F : (Fin (Fintype.card X.Ψ) → ℤ) → (Fin (Fintype.card X.Ψ) → ℝ) → ℂ := fun k' t =>
    a k' * cexp (2 * Real.pi * I * ∑ j, ((mZ k' j - k j : ℤ) : ℂ) * (t j : ℂ)) with hF
  have hexpF : ∀ k' t, ((fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x *
      cexp (4 * Real.pi * I * ∑ τ, (ν' τ : ℂ) * ((sR t τ : ℝ) : ℂ))) ∘ νk β) k' *
      cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I)) =
      F k' t := by
    intro k' t
    simp only [Function.comp_apply, hF, ha, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    have hpair : ∀ j, ∑ τ, ((νk β k' τ : ℝ) : ℂ) * (ω j τ : ℂ) = (mZ k' j : ℂ) / 2 := by
      intro j
      have h2 : ((2 * ∑ τ, νk β k' τ * ω j τ : ℝ) : ℂ) = (mZ k' j : ℂ) := by rw [hmZ k' j]; simp
      push_cast at h2
      linear_combination h2 / 2
    have hsum : ∑ τ, ((νk β k' τ : ℝ) : ℂ) * ((sR t τ : ℝ) : ℂ) =
        (∑ j, (mZ k' j : ℂ) * (t j : ℂ)) / 2 := by
      simp only [hsR]
      push_cast
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc ∑ τ, ((νk β k' τ : ℝ) : ℂ) * ((t j : ℂ) * (ω j τ : ℂ))
          = (t j : ℂ) * ∑ τ, ((νk β k' τ : ℝ) : ℂ) * (ω j τ : ℂ) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
        _ = (mZ k' j : ℂ) * (t j : ℂ) / 2 := by rw [hpair j]; ring
    rw [hsum]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hint : ∀ t ∈ Set.univ.pi (fun _ : Fin (Fintype.card X.Ψ) => Set.Ioc (0 : ℝ) 1),
      (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x))
        (fun j => (t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I) *
      cexp (-2 * Real.pi * I *
        ∑ j, (k j : ℂ) * ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I)) =
      ∑' k', F k' t := by
    intro t _
    have harg : X.flow ξ (fun τ => ∑ j, ((t j : ℂ) + ((0 : Fin (Fintype.card X.Ψ) → ℝ) j : ℂ) * I) *
        (ω j τ : ℂ)) x = X.flow ξ (fun τ => ((sR t τ : ℝ) : ℂ)) x := by
      congr 1
      funext τ
      simp [hsR]
    dsimp only
    rw [harg, ← (hexp t).tsum_eq, ← tsum_mul_right]
    exact tsum_congr fun k' => hexpF k' t
  unfold fourCoeff
  rw [setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) hint]
  have hnormF : ∀ k' t, ‖F k' t‖ = ‖a k'‖ := by
    intro k' t
    simp only [hF, norm_mul]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      norm_exp_real_I (2 * Real.pi) (fun j => mZ k' j - k j) t, mul_one]
  have hvol : volume (Set.univ.pi fun _ : Fin (Fintype.card X.Ψ) => Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_pi_Ioc]; simp
  have hFint : ∀ k', IntegrableOn (F k') (Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1) := by
    intro k'
    refine Measure.integrableOn_of_bounded (M := ‖a k'‖) (by rw [hvol]; exact ENNReal.one_ne_top)
      ?_ (Filter.Eventually.of_forall fun t => (hnormF k' t).le)
    refine Continuous.aestronglyMeasurable ?_
    simp only [hF]
    fun_prop
  have hFsum : Summable fun k' => ∫ t in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1), ‖F k' t‖ := by
    refine hsa.congr fun k' => ?_
    simp_rw [hnormF]
    rw [setIntegral_const, measureReal_def, hvol]; simp
  rw [← integral_tsum_of_summable_integral_norm hFint hFsum]
  have hcoef : ∀ k', ∫ t in Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1), F k' t =
      a k' * (if (fun j => mZ k' j - k j) = 0 then 1 else 0) := by
    intro k'
    simp only [hF]
    rw [integral_const_mul]
    rw [cube_orth (fun j => mZ k' j - k j)]
  simp_rw [hcoef]
  have hcard : Fintype.card (Fin (Fintype.card X.Ψ)) = Module.finrank ℝ (X.Ψ → ℝ) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hΨ : Nonempty X.Ψ := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨⟨τ0, h⟩⟩
    · exact ⟨⟨_, by_contra fun hc => h ((X.cmType τ0).mpr hc)⟩⟩
  have : Nonempty (Fin (Fintype.card X.Ψ)) := Fin.pos_iff_nonempty.mp Fintype.card_pos
  set ωB := basisOfLinearIndependentOfCardEqFinrank hωi hcard with hωBdef
  have hωB : ∀ j, ωB j = ω j := fun j => by simp [hωBdef]
  have hsame : ∀ k', (fun j => mZ k' j - k j) = 0 → νk β k' = ν := by
    intro k' h
    have hm : ∀ j, mZ k' j = k j := fun j => by
      have := congrFun h j; simp only [Pi.zero_apply] at this; omega
    have e1 : νk β k' = νk ωB k := eq_νk ωB (νk β k') k (fun j => by
      rw [hωB, hmZ k' j, hm j])
    have e2 : ν = νk ωB k := eq_νk ωB ν k (fun j => by rw [hωB]; exact (hk j).symm)
    rw [e1, ← e2]
  by_cases hfreq : ∀ p ∈ X.periods la, ∃ z : ℤ, 2 * ∑ τ, ν τ * p τ = z
  · choose k0 hk0 using fun j => hfreq (β j) (hβp j)
    have hν0 : ν = νk β k0 := eq_νk β ν k0 hk0
    have huniq : ∀ k', (fun j => mZ k' j - k j) = 0 → k' = k0 := fun k' h =>
      νk_injective β (by rw [hsame k' h, hν0])
    have hk0z : (fun j => mZ k0 j - k j) = 0 := by
      funext j
      have h1 : (mZ k0 j : ℝ) = k j := by rw [← hmZ k0 j, ← hν0, hk j]
      have h2 : mZ k0 j = k j := by exact_mod_cast h1
      simp only [Pi.zero_apply]
      omega
    rw [tsum_eq_single k0 (fun k' hk' => by rw [if_neg (fun h => hk' (huniq k' h)), mul_zero]),
      if_pos hk0z, mul_one, ha]
    show X.fj la ξ (νk β k0) P x = _
    rw [← hν0]
  · have hz : X.fj la ξ ν P x = 0 := by rw [Data.fj, if_neg hfreq]
    rw [hz]
    have hterm : ∀ k', a k' * (if (fun j => mZ k' j - k j) = 0 then (1 : ℂ) else 0) = 0 := by
      intro k'
      rw [if_neg, mul_zero]
      intro h
      apply hfreq
      rw [← hsame k' h]
      exact freq_of_basis X la β hβ (νk β k') k' (νk_spec β k')
    simp only [hterm, tsum_zero]

end ReciprocityTheory.ChartRestriction.G.FD.SublatticeCoefficients
