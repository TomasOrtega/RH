import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `n ε lam h T μ hlam hgap hN hq hμ`. Establish `hg : GapLap ε lam h` using `⟨hlam.1, hgap, hN⟩`. Establish `hstd` using `stdGap_of_gapLap hg`. Establish `h8 : 8 * (n : ℝ) * S7.q0 ε < h`. Establish `h1` using `lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN`.

Establish `e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ)` using `by simp [S7.q0, Nat.cast_min]`. Rewrite `h1` using `[e]`. Establish `: 0 ≤ (n : ℝ) * S7.q0 ε` using `by positivity`. Use polynomial arithmetic with `[Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))]`. Establish `hP` using `S7.isPsiFor_psiM ε lam h T μ hlam hμ hgap hq h8`.

Use `set Ψ := S7.PsiM T μ with hΨ`. Apply the tactic sequence `replace hP : IsPsiFor ε lam T Ψ := by first | exact hP | exact hP.1`. Establish `hv₀ : T.w ≠ 0` using `fun h0 => by`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one h1`. Establish `hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0` using `norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hstd hP hv₀)`. Use `set c : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) with hc`. Establish `hc0 : c ≠ 0` using `by rw [hc]; exact_mod_cast inv_ne_zero hN0`. Set `j : T.V →ₗ[ℂ] datumV ε Ψ T.w` to `{ toFun := fun v => ⟨⟨uniformisationL2 ε Ψ T.w (c • v), datumEmbedding_mem_smooth hP T.w _⟩, (mem_datumV_iff hP T.w _).2 ⟨c • v, rfl⟩⟩ map_add' := fun v v' => Subtype.ext (Subtype.ext (by show uniformisationL2 ε Ψ T.w (c • (v + v')) = uniformisationL2 ε Ψ T.w (c • v) + uniformisa …`.

Rewrite using `[smul_add, datumEmbedding_add hP]))`. Use the proof step `map_smul' := fun a v => Subtype.ext (Subtype.ext (by show uniformisationL2 ε Ψ T.w (c • (a • v)) = a • uniformisationL2 ε Ψ T.w (c • v)`. Rewrite using `[smul_comm, datumEmbedding_smul hP])) }`. Establish `hj : Function.Bijective j`. Use `⟨fun v v' hv => ?_, fun x => ?_⟩` and prove the remaining obligations.

Establish `: uniformisationL2 ε Ψ T.w (c • v) = uniformisationL2 ε Ψ T.w (c • v')` using `congrArg (fun x : datumV ε Ψ T.w => ((x : smD ε (rreg ε)) : L2 ε)) hv`. Conclude with `smul_right_injective _ hc0 (uniformisationL2_injective hP hv₀ this)`. Take `⟨v, hv⟩` from `(mem_datumV_iff hP T.w x).1 x.2`. Use `⟨c⁻¹ • v, Subtype.ext (Subtype.ext ?_)⟩` and prove the remaining obligations. Use `show uniformisationL2 ε Ψ T.w (c • c⁻¹ • v) = _`.

Rewrite using `[smul_smul, mul_inv_cancel₀ hc0, one_smul, hv]`. Set `e` to `LinearEquiv.ofBijective j hj`. Use `⟨L2 ε, inferInstance, inferInstance, inferInstance, rreg ε, smD ε (rreg ε), smE ε (rreg ε), datumV ε Ψ T.w, e.symm, rreg_isURepOn ε, isDerivedOn_smE (rreg_isURepOn ε), datumV_isKIrrHW hP hv₀, datumV_casimir hP T.w, datumV_kStable hP T.w, fun g hgm v v' => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `e.surjective v`. Take `⟨x', rfl⟩` from `e.surjective v'`.

Rewrite using `[e.symm_apply_apply, e.symm_apply_apply]`. Use `show ⟪uniformisationL2 ε Ψ T.w (c • x'), rreg ε g (uniformisationL2 ε Ψ T.w (c • x))⟫_ℂ = _`. Establish `key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1`. Rewrite using `[hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]`. Use `congr 1`.

Rewrite using `[pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]`. Rewrite using `[formulaF hstd hP hv₀ hgm, map_smul, inner_smul_left, inner_smul_right]`. Take the linear combination `⟪x', Ψ g x⟫_ℂ * key`.
-/
theorem psiDatum : PsiDatumStatement := by
  intro n ε lam h T μ hlam hgap hN hq hμ
  have hg : GapLap ε lam h := ⟨hlam.1, hgap, hN⟩
  have hstd := stdGap_of_gapLap hg
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
    have e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by simp [S7.q0, Nat.cast_min]
    rw [e] at h1
    have : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
    nlinarith [Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))]
  have hP := S7.isPsiFor_psiM ε lam h T μ hlam hμ hgap hq h8
  set Ψ := S7.PsiM T μ with hΨ
  replace hP : IsPsiFor ε lam T Ψ := by first | exact hP | exact hP.1
  have hv₀ : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hstd hP hv₀)
  set c : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast inv_ne_zero hN0
  let j : T.V →ₗ[ℂ] datumV ε Ψ T.w :=
    { toFun := fun v => ⟨⟨uniformisationL2 ε Ψ T.w (c • v), datumEmbedding_mem_smooth hP T.w _⟩,
        (mem_datumV_iff hP T.w _).2 ⟨c • v, rfl⟩⟩
      map_add' := fun v v' => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (v + v')) = uniformisationL2 ε Ψ T.w (c • v) + uniformisationL2 ε Ψ T.w (c • v')
        rw [smul_add, datumEmbedding_add hP]))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (a • v)) = a • uniformisationL2 ε Ψ T.w (c • v)
        rw [smul_comm, datumEmbedding_smul hP])) }
  have hj : Function.Bijective j := by
    refine ⟨fun v v' hv => ?_, fun x => ?_⟩
    · have : uniformisationL2 ε Ψ T.w (c • v) = uniformisationL2 ε Ψ T.w (c • v') :=
        congrArg (fun x : datumV ε Ψ T.w => ((x : smD ε (rreg ε)) : L2 ε)) hv
      exact smul_right_injective _ hc0 (uniformisationL2_injective hP hv₀ this)
    · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 x.2
      refine ⟨c⁻¹ • v, Subtype.ext (Subtype.ext ?_)⟩
      show uniformisationL2 ε Ψ T.w (c • c⁻¹ • v) = _
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, hv]
  let e := LinearEquiv.ofBijective j hj
  refine ⟨L2 ε, inferInstance, inferInstance, inferInstance, rreg ε, smD ε (rreg ε), smE ε (rreg ε),
    datumV ε Ψ T.w, e.symm, rreg_isURepOn ε, isDerivedOn_smE (rreg_isURepOn ε),
    datumV_isKIrrHW hP hv₀, datumV_casimir hP T.w, datumV_kStable hP T.w, fun g hgm v v' => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  obtain ⟨x', rfl⟩ := e.surjective v'
  rw [e.symm_apply_apply, e.symm_apply_apply]
  show ⟪uniformisationL2 ε Ψ T.w (c • x'), rreg ε g (uniformisationL2 ε Ψ T.w (c • x))⟫_ℂ = _
  have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
  rw [formulaF hstd hP hv₀ hgm, map_smul, inner_smul_left, inner_smul_right]
  linear_combination ⟪x', Ψ g x⟫_ℂ * key

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
