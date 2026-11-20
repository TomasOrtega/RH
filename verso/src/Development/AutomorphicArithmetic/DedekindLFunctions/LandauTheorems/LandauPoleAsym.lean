import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCauchy

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Rewrite using `[iteratedDeriv_const_mul_field]`. Use `congr 1`. Establish `e` using `congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) ρ) z`. Rewrite using `[e, iteratedDeriv_eq_iterate, show (fun t : ℂ => t⁻¹) = Inv.inv from rfl, iter_deriv_inv, show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]`.
-/
theorem landau_pole_asym_deriv (c ρ z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => c * (s - ρ)⁻¹) z
      = c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹) := by
  rw [iteratedDeriv_const_mul_field]
  congr 1
  have e := congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) ρ) z
  rw [e, iteratedDeriv_eq_iterate, show (fun t : ℂ => t⁻¹) = Inv.inv from rfl, iter_deriv_inv,
    show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

/- English proof (translation)
Take `⟨hfun, han, hev⟩` from `hp`. Establish `hopen : IsOpen (Metric.ball z r \ {ρ})` using `Metric.isOpen_ball.sdiff isClosed_singleton`. Use `set G : ℂ → ℂ := fun s => if s = ρ then hfun ρ else Φ s - c / (s - ρ) with hG`. Establish `hGeq : G =ᶠ[𝓝 ρ] hfun`. Rewrite `hev` using `[eventually_nhdsWithin_iff]`.

Use `filter_upwards [hev] with s hs`. Distinguish the cases in `hsρ : s = ρ`. Rewrite using `[hsρ]`. Simplify using `[G]`. Simplify using `only [G, if_neg hsρ]`.

Rewrite using `[hs (Set.mem_compl_singleton_iff.mpr hsρ)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGd : DifferentiableOn ℂ G (Metric.ball z r)`. Introduce `s hs`. Distinguish the cases in `hsρ : s = ρ`.

Rewrite using `[hsρ]`. Conclude with `((hGeq.differentiableAt_iff).mpr han.differentiableAt).differentiableWithinAt`. Establish `hmem : s ∈ Metric.ball z r \ {ρ}` using `⟨hs, hsρ⟩`. Establish `hΦ : DifferentiableAt ℂ Φ s` using `(hd s hmem).differentiableAt (hopen.mem_nhds hmem)`. Establish `hloc : G =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ)` using `by filter_upwards [hopen.mem_nhds hmem] with t ht`.

Establish `htρ : t ≠ ρ` using `ht.2`. Simplify using `only [G, if_neg htρ]`. Establish `hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s` using `hΦ.sub ((differentiableAt_const c).div (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))`. Conclude with `((hloc.differentiableAt_iff).mpr hd').differentiableWithinAt`. Take `⟨M, hM⟩` from `landau_cauchy hGd h0 h1`.

Use `⟨M, fun k => ?_⟩` and prove the remaining obligations. Establish `hzρ : z ≠ ρ` using `Ne.symm hne`. Establish `hr : 0 < r` using `lt_trans h0 h1`. Establish `hmemz : z ∈ Metric.ball z r \ {ρ}` using `⟨Metric.mem_ball_self hr, hzρ⟩`. Establish `hloc : Φ =ᶠ[𝓝 z] G + fun s => c * (s - ρ)⁻¹` using `by filter_upwards [hopen.mem_nhds hmemz] with t ht`.

Establish `htρ : t ≠ ρ` using `ht.2`. Simplify using `only [Pi.add_apply, G, if_neg htρ, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGc : ContDiffAt ℂ k G z` using `(hGd.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))`. Establish `hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z`.

Establish `hs : ContDiffAt ℂ k (fun s : ℂ => s - ρ) z` using `contDiffAt_id.sub contDiffAt_const`. Conclude with `contDiffAt_const.mul (hs.inv (sub_ne_zero.mpr hzρ))`. Rewrite using `[hloc.iteratedDeriv_eq, iteratedDeriv_add hGc hPc, landau_pole_asym_deriv]`. Establish `hfac : (k.factorial : ℂ) ≠ 0` using `by exact_mod_cast k.factorial_ne_zero`. Establish `hpow : ((-1 : ℂ)) ^ k * (-1) ^ k = 1` using `by rw [← mul_pow]; norm_num`.

Use `set iG := iteratedDeriv k G z`. Use `set X := (z - ρ) ^ (k + 1)`. Establish `e : (-1) ^ k * (iG + c * ((-1) ^ k * (k.factorial : ℂ) * X⁻¹)) / (k.factorial : ℂ) - c / X = (-1) ^ k * (iG / k.factorial)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`.

Conclude with `hM k`.
-/
theorem landau_pole_asym {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ} (hρ : ρ ∈ Metric.ball z r) (hne : ρ ≠ z)
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ) - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨hfun, han, hev⟩ := hp
  have hopen : IsOpen (Metric.ball z r \ {ρ}) := Metric.isOpen_ball.sdiff isClosed_singleton
  set G : ℂ → ℂ := fun s => if s = ρ then hfun ρ else Φ s - c / (s - ρ) with hG
  have hGeq : G =ᶠ[𝓝 ρ] hfun := by
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      simp [G]
    · simp only [G, if_neg hsρ]
      rw [hs (Set.mem_compl_singleton_iff.mpr hsρ)]
      ring
  have hGd : DifferentiableOn ℂ G (Metric.ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      exact ((hGeq.differentiableAt_iff).mpr han.differentiableAt).differentiableWithinAt
    · have hmem : s ∈ Metric.ball z r \ {ρ} := ⟨hs, hsρ⟩
      have hΦ : DifferentiableAt ℂ Φ s := (hd s hmem).differentiableAt (hopen.mem_nhds hmem)
      have hloc : G =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ) := by
        filter_upwards [hopen.mem_nhds hmem] with t ht
        have htρ : t ≠ ρ := ht.2
        simp only [G, if_neg htρ]
      have hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s :=
        hΦ.sub ((differentiableAt_const c).div
          (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))
      exact ((hloc.differentiableAt_iff).mpr hd').differentiableWithinAt
  obtain ⟨M, hM⟩ := landau_cauchy hGd h0 h1
  refine ⟨M, fun k => ?_⟩
  have hzρ : z ≠ ρ := Ne.symm hne
  have hr : 0 < r := lt_trans h0 h1
  have hmemz : z ∈ Metric.ball z r \ {ρ} := ⟨Metric.mem_ball_self hr, hzρ⟩
  have hloc : Φ =ᶠ[𝓝 z] G + fun s => c * (s - ρ)⁻¹ := by
    filter_upwards [hopen.mem_nhds hmemz] with t ht
    have htρ : t ≠ ρ := ht.2
    simp only [Pi.add_apply, G, if_neg htρ, div_eq_mul_inv]
    ring
  have hGc : ContDiffAt ℂ k G z :=
    (hGd.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z := by
    have hs : ContDiffAt ℂ k (fun s : ℂ => s - ρ) z := contDiffAt_id.sub contDiffAt_const
    exact contDiffAt_const.mul (hs.inv (sub_ne_zero.mpr hzρ))
  rw [hloc.iteratedDeriv_eq, iteratedDeriv_add hGc hPc, landau_pole_asym_deriv]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpow : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  set iG := iteratedDeriv k G z
  set X := (z - ρ) ^ (k + 1)
  have e : (-1) ^ k * (iG + c * ((-1) ^ k * (k.factorial : ℂ) * X⁻¹)) / (k.factorial : ℂ) - c / X
      = (-1) ^ k * (iG / k.factorial) := by
    calc _ = (-1) ^ k * (iG / k.factorial) + ((-1) ^ k * (-1) ^ k) * c *
          ((k.factorial : ℂ) / k.factorial) * X⁻¹ - c / X := by ring
      _ = _ := by rw [hpow, div_self hfac, div_eq_mul_inv c]; ring
  rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hM k

end Deduction

end
