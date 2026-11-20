import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffSubstEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeriesStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

/- English proof (translation)
Introduce `d q hq M ω θ hd h16 hs hL hM hθ`. Take `⟨-, h2, -, h4, -⟩` from `GlobalTheory.MomOne.okArith d q M.ι hd h16 hs`. Take `⟨α, hα, hα1, hα2⟩` from `h4 1 1 (Nat.coprime_one_left q)`. Take `⟨⟨a, ha⟩, ⟨m, hm⟩, -⟩` from `h2 α hα`. Establish `hq1 : (q : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1`.

Establish `: (1 : ℝ) < q` using `by exact_mod_cast hq.out.one_lt`. Conclude with `zpow_lt_one_of_neg₀ this (by norm_num)`. Establish `hα1' : ‖M.ι α - 1‖ < 1`. Use `hα1.trans_lt hq1` as an intermediate fact. Simplify using `using this`.

Establish `hn : ‖M.ι α‖ = 1`. Establish `h` using `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := M.ι α - 1) (y := (1 : ℂ_[q])) (by rw [norm_one]; exact hα1'.ne)`. Rewrite `h` using `[sub_add_cancel, norm_one, max_eq_right hα1'.le]`. Conclude with `h`. Establish `hα0 : α ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hn`. Establish `hmn : ‖(m : ℂ_[q])‖ < 1`. Establish `: (m : ℂ_[q]) = M.ι α * M.ι (conj α)`. Rewrite using `[← map_mul, ← hm, map_natCast]`.

Rewrite using `[this, norm_mul, hn, one_mul]`. Conclude with `hα2.trans_lt hq1`. Establish `hm2 : 2 ≤ m`. Break down `m with _ | _ | m` into its components or cases. It suffices to derive a contradiction.

Establish `: α * conj α = 0` using `by rw [← hm]; simp`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `hα0 h`. Conclude with `hα0 (by simpa using h)`. Simplify using `at hmn`.

Use linear arithmetic over natural numbers and integers. Take `⟨ε, -, hεa, -, hεb, hfe, -⟩` from `GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries d q M ω θ hd h16 hs hL hM hθ α m hα hα0 hm`. Take `⟨hmul, -⟩` from `GlobalTheory.MomOne.MulSeries.mulS_laws q`. Take `⟨hb, hc0, hc1, -⟩` from `hmul a`. Establish `hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0`.

Rewrite using `[map_mul]`. Establish `: constantCoeff (logS : ℂ_[q]⟦X⟧) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Simplify using `[logS]`. Rewrite using `[this, mul_zero]`.

Take `⟨hring, hconst, -, hcc, -⟩` from `GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hℓ`. Establish `hθa : ∀ z, AnalyticAt ℂ θ z` using `fun z => hθ.1.analyticAt z`. Establish `hpow : ∀ k : ℕ, hat M.ι (C ω * logS) (fun z => θ z ^ k) = hat M.ι (C ω * logS) θ ^ k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hconst 1`. Consider the case `succ k ih`. Use `(hring (fun z => θ z ^ k) θ ((hθa 0).pow k) (hθa 0)).2.1` as an intermediate fact. Simplify using `only [pow_succ]`. Rewrite using `[this, ih]`.

Establish `hsub` using `(GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω θ (hθa 0)).2.2.1 α a ha`. Establish `hne : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0` using `(hθa 0).continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)`. Establish `hαa : AnalyticAt ℂ (fun z => θ (α * z)) 0` using `(hθ.1.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => α * z))).analyticAt 0`. Establish `heq` using `(hring (fun z => θ (α * z)) (fun z => θ z ^ m * ε z) hαa (((hθa 0).pow m).mul hεa)).2.2.1 ((hne.mono fun z hz => hfe z hz).filter_mono nhdsWithin_le_nhds)`. Rewrite `heq` using `[hsub, (hring (fun z => θ z ^ m) ε ((hθa 0).pow m) hεa).2.1, hpow]`.

Use `(GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m hc0 (by rw [hc1, ← ha, hn]) hmn hm2).2 _ _ hb hεb ?_ heq` and prove the remaining obligations. Rewrite using `[hcc, hθ.2.1, map_one]`.
-/
theorem theta_series_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 →
    Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  intro d q hq M ω θ hd h16 hs hL hM hθ
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd h16 hs
  obtain ⟨α, hα, hα1, hα2⟩ := h4 1 1 (Nat.coprime_one_left q)
  obtain ⟨⟨a, ha⟩, ⟨m, hm⟩, -⟩ := h2 α hα
  have hq1 : (q : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    exact zpow_lt_one_of_neg₀ this (by norm_num)
  have hα1' : ‖M.ι α - 1‖ < 1 := by
    have := hα1.trans_lt hq1
    simpa using this
  have hn : ‖M.ι α‖ = 1 := by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := M.ι α - 1) (y := (1 : ℂ_[q]))
      (by rw [norm_one]; exact hα1'.ne)
    rw [sub_add_cancel, norm_one, max_eq_right hα1'.le] at h
    exact h
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hn
  have hmn : ‖(m : ℂ_[q])‖ < 1 := by
    have : (m : ℂ_[q]) = M.ι α * M.ι (conj α) := by
      rw [← map_mul, ← hm, map_natCast]
    rw [this, norm_mul, hn, one_mul]
    exact hα2.trans_lt hq1
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · exfalso
      have : α * conj α = 0 := by rw [← hm]; simp
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    · simp at hmn
    · omega
  obtain ⟨ε, -, hεa, -, hεb, hfe, -⟩ := GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries d q M ω θ hd h16 hs hL hM hθ α m hα hα0 hm
  obtain ⟨hmul, -⟩ := GlobalTheory.MomOne.MulSeries.mulS_laws q
  obtain ⟨hb, hc0, hc1, -⟩ := hmul a
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [map_mul]
    have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; simp [logS]
    rw [this, mul_zero]
  obtain ⟨hring, hconst, -, hcc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  have hθa : ∀ z, AnalyticAt ℂ θ z := fun z => hθ.1.analyticAt z
  have hpow : ∀ k : ℕ, hat M.ι (C ω * logS) (fun z => θ z ^ k) = hat M.ι (C ω * logS) θ ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have := (hring (fun z => θ z ^ k) θ ((hθa 0).pow k) (hθa 0)).2.1
      simp only [pow_succ]
      rw [this, ih]
  have hsub := (GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω θ (hθa 0)).2.2.1 α a ha
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 :=
    (hθa 0).continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)
  have hαa : AnalyticAt ℂ (fun z => θ (α * z)) 0 :=
    (hθ.1.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => α * z))).analyticAt 0
  have heq := (hring (fun z => θ (α * z)) (fun z => θ z ^ m * ε z) hαa (((hθa 0).pow m).mul hεa)).2.2.1
    ((hne.mono fun z hz => hfe z hz).filter_mono nhdsWithin_le_nhds)
  rw [hsub, (hring (fun z => θ z ^ m) ε ((hθa 0).pow m) hεa).2.1, hpow] at heq
  refine (GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m hc0 (by rw [hc1, ← ha, hn]) hmn hm2).2 _ _ hb hεb ?_ heq
  rw [hcc, hθ.2.1, map_one]

end GlobalTheory.MomOne
