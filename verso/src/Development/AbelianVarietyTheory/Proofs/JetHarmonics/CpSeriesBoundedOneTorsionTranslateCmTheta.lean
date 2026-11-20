import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientEllipticStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLeStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateNorm

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `h`. Conclude with `⟨-u, -v, by push_cast; ring⟩`.
-/
theorem inOK_neg {d : ℕ} {z : ℂ} (h : InOK d z) : InOK d (-z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨-u, -v, by push_cast; ring⟩

/- English proof (translation)
Unfold `U1 h1`. Rewrite using `[← he (z + -t)]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_neg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslateValueAtZero_neg (d : ℕ) (θ : ℂ → ℂ) (he : ∀ z, θ (-z) = θ z) (t z : ℂ) :
    U1 d (-t) θ z = U1 d t θ (-z) := by
  unfold U1 h1
  rw [← he (z + -t)]
  congr 2
  · ring
  · simp only [map_neg]; ring

/- English proof (translation)
Unfold `U1 h1`. Establish `h0 : w + t + -t = w` using `by ring`. Rewrite using `[h0, mul_mul_mul_comm, ← Complex.exp_add]`. Establish `: -(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * (w * conj t)) - (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (t * conj t)) + (-(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * ((w + t) * conj (-t))) - (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (-t * conj (-t)))) = 0`. Simplify using `only [map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.exp_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeTranslationOperator_mul_neg_translate (d : ℕ) (θ : ℂ → ℂ) (t w : ℂ) :
    U1 d t θ w * U1 d (-t) θ (w + t) = θ w * θ (w + t) := by
  unfold U1 h1
  have h0 : w + t + -t = w := by ring
  rw [h0, mul_mul_mul_comm, ← Complex.exp_add]
  have : -(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * (w * conj t)) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (t * conj t)) +
      (-(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * ((w + t) * conj (-t))) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (-t * conj (-t)))) = 0 := by
    simp only [map_neg]; ring
  rw [this, Complex.exp_zero]; ring

/- English proof (translation)
Unfold `U1 h1`. Use `fun_prop`.
-/
theorem differentiable_cmLatticeTranslationOperator_of_diff (d : ℕ) (θ : ℂ → ℂ) (hθ : Differentiable ℂ θ) (t : ℂ) : Differentiable ℂ (U1 d t θ) := by
  unfold U1 h1
  fun_prop

/- English proof (translation)
Use `⟨fun x => ?_, fun l hl z => ?_⟩` and prove the remaining obligations. Establish `h1 : MeromorphicAt φ ((fun z : ℂ => z + a) x)` using `h.1 _`. Conclude with `h1.comp_analyticAt (f := φ) (g := fun z : ℂ => z + a) (by fun_prop)`. Use `h.2 l hl (z + a) show φ (z + l + a) = φ (z + a)` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ell_shift {L : PeriodPair} {φ : ℂ → ℂ} (h : Ell L φ) (a : ℂ) : Ell L (fun z => φ (z + a)) := by
  refine ⟨fun x => ?_, fun l hl z => ?_⟩
  · have h1 : MeromorphicAt φ ((fun z : ℂ => z + a) x) := h.1 _
    exact h1.comp_analyticAt (f := φ) (g := fun z : ℂ => z + a) (by fun_prop)
  · have := h.2 l hl (z + a)
    show φ (z + l + a) = φ (z + a)
    rw [← this]; congr 1; ring

/- English proof (translation)
Establish `h1 : Bd 1 (f * g)`. Rewrite using `[hfg]`. Introduce `n`. Rewrite using `[coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hm` using `(sup_norm_laws q).2.2.2.1 f g 1 hf hg h1`. Introduce `i`. Assume the negation of the conclusion as `hi`. Use `push_neg at hi`. Establish `hp : 0 < ‖coeff i f‖` using `lt_trans one_pos hi`.

Establish `hb : Bd (1 / ‖coeff i f‖) g` using `fun j => by`. Rewrite using `[le_div_iff₀ hp, mul_comm]`. Conclude with `hm i j`. Use `h _ hb i` as an intermediate fact. Rewrite `this` using `[le_div_iff₀ hp]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bd_one_of_inv {q : ℕ} [Fact q.Prime] (f g : ℂ_[q]⟦X⟧) (hf : Bdd f) (hg : Bdd g) (hfg : f * g = 1)
    (h : ∀ B, Bd B g → Bd B f) : Bd 1 f := by
  have h1 : Bd 1 (f * g) := by
    rw [hfg]
    intro n
    rw [coeff_one]
    split_ifs <;> simp
  have hm := (sup_norm_laws q).2.2.2.1 f g 1 hf hg h1
  intro i
  by_contra hi
  push_neg at hi
  have hp : 0 < ‖coeff i f‖ := lt_trans one_pos hi
  have hb : Bd (1 / ‖coeff i f‖) g := fun j => by
    rw [le_div_iff₀ hp, mul_comm]; exact hm i j
  have := h _ hb i
  rw [le_div_iff₀ hp] at this
  nlinarith

/- English proof (translation)
Introduce `d q _ M ω θ hd h16 hsp hOK hch hth t hpt hnt`. Take `⟨s, hs, hsq, hst⟩` from `id hpt`. Establish `hs0 : (s : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`. Take `⟨hdiff, h0, hev, -, hz⟩` from `id hth`. Establish `hθt : θ t ≠ 0` using `fun h => hnt (hz t h)`.

Establish `hP` using `GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd h16 hsp hOK hch hth t s hs hsq hst`. Establish `hN` using `GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd h16 hsp hOK hch hth (-t) s hs hsq (by have := inOK_neg hst; rwa [← mul_neg] at this)`. Simplify using `only at hP hN`. Use `set φp : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφp`. Use `set φm : ℂ → ℂ := fun z => U1 d (-t) θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφm`.

Take `⟨-, hPa, -, hPs, hPb⟩` from `hP`. Take `⟨hNe, hNa, hNp, -, hNb⟩` from `hN`. Use `set t' : ℂ := t / s with ht'`. Establish `hst' : (s : ℂ) * t' = t` using `by rw [ht']; field_simp`. Use `set ψ : ℂ → ℂ := fun z => φm (z + t') with hψ`.

Establish `hψe : Ell M.L ψ` using `ell_shift hNe t'`. Establish `hψan : ∀ p, AnalyticAt ℂ φm (p + t') → AnalyticAt ℂ ψ p` using `fun p hp => AnalyticAt.comp (g := φm) (f := fun z : ℂ => z + t') hp (by fun_prop)`. Establish `hψ0 : AnalyticAt ℂ ψ 0` using `hψan 0 (hNp _ (by rwa [zero_add, hst']))`. Establish `hψt : AnalyticAt ℂ ψ (-t')` using `hψan _ (by rwa [neg_add_cancel])`. Establish `hψp : ∀ p, meromorphicOrderAt ψ p < 0 → ¬ M.Small p`.

Introduce `p hp`. Apply `hPs p t hpt hnt` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`. Establish `: AnalyticAt ℂ ψ p` using `hψan p (hNp _ (by rwa [mul_add, hst']))`. Conclude with `absurd this.meromorphicOrderAt_nonneg (not_le.mpr hp)`.

Establish `hψb` using `GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ ψ hch hψe hψ0 hψp`. Establish `hback : (fun z => ψ (z + -t')) = φm`. Use function extensionality and compare the values at `z`. Simplify using `[hψ]`. Establish `hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0` using `hch.2.1`.

Establish `hat1` using `TaylorRead.hat_laws q M.ι _ hℓ`. Establish `hmul` using `MulSeries.mulS_laws q`. Establish `hb1 : ∀ B, Bd B (hat M.ι (C ω * logS) ψ) → Bd B (hat M.ι (C ω * logS) φm)`. Introduce `B hB`. Distinguish the cases in `hsm : M.Small (-t')`.

Establish `hin : InOK d (-t')` using `(GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd h16 hsp hOK hch).2.2.1 (-t') ⟨s * s, Nat.mul_pos hs hs, Nat.Coprime.mul_left hsq hsq, by`. Establish `: ((s * s : ℕ) : ℂ) * (-t') = -((s : ℂ) * t)`. Rewrite using `[← hst']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `inOK_neg hst⟩ hsm`. Establish `hl : t' ∈ M.L.lattice` using `(hOK t').2 (by simpa using inOK_neg hin)`. Establish `: ψ = φm` using `funext fun z => hNe.2 t' hl z`. Rewrite using `[← this]` and apply the resulting hypothesis.

Use `GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ ψ (-t') B hch hψe hψ0 hψt hψp hsm (by rwa [hback]) hB` as an intermediate fact. Rewrite `this` using `[hback]`. Then use the resulting hypothesis. Establish `hmp : φm = fun z => φp ((-1 : ℂ) * z)`. Use function extensionality and compare the values at `z`. Simplify using `only [hφm, hφp]`.

Rewrite using `[thetaTranslateValueAtZero_neg d θ hev, ← hev ((s : ℂ) * z)]`. Apply the tactic sequence `congr 2 <;> ring`. Establish `hb2 : ∀ B, Bd B (hat M.ι (C ω * logS) φm) → Bd B (hat M.ι (C ω * logS) φp)`. Introduce `B hB`. Rewrite `hB` using `[hmp, (hat_multiplicative_chart q M.ι ω φp hPa).2.2.1 (-1) (-1) (by simp [zc])]`.

Conclude with `(hmul.2.2.2.1 (-1) _ B (by simp)).1 hB`. Establish `hprod : hat M.ι (C ω * logS) φp * hat M.ι (C ω * logS) ψ = 1`. Rewrite using `[← (hat1.1 φp ψ hPa hψ0).2.1]`. Establish `hc` using `hat1.2.1 1`. Rewrite `hc` using `[map_one, map_one]`.

Rewrite using `[← hc]`. Apply `(hat1.1 _ _ (hPa.mul hψ0) analyticAt_const).2.2.1` to reduce the goal to its premises. Apply `Filter.Eventually.filter_mono nhdsWithin_le_nhds` to reduce the goal to its premises. Establish `c1 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z)) 0` using `(hdiff.continuous.comp (by fun_prop)).continuousAt`. Establish `c2 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z + t)) 0` using `(hdiff.continuous.comp (by fun_prop)).continuousAt`.

Use `filter_upwards [c1.eventually_ne (y := 0) (by simp [h0]), c2.eventually_ne (y := 0) (by simpa using hθt)] with z hz1 hz2`. Simplify using `only [hψ, hφm, hφp, Pi.mul_apply]`. Rewrite using `[mul_add, hst', div_mul_div_comm, cmLatticeTranslationOperator_mul_neg_translate]`. Conclude with `div_self (mul_ne_zero hz1 hz2)`. Establish `hP1 : Bd 1 (hat M.ι (C ω * logS) φp)` using `bd_one_of_inv _ _ hPb hψb hprod fun B hB => hb2 B (hb1 B hB)`.

Establish `hθa : AnalyticAt ℂ θ 0` using `hdiff.analyticAt 0`. Establish `hUa : AnalyticAt ℂ (U1 d t θ) 0` using `(differentiable_cmLatticeTranslationOperator_of_diff d θ hdiff t).analyticAt 0`. Use `set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf`. Establish `hfa : AnalyticAt ℂ f 0` using `hUa.div hθa (by simp [h0])`. Establish `hf1 : Bd 1 (hat M.ι (C ω * logS) f)`.

Establish `e` using `(hat_multiplicative_chart q M.ι ω f hfa).2.2.1 (s : ℂ) (s : ℤ_[q]) (by simp [zc])`. Establish `e' : φp = fun z => f ((s : ℂ) * z)` using `rfl`. Rewrite `hP1` using `[e', e]`. Conclude with `(hmul.2.2.2.1 (s : ℤ_[q]) _ 1 (PadicInt.norm_natCast_eq_one_iff.2 hsq.symm)).1 hP1`. Establish `hθ1` using `GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h16 hsp hOK hch hth`.

Establish `hfin : hat M.ι (C ω * logS) (U1 d t θ) = hat M.ι (C ω * logS) f * hat M.ι (C ω * logS) θ`. Rewrite using `[← (hat1.1 f θ hfa hθa).2.1]`. Apply `(hat1.1 _ _ hUa (hfa.mul hθa)).2.2.1` to reduce the goal to its premises. Apply `Filter.Eventually.filter_mono nhdsWithin_le_nhds` to reduce the goal to its premises. Use `filter_upwards [hdiff.continuous.continuousAt.eventually_ne (y := 0) (x := 0) (by simp [h0])] with z hz1`.

Simplify using `only [hf, Pi.mul_apply]`. Rewrite using `[div_mul_cancel₀ _ hz1]`. Rewrite using `[hfin]`. Simplify using `using ((sup_norm_laws q).1 _ _ 1 1 hf1 hθ1).2`.
-/
theorem bd_translate : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ t : ℂ, PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd 1 (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q _ M ω θ hd h16 hsp hOK hch hth t hpt hnt
  obtain ⟨s, hs, hsq, hst⟩ := id hpt
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨hdiff, h0, hev, -, hz⟩ := id hth
  have hθt : θ t ≠ 0 := fun h => hnt (hz t h)
  have hP := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd h16 hsp hOK hch hth t s hs hsq hst
  have hN := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd h16 hsp hOK hch hth (-t) s hs hsq
    (by have := inOK_neg hst; rwa [← mul_neg] at this)
  simp only at hP hN
  set φp : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφp
  set φm : ℂ → ℂ := fun z => U1 d (-t) θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφm
  obtain ⟨-, hPa, -, hPs, hPb⟩ := hP
  obtain ⟨hNe, hNa, hNp, -, hNb⟩ := hN
  set t' : ℂ := t / s with ht'
  have hst' : (s : ℂ) * t' = t := by rw [ht']; field_simp
  set ψ : ℂ → ℂ := fun z => φm (z + t') with hψ
  have hψe : Ell M.L ψ := ell_shift hNe t'
  have hψan : ∀ p, AnalyticAt ℂ φm (p + t') → AnalyticAt ℂ ψ p := fun p hp =>
    AnalyticAt.comp (g := φm) (f := fun z : ℂ => z + t') hp (by fun_prop)
  have hψ0 : AnalyticAt ℂ ψ 0 := hψan 0 (hNp _ (by rwa [zero_add, hst']))
  have hψt : AnalyticAt ℂ ψ (-t') := hψan _ (by rwa [neg_add_cancel])
  have hψp : ∀ p, meromorphicOrderAt ψ p < 0 → ¬ M.Small p := by
    intro p hp
    apply hPs p t hpt hnt
    by_contra hne
    have : AnalyticAt ℂ ψ p := hψan p (hNp _ (by rwa [mul_add, hst']))
    exact absurd this.meromorphicOrderAt_nonneg (not_le.mpr hp)
  have hψb := GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ ψ hch hψe hψ0 hψp
  have hback : (fun z => ψ (z + -t')) = φm := by
    funext z; simp [hψ]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hat1 := TaylorRead.hat_laws q M.ι _ hℓ
  have hmul := MulSeries.mulS_laws q

  have hb1 : ∀ B, Bd B (hat M.ι (C ω * logS) ψ) → Bd B (hat M.ι (C ω * logS) φm) := by
    intro B hB
    by_cases hsm : M.Small (-t')
    · have hin : InOK d (-t') := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd h16 hsp hOK hch).2.2.1 (-t')
        ⟨s * s, Nat.mul_pos hs hs, Nat.Coprime.mul_left hsq hsq, by
          have : ((s * s : ℕ) : ℂ) * (-t') = -((s : ℂ) * t) := by
            rw [← hst']; push_cast; ring
          rw [this]; exact inOK_neg hst⟩ hsm
      have hl : t' ∈ M.L.lattice := (hOK t').2 (by simpa using inOK_neg hin)
      have : ψ = φm := funext fun z => hNe.2 t' hl z
      rwa [← this]
    · have := GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ ψ (-t') B hch hψe hψ0 hψt hψp hsm (by rwa [hback]) hB
      rwa [hback] at this

  have hmp : φm = fun z => φp ((-1 : ℂ) * z) := by
    funext z
    simp only [hφm, hφp]
    rw [thetaTranslateValueAtZero_neg d θ hev, ← hev ((s : ℂ) * z)]
    congr 2 <;> ring
  have hb2 : ∀ B, Bd B (hat M.ι (C ω * logS) φm) → Bd B (hat M.ι (C ω * logS) φp) := by
    intro B hB
    rw [hmp, (hat_multiplicative_chart q M.ι ω φp hPa).2.2.1 (-1) (-1) (by simp [zc])] at hB
    exact (hmul.2.2.2.1 (-1) _ B (by simp)).1 hB

  have hprod : hat M.ι (C ω * logS) φp * hat M.ι (C ω * logS) ψ = 1 := by
    rw [← (hat1.1 φp ψ hPa hψ0).2.1]
    have hc := hat1.2.1 1
    rw [map_one, map_one] at hc
    rw [← hc]
    apply (hat1.1 _ _ (hPa.mul hψ0) analyticAt_const).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have c1 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    have c2 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z + t)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [c1.eventually_ne (y := 0) (by simp [h0]), c2.eventually_ne (y := 0) (by simpa using hθt)]
      with z hz1 hz2
    simp only [hψ, hφm, hφp, Pi.mul_apply]
    rw [mul_add, hst', div_mul_div_comm, cmLatticeTranslationOperator_mul_neg_translate]
    exact div_self (mul_ne_zero hz1 hz2)
  have hP1 : Bd 1 (hat M.ι (C ω * logS) φp) :=
    bd_one_of_inv _ _ hPb hψb hprod fun B hB => hb2 B (hb1 B hB)

  have hθa : AnalyticAt ℂ θ 0 := hdiff.analyticAt 0
  have hUa : AnalyticAt ℂ (U1 d t θ) 0 := (differentiable_cmLatticeTranslationOperator_of_diff d θ hdiff t).analyticAt 0
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := hUa.div hθa (by simp [h0])
  have hf1 : Bd 1 (hat M.ι (C ω * logS) f) := by
    have e := (hat_multiplicative_chart q M.ι ω f hfa).2.2.1 (s : ℂ) (s : ℤ_[q]) (by simp [zc])
    have e' : φp = fun z => f ((s : ℂ) * z) := rfl
    rw [e', e] at hP1
    exact (hmul.2.2.2.1 (s : ℤ_[q]) _ 1 (PadicInt.norm_natCast_eq_one_iff.2 hsq.symm)).1 hP1
  have hθ1 := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h16 hsp hOK hch hth
  have hfin : hat M.ι (C ω * logS) (U1 d t θ) = hat M.ι (C ω * logS) f * hat M.ι (C ω * logS) θ := by
    rw [← (hat1.1 f θ hfa hθa).2.1]
    apply (hat1.1 _ _ hUa (hfa.mul hθa)).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hdiff.continuous.continuousAt.eventually_ne (y := 0) (x := 0) (by simp [h0])] with z hz1
    simp only [hf, Pi.mul_apply]
    rw [div_mul_cancel₀ _ hz1]
  rw [hfin]
  simpa using ((sup_norm_laws q).1 _ _ 1 1 hf1 hθ1).2

end GlobalTheory.MomOne.TranslateNorm
