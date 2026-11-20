import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientEllipticStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegralStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeWeylOperatorEqThetaRootOfUnityShiftStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslateStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateLaw

variable {q : ℕ} [Fact q.Prime]

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `h`. Conclude with `⟨s * a, s * b, by push_cast; ring⟩`.
-/
theorem inOK_natMul {d : ℕ} (s : ℕ) {v : ℂ} (h : InOK d v) : InOK d ((s : ℂ) * v) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨s * a, s * b, by push_cast; ring⟩

/- English proof (translation)
Unfold `kap1`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Establish `: h1 d x ((s : ℂ) * y) = ((s : ℝ) : ℂ) * h1 d x y`. Simplify using `only [h1, map_mul, map_natCast, Complex.ofReal_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.im_ofReal_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeCommutatorPairing_natMul_right (d s : ℕ) (x y : ℂ) : kap1 d x ((s : ℂ) * y) = kap1 d x y ^ s := by
  unfold kap1
  rw [← Complex.exp_nat_mul]
  congr 1
  have : h1 d x ((s : ℂ) * y) = ((s : ℝ) : ℂ) * h1 d x y := by
    simp only [h1, map_mul, map_natCast, Complex.ofReal_natCast]; ring
  rw [this, Complex.im_ofReal_mul]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[PadicInt.norm_natCast_eq_one_iff]`. Conclude with `h.symm`.
-/
theorem norm_natCast_eq_one {s : ℕ} (h : Nat.Coprime s q) : ‖(s : ℤ_[q])‖ = 1 := by
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact h.symm

/- English proof (translation)
Simplify using `[zc]`.
-/
theorem zc_natCast (s : ℕ) : zc (s : ℤ_[q]) = (s : ℂ_[q]) := by
  simp [zc]

/- English proof (translation)
The claim follows from `HasSubst.of_constantCoeff_zero' ((MulSeries.mulS_laws q).1 a).2.1`.
-/
theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' ((MulSeries.mulS_laws q).1 a).2.1

/- English proof (translation)
Take `⟨u, rfl⟩` from `PadicInt.isUnit_iff.mpr ha`. Establish `key : ∀ f : ℂ_[q]⟦X⟧, PowerSeries.subst (mulS ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℂ_[q]⟦X⟧) (show ℂ_[q]⟦X⟧ from f.subst (mulS (u : ℤ_[q]) : ℂ_[q]⟦X⟧)) = f`. Introduce `f`. Simplify using `only`. Rewrite using `[subst_comp_subst_apply (hasSubst_mulS _) (hasSubst_mulS _), (MulSeries.mulS_laws q).2.1, Units.mul_inv, (MulSeries.mulS_laws q).2.2.1]`.

Rewrite using `[← map_algebraMap_eq_subst_X]`. Simplify using the standard rewrite rules. Establish `h1` using `key f`. Establish `h2` using `key g`. Simplify using `only at h1 h2`.

Rewrite using `[← h1, h, h2]`.
-/
theorem subst_mulS_cancel {a : ℤ_[q]} (ha : ‖a‖ = 1) {f g : ℂ_[q]⟦X⟧}
    (h : f.subst (mulS a : ℂ_[q]⟦X⟧) = g.subst (mulS a : ℂ_[q]⟦X⟧)) : f = g := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr ha
  have key : ∀ f : ℂ_[q]⟦X⟧, PowerSeries.subst (mulS ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℂ_[q]⟦X⟧)
      (show ℂ_[q]⟦X⟧ from f.subst (mulS (u : ℤ_[q]) : ℂ_[q]⟦X⟧)) = f := by
    intro f
    dsimp only
    rw [subst_comp_subst_apply (hasSubst_mulS _) (hasSubst_mulS _), (MulSeries.mulS_laws q).2.1,
      Units.mul_inv, (MulSeries.mulS_laws q).2.2.1]
    rw [← map_algebraMap_eq_subst_X]
    simp
  have h1 := key f
  have h2 := key g
  dsimp only at h1 h2
  rw [← h1, h, h2]

/- English proof (translation)
Introduce `d q hq M ω θ hd hd16 hsp hOK hM hθ hgood t y n s hs ht hy`. Take `⟨v, hv, hvn, hyv⟩` from `hy`. Establish `hs0 : 0 < s`. Break down `Nat.eq_zero_or_pos s with h | h` into its components or cases. Substitute `h` using the available equality.

Conclude with `absurd ((Nat.coprime_zero_left q).mp hs) hq.out.one_lt.ne'`. Conclude with `h`. Establish `hsC : (s : ℂ) ≠ 0` using `by exact_mod_cast hs0.ne'`. Establish `hsn : ‖(s : ℤ_[q])‖ = 1` using `norm_natCast_eq_one hs`. Establish `hιs : M.ι (s : ℂ) = zc (s : ℤ_[q])` using `by rw [zc_natCast, map_natCast]`.

Use `set y' : ℂ := v / (q : ℂ) ^ n with hy'`. Establish `hyy : y = (s : ℂ) * y'` using `by rw [hyv, hy']; ring`. Establish `hg' : Good M.ι d n 1 y'` using `⟨v, hv, hvn, by rw [hy']; simp⟩`. Establish `hg : Good M.ι d n 1 y`. Use `⟨(s : ℂ) * v, inOK_natMul s hv, ?_, by rw [hyv]; simp⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_natCast, hιs, norm_mul, (MulSeries.mulS_laws q).2.2.2.2.2, hsn, one_mul]`. Conclude with `hvn`. Take `⟨hζ, hAt⟩` from `hgood n y hg`. Take `⟨hζ', hAt'⟩` from `hgood n y' hg'`. Use `⟨hζ, ?_⟩` and prove the remaining obligations.

Establish `hζζ : M.ι (kap1 d 1 y) = M.ι (kap1 d 1 y') ^ s` using `by rw [hyy, cmLatticeCommutatorPairing_natMul_right, map_pow]`. Establish `hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0` using `hM.2.1`. Take `⟨hring, -⟩` from `TaylorRead.hat_laws q M.ι (C ω * logS) hℓ`. Take `⟨-, -, hdiff, -⟩` from `GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos`. Establish `hθd : Differentiable ℂ θ` using `hθ.1`.

Establish `hθ0 : θ 0 ≠ 0` using `by rw [hθ.2.1]; exact one_ne_zero`. Establish `hUd : Differentiable ℂ (U1 d t θ)` using `(hdiff t θ hθd).1`. Establish `hWUd : Differentiable ℂ (W1 d y (U1 d t θ))` using `(hdiff y _ hUd).2`. Establish `hWd : Differentiable ℂ (W1 d y θ)` using `(hdiff y _ hθd).2`. Use `set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf`.

Establish `hfa : AnalyticAt ℂ f 0` using `(hUd.analyticAt 0).div (hθd.analyticAt 0) hθ0`. Take `⟨hEll, hφa, -, -, hφb⟩` from `GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hOK hM hθ t s hs0 hs ht`. Establish `hscale : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → hat M.ι (C ω * logS) (fun z => G ((s : ℂ) * z)) = (hat M.ι (C ω * logS) G).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧)` using `fun G hG => (hat_multiplicative_chart q M.ι ω G hG).2.2.1 _ _ hιs`. Establish `hφf : hat M.ι (C ω * logS) (fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)) = (hat M.ι (C ω * logS) f).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧)` using `hscale f hfa`. Establish `hfb : Bdd (hat M.ι (C ω * logS) f)`.

Take `⟨B, hB⟩` from `hφb`. Rewrite `hB` using `[hφf]`. Conclude with `⟨B, ((MulSeries.mulS_laws q).2.2.2.1 _ _ B hsn).mp hB⟩`. Establish `hθb : Bdd (hat M.ι (C ω * logS) θ)` using `⟨1, GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hOK hM hθ⟩`. Take `⟨ψ, hψa, hψ, hψh⟩` from `GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω _ y' _ hM hAt' hEll hφa hφb`.

Rewrite `hψh` using `[hφf]`. Establish `hsc` using `((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n s (s : ℤ_[q]) _ hζ' (by`. Rewrite using `[sub_self, norm_zero]`. Use the proof step `positivity) hfb).2`. Rewrite `hψh` using `[hsc, ← hζζ]`.

Establish `hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z)` using `by fun_prop`. Establish `hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), θ ((s : ℂ) * z + y) ≠ 0`. Establish `hA : AnalyticOnNhd ℂ (fun z : ℂ => θ ((s : ℂ) * z + y)) Set.univ` using `fun z _ => (hθd.comp (hlin.add_const y)).analyticAt z`. Break down `(hA 0 trivial).eventually_eq_zero_or_eventually_ne_zero with h | h` into its components or cases. It suffices to derive a contradiction.

Use `hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h (Set.mem_univ (-y / (s : ℂ)))` as an intermediate fact. Apply `hθ0` to reduce the goal to its premises. Establish `e : (s : ℂ) * (-y / (s : ℂ)) + y = 0` using `by field_simp; ring`. Simplify `this` using `[e]`. Conclude with `h`.

Establish `hWs : AnalyticAt ℂ (fun z => W1 d y θ ((s : ℂ) * z)) 0` using `(hWd.comp hlin).analyticAt 0`. Establish `hWUs : AnalyticAt ℂ (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) 0` using `(hWUd.comp hlin).analyticAt 0`. Establish `hprod : hat M.ι (C ω * logS) (fun z => ψ z * W1 d y θ ((s : ℂ) * z)) = hat M.ι (C ω * logS) (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z))`. Use `(hring _ _ (hψa.mul hWs) hWUs).2.2.1 ?_` and prove the remaining obligations. Use `filter_upwards [hψ, hne] with z h1z h2z`.

Establish `e : (s : ℂ) * (z + y') = (s : ℂ) * z + y` using `by rw [hyy]; ring`. Express the relevant statement in the definitionally equal form `ψ z * W1 d y θ ((s : ℂ) * z) = _`. Rewrite using `[h1z, e]`. Simplify using `only [W1]`. Generalize the expression as in `U1 d t θ = G`.

Simplify using `only [U1]`. Clear the denominators using the available nonvanishing facts. Rewrite `hprod` using `[(hring _ _ hψa hWs).2.1, hψh, hscale _ (hWd.analyticAt 0), hscale _ (hWUd.analyticAt 0), ← subst_mul (hasSubst_mulS _)]`. Rewrite using `[← subst_mulS_cancel hsn hprod, GlobalTheory.T.cmLatticeWeylOperator_eq_theta_rootOfUnity_shift d q M ω θ hd hd16 hsp hOK hM hθ hgood n y hg, ← ((Shift.shift_laws q _ hAt.2.1).2.1 _ _ hfb hθb).2, ← (hring _ _ hfa (hθd.analyticAt 0)).2.1]`. Use `congr 1`.

Use `(hring _ _ (hfa.mul (hθd.analyticAt 0)) (hUd.analyticAt 0)).2.2.1 ?_` and prove the remaining obligations. Establish `: ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0` using `hθd.continuous.continuousAt.eventually_ne hθ0`. Use `filter_upwards [nhdsWithin_le_nhds this] with z hz`. Express the relevant statement in the definitionally equal form `U1 d t θ z / θ z * θ z = _`. Clear the denominators using the available nonvanishing facts.
-/
theorem main : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q hq M ω θ hd hd16 hsp hOK hM hθ hgood t y n s hs ht hy
  obtain ⟨v, hv, hvn, hyv⟩ := hy
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      exact absurd ((Nat.coprime_zero_left q).mp hs) hq.out.one_lt.ne'
    · exact h
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℤ_[q])‖ = 1 := norm_natCast_eq_one hs
  have hιs : M.ι (s : ℂ) = zc (s : ℤ_[q]) := by rw [zc_natCast, map_natCast]
  set y' : ℂ := v / (q : ℂ) ^ n with hy'
  have hyy : y = (s : ℂ) * y' := by rw [hyv, hy']; ring
  have hg' : Good M.ι d n 1 y' := ⟨v, hv, hvn, by rw [hy']; simp⟩
  have hg : Good M.ι d n 1 y := by
    refine ⟨(s : ℂ) * v, inOK_natMul s hv, ?_, by rw [hyv]; simp⟩
    rw [map_mul, map_mul, map_natCast, hιs, norm_mul, (MulSeries.mulS_laws q).2.2.2.2.2, hsn, one_mul]
    exact hvn
  obtain ⟨hζ, hAt⟩ := hgood n y hg
  obtain ⟨hζ', hAt'⟩ := hgood n y' hg'
  refine ⟨hζ, ?_⟩
  have hζζ : M.ι (kap1 d 1 y) = M.ι (kap1 d 1 y') ^ s := by rw [hyy, cmLatticeCommutatorPairing_natMul_right, map_pow]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  obtain ⟨hring, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  obtain ⟨-, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  have hθd : Differentiable ℂ θ := hθ.1
  have hθ0 : θ 0 ≠ 0 := by rw [hθ.2.1]; exact one_ne_zero
  have hUd : Differentiable ℂ (U1 d t θ) := (hdiff t θ hθd).1
  have hWUd : Differentiable ℂ (W1 d y (U1 d t θ)) := (hdiff y _ hUd).2
  have hWd : Differentiable ℂ (W1 d y θ) := (hdiff y _ hθd).2
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := (hUd.analyticAt 0).div (hθd.analyticAt 0) hθ0
  obtain ⟨hEll, hφa, -, -, hφb⟩ := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hOK hM hθ t s hs0 hs ht
  have hscale : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → hat M.ι (C ω * logS) (fun z => G ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) G).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) :=
    fun G hG => (hat_multiplicative_chart q M.ι ω G hG).2.2.1 _ _ hιs
  have hφf : hat M.ι (C ω * logS) (fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) f).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) := hscale f hfa
  have hfb : Bdd (hat M.ι (C ω * logS) f) := by
    obtain ⟨B, hB⟩ := hφb
    rw [hφf] at hB
    exact ⟨B, ((MulSeries.mulS_laws q).2.2.2.1 _ _ B hsn).mp hB⟩
  have hθb : Bdd (hat M.ι (C ω * logS) θ) := ⟨1, GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd hd16 hsp hOK hM hθ⟩
  obtain ⟨ψ, hψa, hψ, hψh⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω _ y' _ hM hAt' hEll hφa hφb
  rw [hφf] at hψh
  have hsc := ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n s (s : ℤ_[q]) _ hζ' (by
    rw [sub_self, norm_zero]; positivity) hfb).2
  rw [hsc, ← hζζ] at hψh

  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), θ ((s : ℂ) * z + y) ≠ 0 := by
    have hA : AnalyticOnNhd ℂ (fun z : ℂ => θ ((s : ℂ) * z + y)) Set.univ :=
      fun z _ => (hθd.comp (hlin.add_const y)).analyticAt z
    rcases (hA 0 trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h
        (Set.mem_univ (-y / (s : ℂ)))
      apply hθ0
      have e : (s : ℂ) * (-y / (s : ℂ)) + y = 0 := by field_simp; ring
      simpa [e] using this
    · exact h
  have hWs : AnalyticAt ℂ (fun z => W1 d y θ ((s : ℂ) * z)) 0 := (hWd.comp hlin).analyticAt 0
  have hWUs : AnalyticAt ℂ (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) 0 := (hWUd.comp hlin).analyticAt 0
  have hprod : hat M.ι (C ω * logS) (fun z => ψ z * W1 d y θ ((s : ℂ) * z)) =
      hat M.ι (C ω * logS) (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) := by
    refine (hring _ _ (hψa.mul hWs) hWUs).2.2.1 ?_
    filter_upwards [hψ, hne] with z h1z h2z
    have e : (s : ℂ) * (z + y') = (s : ℂ) * z + y := by rw [hyy]; ring
    change ψ z * W1 d y θ ((s : ℂ) * z) = _
    rw [h1z, e]
    simp only [W1]
    generalize U1 d t θ = G
    simp only [U1]
    field_simp
  rw [(hring _ _ hψa hWs).2.1, hψh, hscale _ (hWd.analyticAt 0), hscale _ (hWUd.analyticAt 0),
    ← subst_mul (hasSubst_mulS _)] at hprod
  rw [← subst_mulS_cancel hsn hprod, GlobalTheory.T.cmLatticeWeylOperator_eq_theta_rootOfUnity_shift d q M ω θ hd hd16 hsp hOK hM hθ hgood n y hg,
    ← ((Shift.shift_laws q _ hAt.2.1).2.1 _ _ hfb hθb).2, ← (hring _ _ hfa (hθd.analyticAt 0)).2.1]
  congr 1
  refine (hring _ _ (hfa.mul (hθd.analyticAt 0)) (hUd.analyticAt 0)).2.2.1 ?_
  have : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne hθ0
  filter_upwards [nhdsWithin_le_nhds this] with z hz
  change U1 d t θ z / θ z * θ z = _
  field_simp

end GlobalTheory.MomOne.TranslateLaw
