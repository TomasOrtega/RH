import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHermStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

/- English proof (translation)
Simplify using `only [Heisenberg₂, kerSum]`. Rewrite using `[← tsum_mul_right, ← tsum_mul_right]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [kerTerm, mul_assoc, ← Complex.exp_add]`. Use `congr 2`.

Establish `hc : ∀ w : ℂ, (starRingEnd ℂ) w = w - 2 * (w.im : ℂ) * I`. Introduce `w`. Apply the tactic sequence `apply Complex.ext <;> simp`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, LinearMap.add_apply, Complex.add_im, Complex.ofReal_add]`.

Rewrite using `[hH.1 z r, hH.1 z x, hH.1 r x]`. Simplify using `only [hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heis_kerSum_diag {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsPosHerm H)
    (Λ : AddSubgroup V) (α : V → ℂ) (r z : V) :
    Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z) =
      ∑' x : Λ, (α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2
        + 2 * π * I * ((H x r).im : ℂ))) * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := by
  simp only [Heisenberg₂, kerSum]
  rw [← tsum_mul_right, ← tsum_mul_right]
  refine tsum_congr fun x => ?_
  simp only [kerTerm, mul_assoc, ← Complex.exp_add]
  congr 2
  have hc : ∀ w : ℂ, (starRingEnd ℂ) w = w - 2 * (w.im : ℂ) * I := by
    intro w
    apply Complex.ext <;> simp
    ring
  simp only [map_add, LinearMap.add_apply, Complex.add_im, Complex.ofReal_add]
  rw [hH.1 z r, hH.1 z x, hH.1 r x]
  simp only [hc]
  ring

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H hH Λ Λ' _ hle α hα Fd hFd hFdfin r hr`. Establish `hΛc : Countable Λ` using `TopologicalSpace.separableSpace_iff_countable.mp inferInstance`. Establish `hΛ'c : Countable Λ'`. Establish `h1 : (Λ : Set V).Countable` using `Set.countable_coe_iff.mp hΛc`. Conclude with `(h1.mono (fun y hy => hle hy)).to_subtype`.

Take `⟨K, hK⟩ : ∃ K : ℝ, ∀ x : V, ‖H x r‖ ≤ K * ‖x‖` from `⟨‖LinearMap.toContinuousLinearMap (H.flip r)‖, fun x => by`. Simplify using `using (LinearMap.toContinuousLinearMap (H.flip r)).le_opNorm x⟩`. Establish `hcontH : ∀ v : V, Continuous fun z : V => H z v` using `fun v => Continuous.congr (H.flip v).continuous_of_finiteDimensional (fun z => LinearMap.flip_apply _ _ _)`. Establish `hcim : ∀ v : V, Continuous fun z : V => (H v z).im`. Introduce `v`.

Establish `e : (fun z : V => (H v z).im) = fun z => -(H z v).im`. Use function extensionality and compare the values at `z`. Rewrite using `[hH.1 v z, Complex.conj_im]`. Rewrite using `[e]`. Conclude with `(Complex.continuous_im.comp (hcontH v)).neg`.

Establish `he1 : ∀ t : ℝ, ‖cexp (2 * π * I * (t : ℂ))‖ = 1`. Introduce `t`. Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩ : ∃ c : Λ → ℂ, ∀ x, c x = α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2 + 2 * π * I * ((H x r).im : ℂ))` from `⟨_, fun _ => rfl⟩`.

Take `⟨F, hF⟩ : ∃ F : Λ → V → ℂ, ∀ x z, F x z = c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ))` from `⟨_, fun _ _ => rfl⟩`. Establish `hfun : (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) = fun z => ∑' x : Λ, F x z`. Use function extensionality and compare the values at `z`. Rewrite using `[heis_kerSum_diag H hH Λ α r z]`. Simplify using `only [hF, hc]`.

Establish `hre : ∀ x : Λ, (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2 + 2 * π * I * ((H x r).im : ℂ)).re = -π * (H x r).re - π / 2 * (H x x).re - π / 2 * (H r r).re`. Introduce `x`. Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcle : ∀ x : Λ, ‖c x‖ ≤ Real.exp (-(π / 2) * (H x x).re + π * K * ‖(x : V)‖) * Real.exp (-(π / 2) * (H r r).re)`.

Introduce `x`. Establish `hα1 : ‖α x‖ = 1`. Apply the tactic sequence `rcases hα.1 x x.2 with h | h <;> simp [h]`. Rewrite using `[hc, norm_mul, hα1, one_mul, Complex.norm_exp, hre, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `h1 : -(H x r).re ≤ K * ‖(x : V)‖`. Use `(abs_le.mp (Complex.abs_re_le_norm (H x r))).1` as an intermediate fact. Combine the linear relations using `[hK x]`. Establish `hπ : 0 ≤ π` using `Real.pi_pos.le`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hcsum : Summable fun x : Λ => ‖c x‖` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcle ((GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * K)).mul_right _)`. Establish `hFnorm : ∀ x z, ‖F x z‖ = ‖c x‖`. Introduce `x z`. Rewrite using `[hF, norm_mul, he1, mul_one]`. Establish `hFcont : ∀ x : Λ, Continuous (F x)`.

Introduce `x`. Establish `e : F x = fun z => c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ))` using `funext (hF x)`. Rewrite using `[e]`. Conclude with `continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (hcim _))))`. Establish `hsumcont : Continuous fun z => ∑' x : Λ, F x z` using `continuous_tsum hFcont hcsum (fun x z => (hFnorm x z).le)`.

Establish `hFs : ∀ z, Summable fun x : Λ => ‖F x z‖` using `fun z => by`. Simplify using `only [hFnorm]`. Conclude with `hcsum`. Establish `hbdd : ∀ z, ‖∑' x : Λ, F x z‖ ≤ ∑' x : Λ, ‖c x‖` using `fun z => by`. Use `(norm_tsum_le_tsum_norm (hFs z)).trans (le_of_eq ?_)` and prove the remaining obligations.

Simplify using `only [hFnorm]`. Establish `hFint : ∀ x : Λ, IntegrableOn (F x) Fd μ` using `fun x => Measure.integrableOn_of_bounded hFdfin (hFcont x).aestronglyMeasurable (Filter.Eventually.of_forall fun z => (hFnorm x z).le)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`. Conclude with `Measure.integrableOn_of_bounded hFdfin hsumcont.aestronglyMeasurable (Filter.Eventually.of_forall hbdd)`.

Rewrite using `[hfun]`. Establish `hnormint : (fun x : Λ => ∫ z in Fd, ‖F x z‖ ∂μ) = fun x => μ.real Fd * ‖c x‖`. Use function extensionality and compare the values at `x`. Simplify using `only [hFnorm]`. Rewrite using `[setIntegral_const, smul_eq_mul]`.

Rewrite using `[← integral_tsum_of_summable_integral_norm hFint (by rw [hnormint]; exact hcsum.mul_left _)]`. Establish `hint : ∀ x : Λ, ∫ z in Fd, F x z ∂μ = if (x : V) = -r then c x * (μ.real Fd : ℂ) else 0`. Introduce `x`. Simplify using `only [hF]`. Rewrite using `[integral_const_mul]`.

Use `split_ifs with hx`. Establish `h0 : r + (x : V) = 0`. Rewrite using `[hx]`. Normalize the expressions using the abelian group laws. Simplify using `only [h0, map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.ofReal_zero, mul_zero, Complex.exp_zero]`.

Rewrite using `[setIntegral_const, Complex.real_smul, mul_one]`. Establish `hne : r + (x : V) ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`.

Conclude with `h`. Rewrite using `[GlobalTheory.T.setIntegral_cexp_im_herm_eq_zero V μ H hH Λ' Fd hFd (r + x) hne ?_, mul_zero]`. Introduce `y hy`. Take `⟨m1, hm1⟩` from `hr y hy`. Take `⟨m2, hm2⟩` from `hα.2.1 x x.2 y (hle hy)`.

Use `⟨m1 + m2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, LinearMap.add_apply, Complex.add_im, hm1, hm2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hint]`.

Distinguish the cases in `hrΛ : r ∈ Λ`. Rewrite using `[if_pos hrΛ, tsum_eq_single ⟨-r, neg_mem hrΛ⟩]`. Establish `hcoe : ((⟨-r, neg_mem hrΛ⟩ : Λ) : V) = -r` using `rfl`. Establish `him : (H r r).im = 0` using `Complex.conj_eq_iff_im.mp (hH.1 r r).symm`. Establish `hA : cexp (-(π : ℂ) * H (-r) r - (π : ℂ) * H (-r) (-r) / 2 - (π : ℂ) * H r r / 2 + 2 * π * I * ((H (-r) r).im : ℂ)) = 1`.

Rewrite using `[← Complex.exp_zero]`. Use `congr 1`. Simplify using `only [map_neg, LinearMap.neg_apply, neg_neg, Complex.neg_im, him, neg_zero, Complex.ofReal_zero, mul_zero, add_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, hcoe, if_pos rfl, hA, mul_one]`.

Introduce `x hx`. Rewrite using `[if_neg]`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Conclude with `Subtype.ext h`.

Rewrite using `[if_neg hrΛ]`. Establish `hno : ∀ x : Λ, ¬ ((x : V) = -r)`. Introduce `x h`. Apply `hrΛ` to reduce the goal to its premises. Establish `hm` using `neg_mem x.2`.

Rewrite `hm` using `[h, neg_neg]`. Conclude with `hm`. Simplify using `[hno]`.
-/
theorem integral_heis_kerSum_diag : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → ∀ α : V → ℂ, IsSemichar H Λ α → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → μ Fd ≠ ⊤ → ∀ r : V, (∀ y ∈ Λ', ∃ m : ℤ, (H r y).im = m) → IntegrableOn (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) Fd μ ∧ ∫ z in Fd, Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z) ∂μ = if r ∈ Λ then α (-r) * (μ.real Fd : ℂ) else 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ Λ' _ hle α hα Fd hFd hFdfin r hr
  have hΛc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hΛ'c : Countable Λ' := by
    have h1 : (Λ : Set V).Countable := Set.countable_coe_iff.mp hΛc
    exact (h1.mono (fun y hy => hle hy)).to_subtype
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x : V, ‖H x r‖ ≤ K * ‖x‖ :=
    ⟨‖LinearMap.toContinuousLinearMap (H.flip r)‖, fun x => by
      simpa using (LinearMap.toContinuousLinearMap (H.flip r)).le_opNorm x⟩
  have hcontH : ∀ v : V, Continuous fun z : V => H z v := fun v =>
    Continuous.congr (H.flip v).continuous_of_finiteDimensional
      (fun z => LinearMap.flip_apply _ _ _)
  have hcim : ∀ v : V, Continuous fun z : V => (H v z).im := by
    intro v
    have e : (fun z : V => (H v z).im) = fun z => -(H z v).im := by
      funext z
      rw [hH.1 v z, Complex.conj_im]
    rw [e]
    exact (Complex.continuous_im.comp (hcontH v)).neg
  have he1 : ∀ t : ℝ, ‖cexp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  obtain ⟨c, hc⟩ : ∃ c : Λ → ℂ, ∀ x, c x = α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2
      - (π : ℂ) * H r r / 2 + 2 * π * I * ((H x r).im : ℂ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Λ → V → ℂ, ∀ x z,
      F x z = c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := ⟨_, fun _ _ => rfl⟩
  have hfun : (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) =
      fun z => ∑' x : Λ, F x z := by
    funext z
    rw [heis_kerSum_diag H hH Λ α r z]
    simp only [hF, hc]
  have hre : ∀ x : Λ, (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2
      + 2 * π * I * ((H x r).im : ℂ)).re =
      -π * (H x r).re - π / 2 * (H x x).re - π / 2 * (H r r).re := by
    intro x
    simp [Complex.mul_re]
    ring
  have hcle : ∀ x : Λ, ‖c x‖ ≤ Real.exp (-(π / 2) * (H x x).re + π * K * ‖(x : V)‖) *
      Real.exp (-(π / 2) * (H r r).re) := by
    intro x
    have hα1 : ‖α x‖ = 1 := by
      rcases hα.1 x x.2 with h | h <;> simp [h]
    rw [hc, norm_mul, hα1, one_mul, Complex.norm_exp, hre, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -(H x r).re ≤ K * ‖(x : V)‖ := by
      have := (abs_le.mp (Complex.abs_re_le_norm (H x r))).1
      linarith [hK x]
    have hπ : 0 ≤ π := Real.pi_pos.le
    nlinarith
  have hcsum : Summable fun x : Λ => ‖c x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcle
      ((GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * K)).mul_right _)
  have hFnorm : ∀ x z, ‖F x z‖ = ‖c x‖ := by
    intro x z
    rw [hF, norm_mul, he1, mul_one]
  have hFcont : ∀ x : Λ, Continuous (F x) := by
    intro x
    have e : F x = fun z => c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := funext (hF x)
    rw [e]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hcim _))))
  have hsumcont : Continuous fun z => ∑' x : Λ, F x z :=
    continuous_tsum hFcont hcsum (fun x z => (hFnorm x z).le)
  have hFs : ∀ z, Summable fun x : Λ => ‖F x z‖ := fun z => by
    simp only [hFnorm]
    exact hcsum
  have hbdd : ∀ z, ‖∑' x : Λ, F x z‖ ≤ ∑' x : Λ, ‖c x‖ := fun z => by
    refine (norm_tsum_le_tsum_norm (hFs z)).trans (le_of_eq ?_)
    simp only [hFnorm]
  have hFint : ∀ x : Λ, IntegrableOn (F x) Fd μ := fun x =>
    Measure.integrableOn_of_bounded hFdfin (hFcont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (hFnorm x z).le)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Measure.integrableOn_of_bounded hFdfin hsumcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  · rw [hfun]
    have hnormint : (fun x : Λ => ∫ z in Fd, ‖F x z‖ ∂μ) = fun x => μ.real Fd * ‖c x‖ := by
      funext x
      simp only [hFnorm]
      rw [setIntegral_const, smul_eq_mul]
    rw [← integral_tsum_of_summable_integral_norm hFint
      (by rw [hnormint]; exact hcsum.mul_left _)]
    have hint : ∀ x : Λ, ∫ z in Fd, F x z ∂μ =
        if (x : V) = -r then c x * (μ.real Fd : ℂ) else 0 := by
      intro x
      simp only [hF]
      rw [integral_const_mul]
      split_ifs with hx
      · have h0 : r + (x : V) = 0 := by
          rw [hx]
          abel
        simp only [h0, map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.ofReal_zero,
          mul_zero, Complex.exp_zero]
        rw [setIntegral_const, Complex.real_smul, mul_one]
      · have hne : r + (x : V) ≠ 0 := by
          intro h
          apply hx
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h
        rw [GlobalTheory.T.setIntegral_cexp_im_herm_eq_zero V μ H hH Λ' Fd hFd (r + x) hne ?_, mul_zero]
        intro y hy
        obtain ⟨m1, hm1⟩ := hr y hy
        obtain ⟨m2, hm2⟩ := hα.2.1 x x.2 y (hle hy)
        refine ⟨m1 + m2, ?_⟩
        rw [map_add, LinearMap.add_apply, Complex.add_im, hm1, hm2]
        push_cast
        ring
    simp only [hint]
    by_cases hrΛ : r ∈ Λ
    · rw [if_pos hrΛ, tsum_eq_single ⟨-r, neg_mem hrΛ⟩]
      · have hcoe : ((⟨-r, neg_mem hrΛ⟩ : Λ) : V) = -r := rfl
        have him : (H r r).im = 0 := Complex.conj_eq_iff_im.mp (hH.1 r r).symm
        have hA : cexp (-(π : ℂ) * H (-r) r - (π : ℂ) * H (-r) (-r) / 2 - (π : ℂ) * H r r / 2
            + 2 * π * I * ((H (-r) r).im : ℂ)) = 1 := by
          rw [← Complex.exp_zero]
          congr 1
          simp only [map_neg, LinearMap.neg_apply, neg_neg, Complex.neg_im, him, neg_zero,
            Complex.ofReal_zero, mul_zero, add_zero]
          ring
        rw [hc, hcoe, if_pos rfl, hA, mul_one]
      · intro x hx
        rw [if_neg]
        intro h
        apply hx
        exact Subtype.ext h
    · rw [if_neg hrΛ]
      have hno : ∀ x : Λ, ¬ ((x : V) = -r) := by
        intro x h
        apply hrΛ
        have hm := neg_mem x.2
        rw [h, neg_neg] at hm
        exact hm
      simp [hno]

end GlobalTheory.UnitaryTheta
