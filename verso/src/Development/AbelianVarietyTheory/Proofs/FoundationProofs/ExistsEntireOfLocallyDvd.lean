import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

namespace GlobalTheory.EvenTheta

/- English proof (translation)
Use `choose g hg hF using h`. Use `⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩` and prove the remaining obligations. Use `(hg w).differentiableAt.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2`. Use `tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_` and prove the remaining obligations.

Establish `h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0` using `mem_closure_iff_frequently.1 (hS z)`. Use `(h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_` and prove the remaining obligations. Conclude with `mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)`.
-/
theorem exists_entire_of_locally_dvd {F S : ℂ → ℂ} (hS : Dense {z | S z ≠ 0})
    (h : ∀ w, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ ∀ᶠ z in 𝓝 w, F z = S z * g z) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = S z * G z := by
  choose g hg hF using h
  refine ⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩
  refine (hg w).differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2
  refine tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_
  have h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0 := mem_closure_iff_frequently.1 (hS z)
  refine (h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_
  exact mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)

/- English proof (translation)
Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ h`. Rewrite using `[GlobalTheory.OddTheta.sgStar_eq L Λ hL]`. Use `⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩` and prove the remaining obligations. Unfold `GlobalTheory.latticeForm`. Use `fun_prop`.
-/
theorem IsLat.exists_sg_add {Λ : AddSubgroup ℂ} (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) :
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ z, sgStar Λ (z + ω) = c z * sgStar Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.sgStar_eq L Λ hL]
  refine ⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩
  unfold GlobalTheory.latticeForm
  fun_prop

/- English proof (translation)
Introduce `Λ hΛ k F hF he h0 hlaw`. Establish `hσ` using `hΛ.differentiable`. Establish `hσc` using `hσ.continuous`. Establish `hFc` using `hF.continuous`. Establish `hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0` using `fun z hz => (hΛ.sg_eq_zero z).not.2 hz`.

Take `⟨h, hh, eh⟩` from `GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he`. Establish `hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0` using `(differentiableOn_univ.1 ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0`. Establish `hu0 : dslope (sgStar Λ) 0 0 ≠ 0`. Rewrite using `[dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]`. Conclude with `one_ne_zero`.

Establish `eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z` using `fun z => by`. Use `sub_smul_dslope (sgStar Λ) 0 z` as an intermediate fact. Rewrite `this` using `[(hΛ.sg_eq_zero 0).2 Λ.zero_mem]`. Simplify using `using this.symm`. Take `⟨G, hG, eG⟩` from `exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2) (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by`.

Distinguish the cases in `hw : w ∈ Λ`. Take `⟨c, hc, ec⟩` from `hΛ.exists_sg_add hw`. Establish `hcc` using `hc.continuous`. Establish `eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z` using `fun z => by`. Use `congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w)) (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z` and prove the remaining obligations.

Use `mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hlaw w hw, ec]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : AnalyticAt ℂ (fun y : ℂ => y - w) w` using `by fun_prop`.

Establish `ha : AnalyticAt ℂ (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0` using `(((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)`. Use `⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩` and prove the remaining obligations. Use `filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne (y := 0) (by simpa using hu0)] with y hy`. Take `⟨z, rfl⟩ : ∃ z, y = z + w` from `⟨y - w, by ring⟩`. Simplify using `only [Function.comp, add_sub_cancel_right] at hy ⊢`.

Rewrite using `[eF, ec, eh, h0, eu z]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2) (pow_ne_zero 2 (hne w hw)), ?_⟩ filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Establish `hGc` using `hG.continuous`. Use `⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩` and prove the remaining obligations. Use `congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc fun z hz => ?_) z` and prove the remaining obligations. Use `mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_` and prove the remaining obligations. Establish `h1` using `eG (-z)`.

Rewrite `h1` using `[he, hΛ.sg_neg, neg_sq]`. Conclude with `h1.symm.trans (eG z)`. Use `congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k)) (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop) fun z hz => ?_) z` and prove the remaining obligations. Establish `hz' : z + ω ∉ Λ` using `fun h' => hz (by simpa using Λ.sub_mem h' hω)`. Use `mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_` and prove the remaining obligations.

Establish `h1` using `hlaw ω hω z`. Rewrite `h1` using `[eG z, eG (z + ω)]`. Use `beta_reduce at h1 ⊢`. Take the linear combination `h1`.
-/
theorem exists_eq_sg_sq_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 0 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * (k + 1)) = F z * sgStar Λ (z + ω) ^ (2 * (k + 1))) → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (-z) = G z) ∧ (∀ z, F z = sgStar Λ z ^ 2 * G z) ∧ ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ (2 * k) = G z * sgStar Λ (z + ω) ^ (2 * k) := by
  intro Λ hΛ k F hF he h0 hlaw
  have hσ := hΛ.differentiable
  have hσc := hσ.continuous
  have hFc := hF.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (hΛ.sg_eq_zero z).not.2 hz
  obtain ⟨h, hh, eh⟩ := GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he
  have hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0 :=
    (differentiableOn_univ.1
      ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0
  have hu0 : dslope (sgStar Λ) 0 0 ≠ 0 := by
    rw [dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]
    exact one_ne_zero
  have eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(hΛ.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  obtain ⟨G, hG, eG⟩ := exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2)
    (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by
      by_cases hw : w ∈ Λ
      · obtain ⟨c, hc, ec⟩ := hΛ.exists_sg_add hw
        have hcc := hc.continuous
        have eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z := fun z => by
          refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w))
            (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z
          refine mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_
          beta_reduce
          rw [hlaw w hw, ec]
          ring
        have hs : AnalyticAt ℂ (fun y : ℂ => y - w) w := by fun_prop
        have ha : AnalyticAt ℂ
            (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0 :=
          (((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)
        refine ⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩
        filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne
          (y := 0) (by simpa using hu0)] with y hy
        obtain ⟨z, rfl⟩ : ∃ z, y = z + w := ⟨y - w, by ring⟩
        simp only [Function.comp, add_sub_cancel_right] at hy ⊢
        rw [eF, ec, eh, h0, eu z]
        field_simp
        ring
      · refine ⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2)
          (pow_ne_zero 2 (hne w hw)), ?_⟩
        filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy
        field_simp
  have hGc := hG.continuous
  refine ⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩
  · refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [he, hΛ.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  · refine congrFun (Continuous.ext_on hΛ.dense_compl
      (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k))
      (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop)
      fun z hz => ?_) z
    have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using Λ.sub_mem h' hω)
    refine mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_
    have h1 := hlaw ω hω z
    rw [eG z, eG (z + ω)] at h1
    beta_reduce at h1 ⊢
    linear_combination h1

end GlobalTheory.EvenTheta
