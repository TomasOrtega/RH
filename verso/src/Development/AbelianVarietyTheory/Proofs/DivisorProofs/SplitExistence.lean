import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactorStatement

noncomputable section

namespace GlobalTheory.ThKSplit

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

/- English proof (translation)
Take `⟨μ, 𝓕, hμ, h𝓕, h1⟩` from `hdom`. Take `⟨t, m, hm, ht⟩` from `hlevi`. Establish `hsum : ∀ h, fa h + fb h = fa' h + fb' h`. Introduce `h`. Establish `e1` using `h₁.1 μ 𝓕 hμ h𝓕 h1 h`.

Establish `e2` using `h₂.1 μ 𝓕 hμ h𝓕 h1 h`. Simplify using `only [Pi.add_apply] at e1 e2`. Rewrite using `[e1, e2]`. Establish `key : ∀ h, fa h = fa' h`. Introduce `h`.

Assume the negation of the conclusion as `hne`. Establish `hA` using `h₁.2.1 t m hm h`. Establish `hA'` using `h₂.2.1 t m hm h`. Establish `hB` using `h₁.2.2 t m hm h`. Establish `hB'` using `h₂.2.2 t m hm h`.

Establish `s1` using `hsum (m * h)`. Establish `s0` using `hsum h`. Use `set cA' : ℂ := (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) with hcA`. Use `set cB : ℂ := (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) with hcB`. Establish `e : cA' * (fa h - fa' h) = cB * (fa h - fa' h)`.

Take the linear combination `-hA + hA' + s1 - hB + hB' - cB * s0`. Establish `e' : cA' = cB` using `mul_right_cancel₀ (sub_ne_zero.2 hne) e`. Establish `n1 : ‖cA'‖ = (absE F E t : ℝ) ^ ((a' : ℝ) / 2)`. Rewrite using `[hcA, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]`. Establish `n2 : ‖cB‖ = (absE F E t : ℝ) ^ ((a : ℝ) / 2)`.

Rewrite using `[hcB, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]`. Establish `hlt' : (a' : ℝ) / 2 < (a : ℝ) / 2`. Establish `: (a' : ℝ) < a` using `by exact_mod_cast hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.rpow_lt_rpow_of_exponent_lt ht hlt'` as an intermediate fact.

Rewrite `this` using `[← n1, ← n2, e']`. Conclude with `lt_irrefl _ this`. Use `⟨funext key, funext fun h => ?_⟩` and prove the remaining obligations. Use `hsum h` as an intermediate fact. Rewrite `this` using `[key h]`.

Conclude with `add_left_cancel this`.
-/
theorem split2_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} {W : Spc F E (a + a')} {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {X : Chars F E}
    (hlt : a' < a)
    (hdom : ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m ∧ 1 < (absE F E t : ℝ))
    {f fa fb fa' fb' : UA σ W.J → ℂ} (h₁ : Split2 W₁ H' X f fa fb) (h₂ : Split2 W₁ H' X f fa' fb') :
    fa = fa' ∧ fb = fb' := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  obtain ⟨t, m, hm, ht⟩ := hlevi
  have hsum : ∀ h, fa h + fb h = fa' h + fb' h := by
    intro h
    have e1 := h₁.1 μ 𝓕 hμ h𝓕 h1 h
    have e2 := h₂.1 μ 𝓕 hμ h𝓕 h1 h
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
  have key : ∀ h, fa h = fa' h := by
    intro h
    by_contra hne
    have hA := h₁.2.1 t m hm h
    have hA' := h₂.2.1 t m hm h
    have hB := h₁.2.2 t m hm h
    have hB' := h₂.2.2 t m hm h
    have s1 := hsum (m * h)
    have s0 := hsum h
    set cA' : ℂ := (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) with hcA
    set cB : ℂ := (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) with hcB
    have e : cA' * (fa h - fa' h) = cB * (fa h - fa' h) := by
      linear_combination -hA + hA' + s1 - hB + hB' - cB * s0
    have e' : cA' = cB := mul_right_cancel₀ (sub_ne_zero.2 hne) e
    have n1 : ‖cA'‖ = (absE F E t : ℝ) ^ ((a' : ℝ) / 2) := by
      rw [hcA, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have n2 : ‖cB‖ = (absE F E t : ℝ) ^ ((a : ℝ) / 2) := by
      rw [hcB, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have hlt' : (a' : ℝ) / 2 < (a : ℝ) / 2 := by
      have : (a' : ℝ) < a := by exact_mod_cast hlt
      linarith
    have := Real.rpow_lt_rpow_of_exponent_lt ht hlt'
    rw [← n1, ← n2, e'] at this
    exact lt_irrefl _ this
  refine ⟨funext key, funext fun h => ?_⟩
  have := hsum h
  rw [key h] at this
  exact add_left_cancel this

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH`. Establish `hd` using `GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH`. Establish `hl` using `GlobalTheory.T.triple_adapted_plane_local_factor F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH`. Take `⟨h1, h2⟩` from `GlobalTheory.T.triple_adapted_plane_restriction hP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH`. Use `⟨fun Φ hΦ => ?_, fun Φ' hΦ' => ?_⟩` and prove the remaining obligations.

Take `⟨fa, fb, hs⟩` from `h1 Φ hΦ`. Use `⟨(fa, fb), hs, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨e1, e2⟩` from `split2_unique hT.geo.lt hd hl hy hs`. Conclude with `Prod.ext e1 e2`. Take `⟨fa, fb, hs⟩` from `h2 Φ' hΦ'`.

Use `⟨(fa, fb), hs, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨e1, e2⟩` from `split2_unique hT.geo.lt hd hl hy hs`. Conclude with `Prod.ext e1 e2`.
-/
theorem splitEx : KP → SplitEx := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hd := GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hl := GlobalTheory.T.triple_adapted_plane_local_factor F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  obtain ⟨h1, h2⟩ := GlobalTheory.T.triple_adapted_plane_restriction hP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  refine ⟨fun Φ hΦ => ?_, fun Φ' hΦ' => ?_⟩
  · obtain ⟨fa, fb, hs⟩ := h1 Φ hΦ
    refine ⟨(fa, fb), hs, fun y hy => ?_⟩
    obtain ⟨e1, e2⟩ := split2_unique hT.geo.lt hd hl hy hs
    exact Prod.ext e1 e2
  · obtain ⟨fa, fb, hs⟩ := h2 Φ' hΦ'
    refine ⟨(fa, fb), hs, fun y hy => ?_⟩
    obtain ⟨e1, e2⟩ := split2_unique hT.geo.lt hd hl hy hs
    exact Prod.ext e1 e2

end GlobalTheory.ThKSplit
