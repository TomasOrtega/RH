import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.UiwMul
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

/- English proof (translation)
The claim follows from `(continuous_fst.mul continuous_const).mul continuous_snd`.
-/
private theorem gl_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (x : GL (Fin n) k) :
    Continuous (fun p : GL (Fin n) k × GL (Fin n) k => p.1 * x * p.2) :=
  (continuous_fst.mul continuous_const).mul continuous_snd

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨(a, b), ⟨ha, hb⟩, rfl⟩`. Introduce and unpack `⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩`.

Conclude with `⟨a, ha, b, hb, rfl⟩`.
-/
private theorem iwCoset_eq_image {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    iwCoset w ν = (fun p : GL (Fin n) (w.adicCompletion K) × GL (Fin n) (w.adicCompletion K) =>
        p.1 * Cartan.diagPow (w.adicCompletion K) n ν * p.2) ''
      ((GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ×ˢ
        (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Rewrite using `[GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]`. Conclude with `mul_mem ha hb`.

Introduce `hg`. Conclude with `⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩`.
-/
private theorem iwCoset_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩

/- English proof (translation)
Rewrite using `[Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, h⟩`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientGroup.out_eq' c, h]`.

Use `QuotientGroup.eq.mpr ?_` and prove the remaining obligations. Establish `: (a * Cartan.diagPow (w.adicCompletion K) n ν * b)⁻¹ * (a * Cartan.diagPow (w.adicCompletion K) n ν) = b⁻¹` using `by group`. Rewrite using `[this]`. Conclude with `inv_mem hb`. Introduce and unpack `⟨k, hk, rfl⟩`.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (GLnLocal.iwahori (w.adicCompletion K) n) (k * Cartan.diagPow (w.adicCompletion K) n ν)`. Conclude with `⟨k, hk, h, h.2, hh⟩`.
-/
private theorem out_mem_iwCoset_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ)
    (c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n) :
    c.out ∈ iwCoset w ν ↔ c ∈ {c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n |
      ∃ k ∈ GLnLocal.iwahori (w.adicCompletion K) n,
        c = QuotientGroup.mk (k * Cartan.diagPow (w.adicCompletion K) n ν)} := by
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.out_eq' c, h]
    refine QuotientGroup.eq.mpr ?_
    have : (a * Cartan.diagPow (w.adicCompletion K) n ν * b)⁻¹ * (a * Cartan.diagPow (w.adicCompletion K) n ν) = b⁻¹ := by
      group
    rw [this]
    exact inv_mem hb
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GLnLocal.iwahori (w.adicCompletion K) n)
      (k * Cartan.diagPow (w.adicCompletion K) n ν)
    exact ⟨k, hk, h, h.2, hh⟩

/- English proof (translation)
Establish `hcomp : IsCompact (iwCoset w ν)`. Rewrite using `[iwCoset_eq_image]`. Conclude with `(hC.prod hC).image (gl_cont _)`. Conclude with `HasCompactSupport.intro hcomp (fun x hx => Set.indicator_of_notMem hx _)`.
-/
private theorem iwCoset_ind_hasCompactSupport {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ)
    (hC : IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) :
    HasCompactSupport ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) := by
  have hcomp : IsCompact (iwCoset w ν) := by
    rw [iwCoset_eq_image]
    exact (hC.prod hC).image (gl_cont _)
  exact HasCompactSupport.intro hcomp (fun x hx => Set.indicator_of_notMem hx _)

/- English proof (translation)
Introduce `k hk x`. Establish `hiff : x * k ∈ iwCoset w ν ↔ x ∈ iwCoset w ν`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, h⟩`. Use `⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), ?_⟩` and prove the remaining obligations.

Rewrite using `[← mul_assoc, ← h]`. Use `group`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨a, ha, b * k, mul_mem hb hk, by group⟩`. Distinguish the cases in `hxm : x ∈ iwCoset w ν`.

Rewrite using `[Set.indicator_of_mem hxm, Set.indicator_of_mem (hiff.2 hxm)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hxm, Set.indicator_of_notMem (fun h => hxm (hiff.1 h))]`.
-/
private theorem iwCoset_ind_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    ∀ k ∈ GLnLocal.iwahori (w.adicCompletion K) n, ∀ x,
      (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) (x * k) =
        (iwCoset w ν).indicator 1 x := by
  intro k hk x
  have hiff : x * k ∈ iwCoset w ν ↔ x ∈ iwCoset w ν := by
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      refine ⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), ?_⟩
      rw [← mul_assoc, ← h]
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by group⟩
  by_cases hxm : x ∈ iwCoset w ν
  · rw [Set.indicator_of_mem hxm, Set.indicator_of_mem (hiff.2 hxm)]
    rfl
  · rw [Set.indicator_of_notMem hxm, Set.indicator_of_notMem (fun h => hxm (hiff.1 h))]

/- English proof (translation)
Rewrite using `[finsum_mem_def]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c.out ∈ iwCoset w ν`. Rewrite using `[Set.indicator_of_mem hc, Set.indicator_of_mem ((out_mem_iwCoset_iff w _ c).1 hc)]`. Simplify using the standard rewrite rules.

Rewrite using `[Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h => hc ((out_mem_iwCoset_iff w _ c).2 h))]`. Simplify using the standard rewrite rules.
-/
private theorem iwCoset_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (ν : Fin n → ℤ) :
    (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n,
        (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) c.out • rhoL μ w c.out) =
      ∑ᶠ c ∈ {c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n |
          ∃ k ∈ GLnLocal.iwahori (w.adicCompletion K) n,
            c = QuotientGroup.mk (k * Cartan.diagPow (w.adicCompletion K) n ν)}, rhoL μ w c.out := by
  rw [finsum_mem_def]
  refine finsum_congr fun c => ?_
  by_cases hc : c.out ∈ iwCoset w ν
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((out_mem_iwCoset_iff w _ c).1 hc)]
    simp
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun h => hc ((out_mem_iwCoset_iff w _ c).2 h))]
    simp

/- English proof (translation)
Rewrite using `[iwCoset_sum, Uiw, Hop, ContinuousLinearMap.comp_assoc]`. Use `congr 1`. Use `ext1 u`. Simplify using `only [ContinuousLinearMap.comp_apply, prj]`. Conclude with `(Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ (hfix u))).symm`.
-/
private theorem uiw_comp_of_fix {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (ν : Fin n → ℤ) (T : LL μ →L[ℂ] LL μ)
    (hfix : ∀ u, T u ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion K) n)) :
    (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.iwahori (w.adicCompletion K) n,
        (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) c.out • rhoL μ w c.out) ∘L T =
      Uiw μ w ν ∘L T := by
  rw [iwCoset_sum, Uiw, Hop, ContinuousLinearMap.comp_assoc]
  congr 1
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, prj]
  exact (Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ (hfix u))).symm

/- English proof (translation)
Introduce `K _ _ n hn μ _ m _ w ν hν j r hr e₀ e₁ h₀ h₁`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Establish `hz : (fun i => ((0 : ℕ) : ℤ) * ν i) = (0 : Fin n → ℤ)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `he : e₁ = e₀`. Use extensionality with `x`. Rewrite using `[h₀, h₁, hz]`. Rewrite using `[he, pow_zero]`. Both sides reduce to the same expression.

Take `⟨-, hpow, hO, hC, -⟩` from `UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν`. Establish `hx : (fun i => (j : ℤ) * ν i) = j • ν`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite `h₁` using `[hx]`.

Take `⟨hfix, hOf⟩` from `UpperTheory.ConvolutionTheory.GM.stepFin K n hn μ m w (GLnLocal.iwahori (w.adicCompletion K) n) hO ((iwCoset w (j • ν)).indicator 1) (iwCoset_ind_hasCompactSupport w _ hC) (iwCoset_ind_mul w _) r hr e₀ e₁ (fun x => by rw [h₀, iwCoset_zero]) h₁`. Rewrite using `[hOf, hpow j hj]`. Conclude with `uiw_comp_of_fix μ w _ _ hfix`.
-/
theorem UpperTheory.ConvolutionTheory.GM.uiwFin :
    UiwFin := by
  intro K _ _ n hn μ _ m _ w ν hν j r hr e₀ e₁ h₀ h₁
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hz : (fun i => ((0 : ℕ) : ℤ) * ν i) = (0 : Fin n → ℤ) := by
      funext i
      simp
    have he : e₁ = e₀ := by
      ext x
      rw [h₀, h₁, hz]
    rw [he, pow_zero]
    rfl
  obtain ⟨-, hpow, hO, hC, -⟩ := UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν
  have hx : (fun i => (j : ℤ) * ν i) = j • ν := by
    funext i
    simp
  rw [hx] at h₁
  obtain ⟨hfix, hOf⟩ := UpperTheory.ConvolutionTheory.GM.stepFin K n hn μ m w (GLnLocal.iwahori (w.adicCompletion K) n) hO
    ((iwCoset w (j • ν)).indicator 1) (iwCoset_ind_hasCompactSupport w _ hC) (iwCoset_ind_mul w _) r hr e₀ e₁
    (fun x => by rw [h₀, iwCoset_zero]) h₁
  rw [hOf, hpow j hj]
  exact uiw_comp_of_fix μ w _ _ hfix
