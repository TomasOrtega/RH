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
A detailed English derivation is pending.
-/
private theorem gl_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (x : GL (Fin n) k) :
    Continuous (fun p : GL (Fin n) k × GL (Fin n) k => p.1 * x * p.2) :=
  (continuous_fst.mul continuous_const).mul continuous_snd

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
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
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem iwCoset_ind_hasCompactSupport {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ)
    (hC : IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) :
    HasCompactSupport ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) := by
  have hcomp : IsCompact (iwCoset w ν) := by
    rw [iwCoset_eq_image]
    exact (hC.prod hC).image (gl_cont _)
  exact HasCompactSupport.intro hcomp (fun x hx => Set.indicator_of_notMem hx _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
