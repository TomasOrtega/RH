import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

/- English proof (translation)
Introduce `hL n _ _ μ _ E κ f hκ hf hleft`. Take `⟨-, -, -, -, hcG, -, -⟩` from `hL n`. Take `⟨hkc, R, hR⟩` from `hκ`. Use `haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V`. Establish `hval : ∀ y : G n, y.val ∈ GLs n` using `fun y => by`.

Establish `: IsUnit y.val.det` using `(Matrix.isUnit_iff_isUnit_det _).1 y.isUnit`. Conclude with `this.ne_zero`. Establish `hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n` using `fun a ha b hb => by`. Express the relevant statement in the definitionally equal form `(a * b).det ≠ 0`. Rewrite using `[Matrix.det_mul]`.

Conclude with `mul_ne_zero ha hb`. Use `⟨?_, fun x _ k₂ => ?_⟩` and prove the remaining obligations. Establish `hcv : Continuous (fun y : G n => y.val)` using `Units.continuous_val`. Establish `h1 : ContinuousOn (fun p : Mat n × G n => κ p.2.val) (GLs n ×ˢ Set.univ)` using `hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)`. Establish `h2 : ContinuousOn (fun p : Mat n × G n => f (p.1 * p.2.val)) (GLs n ×ˢ Set.univ)` using `hf.comp (continuous_fst.mul (hcv.comp continuous_snd)).continuousOn (fun p hp => hmul _ hp.1 _ (hval _))`.

Establish `h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => κ y.val (f (x * y.val))) (GLs n ×ˢ Set.univ)` using `h1.clm_apply h2`. Conclude with `continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by`. Establish `: R < lg y.val` using `not_le.1 hy`. Simplify using `[hR _ (hval y) this])`. Establish `hk : k₂.1 * (k₂⁻¹).1 = 1` using `congrArg Subtype.val (mul_inv_cancel k₂)`.

Establish `hk' : (k₂⁻¹).1 * k₂.1 = 1` using `congrArg Subtype.val (inv_mul_cancel k₂)`. Set `g : G n` to `⟨(k₂⁻¹).1, k₂.1, hk', hk⟩`. Express the relevant statement in the definitionally equal form `∫ y : G n, κ y.val (f (x * k₂.1 * y.val)) ∂μ = E.ρ k₂⁻¹ (∫ y : G n, κ y.val (f (x * y.val)) ∂μ)`. Rewrite using `[← integral_mul_left_eq_self (fun y : G n => κ y.val (f (x * k₂.1 * y.val))) g]`. Establish `hpt : ∀ y : G n, κ (g * y).val (f (x * k₂.1 * (g * y).val)) = E.ρ k₂⁻¹ (κ y.val (f (x * y.val)))` using `fun y => by`.

Establish `e1 : (g * y).val = (k₂⁻¹).1 * y.val` using `rfl`. Establish `e2 : x * k₂.1 * ((k₂⁻¹).1 * y.val) = x * y.val`. Rewrite using `[mul_assoc, ← mul_assoc k₂.1, hk, one_mul]`. Rewrite using `[e1, e2, hleft _ (hval y) k₂⁻¹]`. Both sides reduce to the same expression.

Repeatedly rewrite using `[hpt]`. Conclude with `(E.ρ k₂⁻¹).integral_comp_comm' (AddMonoidHomClass.isometry_of_norm (E.ρ k₂⁻¹) (E.iso _)).antilipschitz _`.
-/
theorem act_kReg_section : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg κ →
    ContinuousOn f (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, κ (k₁.1 * y) = E.ρ k₁ * κ y) →
    ContinuousOn (act μ E κ f) (GLs n) ∧
      ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, act μ E κ f (x * k₂.1) = E.ρ k₂⁻¹ (act μ E κ f x) := by
  intro hL n _ _ μ _ E κ f hκ hf hleft
  obtain ⟨-, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hκ
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, fun x _ k₂ => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have h1 : ContinuousOn (fun p : Mat n × G n => κ p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => f (p.1 * p.2.val)) (GLs n ×ˢ Set.univ) :=
      hf.comp (continuous_fst.mul (hcv.comp continuous_snd)).continuousOn
        (fun p hp => hmul _ hp.1 _ (hval _))
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => κ y.val (f (x * y.val)))
        (GLs n ×ˢ Set.univ) := h1.clm_apply h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hk : k₂.1 * (k₂⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel k₂)
    have hk' : (k₂⁻¹).1 * k₂.1 = 1 := congrArg Subtype.val (inv_mul_cancel k₂)
    let g : G n := ⟨(k₂⁻¹).1, k₂.1, hk', hk⟩
    change ∫ y : G n, κ y.val (f (x * k₂.1 * y.val)) ∂μ = E.ρ k₂⁻¹ (∫ y : G n, κ y.val (f (x * y.val)) ∂μ)
    rw [← integral_mul_left_eq_self (fun y : G n => κ y.val (f (x * k₂.1 * y.val))) g]
    have hpt : ∀ y : G n, κ (g * y).val (f (x * k₂.1 * (g * y).val)) =
        E.ρ k₂⁻¹ (κ y.val (f (x * y.val))) := fun y => by
      have e1 : (g * y).val = (k₂⁻¹).1 * y.val := rfl
      have e2 : x * k₂.1 * ((k₂⁻¹).1 * y.val) = x * y.val := by
        rw [mul_assoc, ← mul_assoc k₂.1, hk, one_mul]
      rw [e1, e2, hleft _ (hval y) k₂⁻¹]
      rfl
    simp_rw [hpt]
    exact (E.ρ k₂⁻¹).integral_comp_comm'
      (AddMonoidHomClass.isometry_of_norm (E.ρ k₂⁻¹) (E.iso _)).antilipschitz _

end GlobalTheory.CompanionTheory.WaveMult
