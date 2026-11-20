import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.WhittakerInducedSpan

/- English proof (translation)
Introduce `hFe F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂`. Establish `gen : ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, W2 ψ μ₁ μ₂ φ ∈ V2 ψ μ₁ μ₂` using `fun φ hφ => Submodule.subset_span ⟨φ, hφ, rfl⟩`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, hne⟩` from `GlobalTheory.CompanionTheory.WhNe.sNe F ψ hψ μ₁ μ₂ h₁ h₂`. Conclude with `⟨_, gen φ hφ, hne⟩`.

Introduce `W hW h`. Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem W hW`. Take `⟨φ, hφ, rfl⟩` from `hW`. Take `⟨hrt, heq⟩` from `GlobalTheory.CompanionTheory.WhittakerTrans.sTrans F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ h`.

Establish `: (fun g => W2 ψ μ₁ μ₂ φ (g * h)) = (((μ₂ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det h) (1 / 2)) • W2 ψ μ₁ μ₂ (SchwartzSpaceL2.rt φ h)`. Use function extensionality and compare the values at `g`. Simplify using `using heq g`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (gen _ hrt)`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add W₁ W₂ _ _ i₁ i₂ => exact Submodule.add_mem _ i₁ i₂`. Consider the case `smul c W _ i => exact Submodule.smul_mem _ c i`. Introduce `W hW x g`. Proceed by induction on `hW using Submodule.span_induction with`.

Consider the case `mem W hW`. Take `⟨φ, hφ, rfl⟩` from `hW`. Conclude with `GlobalTheory.CompanionTheory.WhittakerPsi.sPsi F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ x g`. Consider the case `zero => simp`. Consider the case `add W₁ W₂ _ _ i₁ i₂ => simp only [Pi.add_apply, i₁, i₂, mul_add]`.

Consider the case `smul c W _ i => simp only [Pi.smul_apply, smul_eq_mul, i]`. Expand and normalize the polynomial expressions, which then agree. Introduce `W hW a g`. Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem W hW`.

Take `⟨φ, hφ, rfl⟩` from `hW`. Conclude with `GlobalTheory.CompanionTheory.WhittakerCentral.sCen F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ a g`. Consider the case `zero => simp`. Consider the case `add W₁ W₂ _ _ i₁ i₂ => simp only [Pi.add_apply, i₁, i₂, mul_add]`. Consider the case `smul c W _ i => simp only [Pi.smul_apply, smul_eq_mul, i]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `W hW`. Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem W hW`. Take `⟨φ, hφ, rfl⟩` from `hW`.

Conclude with `GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ`. Consider the case `zero => exact ⟨⊤, fun _ _ _ => rfl⟩`. Consider the case `add W₁ W₂ _ _ i₁ i₂`. Take `⟨U₁, hU₁⟩` from `i₁`. Take `⟨U₂, hU₂⟩` from `i₂`.

Use `⟨U₁ ⊓ U₂, fun g u hu => ?_⟩` and prove the remaining obligations. Establish `hu' : u ∈ U₁ ∧ u ∈ U₂` using `by simpa using hu`. Simplify using `only [Pi.add_apply, hU₁ g u hu'.1, hU₂ g u hu'.2]`. Consider the case `smul c W _ i`. Take `⟨U, hU⟩` from `i`.

Conclude with `⟨U, fun g u hu => by simp only [Pi.smul_apply, hU g u hu]⟩`. Introduce `W hW ε hε`. Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem W hW`. Take `⟨φ, hφ, rfl⟩` from `hW`.

Conclude with `GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ ε hε`. Consider the case `zero => exact ⟨0, 0, fun a k _ => by simp⟩`. Consider the case `add W₁ W₂ _ _ i₁ i₂`. Take `⟨C₁, B₁, hb₁⟩` from `i₁`. Take `⟨C₂, B₂, hb₂⟩` from `i₂`.

Use `⟨C₁ + C₂, max B₁ B₂, fun a k hk => ⟨?_, fun hne => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `h0 : W₁ (dg2 a 1 * k) = 0`. Establish `: W₂ (dg2 a 1 * k) ≠ 0` using `fun h => hne (by simp [h0, h])`.

Conclude with `le_max_of_le_right ((hb₂ a k hk).2 this)`. Conclude with `le_max_of_le_left ((hb₁ a k hk).2 h0)`. Consider the case `smul c W _ i`. Take `⟨C, B, hb⟩` from `i`. Use `⟨‖c‖ * C, B, fun a k hk => ⟨?_, fun hne => ?_⟩⟩` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, norm_smul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hb a k hk).1 (norm_nonneg c)`. Conclude with `(hb a k hk).2 fun h => hne (by simp [h])`. Establish `key : ∀ W ∈ V2 ψ μ₁ μ₂, ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 → Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) (multHaar F) ∧ Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (mult …`. Introduce `W hW c hc s hs0 hs1`.

Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem W hW`. Take `⟨φ, hφ, rfl⟩` from `hW`. Conclude with `hFe F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1`. Consider the case `zero => simp [integrable_zero]`.

Consider the case `add W₁ W₂ _ _ i₁ i₂`. Take `⟨a₁, b₁, e₁⟩` from `i₁`. Take `⟨a₂, b₂, e₂⟩` from `i₂`. Establish `ha : (fun a : Fˣ => (W₁ + W₂) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) = (fun a : Fˣ => W₁ (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) + (fun a : Fˣ => W₂ (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 …`. Use function extensionality and compare the values at `a`.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : (fun a : Fˣ => (W₁ + W₂) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) = (fun a : Fˣ => W₁ (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) + (fun a : Fˣ => W₂ (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ha, hb]`. Use `⟨a₁.add a₂, b₁.add b₂, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add' a₁ a₂, integral_add' b₁ b₂, e₁, e₂, mul_add]`. Consider the case `smul k W _ i`.

Take `⟨a₁, b₁, e₁⟩` from `i`. Establish `ha : (fun a : Fˣ => (k • W) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) = fun a : Fˣ => k * (W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s))`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hb : (fun a : Fˣ => (k • W) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) = fun a : Fˣ => k * (W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ha, hb]`.

Use `⟨a₁.const_mul k, b₁.const_mul k, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, integral_const_mul, e₁]`. Expand and normalize the polynomial expressions, which then agree. Introduce `W hW c hc s hs0 hs1`. Conclude with `(key W hW c hc s hs0 hs1).2.2`.
-/
theorem whittaker_induced_space : Ad3.SchwartzSpaceL2.FeGen → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ (V2 ψ μ₁ μ₂) := by
  intro hFe F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂
  have gen : ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, W2 ψ μ₁ μ₂ φ ∈ V2 ψ μ₁ μ₂ :=
    fun φ hφ => Submodule.subset_span ⟨φ, hφ, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨φ, hφ, hne⟩ := GlobalTheory.CompanionTheory.WhNe.sNe F ψ hψ μ₁ μ₂ h₁ h₂
    exact ⟨_, gen φ hφ, hne⟩
  · intro W hW h
    induction hW using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨φ, hφ, rfl⟩ := hW
      obtain ⟨hrt, heq⟩ := GlobalTheory.CompanionTheory.WhittakerTrans.sTrans F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ h
      have : (fun g => W2 ψ μ₁ μ₂ φ (g * h)) =
          (((μ₂ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det h) (1 / 2)) •
            W2 ψ μ₁ μ₂ (SchwartzSpaceL2.rt φ h) := by
        funext g
        simpa using heq g
      rw [this]
      exact Submodule.smul_mem _ _ (gen _ hrt)
    | zero => exact Submodule.zero_mem _
    | add W₁ W₂ _ _ i₁ i₂ => exact Submodule.add_mem _ i₁ i₂
    | smul c W _ i => exact Submodule.smul_mem _ c i
  · intro W hW x g
    induction hW using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨φ, hφ, rfl⟩ := hW
      exact GlobalTheory.CompanionTheory.WhittakerPsi.sPsi F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ x g
    | zero => simp
    | add W₁ W₂ _ _ i₁ i₂ => simp only [Pi.add_apply, i₁, i₂, mul_add]
    | smul c W _ i => simp only [Pi.smul_apply, smul_eq_mul, i]; ring
  · intro W hW a g
    induction hW using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨φ, hφ, rfl⟩ := hW
      exact GlobalTheory.CompanionTheory.WhittakerCentral.sCen F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ a g
    | zero => simp
    | add W₁ W₂ _ _ i₁ i₂ => simp only [Pi.add_apply, i₁, i₂, mul_add]
    | smul c W _ i => simp only [Pi.smul_apply, smul_eq_mul, i]; ring
  · intro W hW
    induction hW using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨φ, hφ, rfl⟩ := hW
      exact GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ
    | zero => exact ⟨⊤, fun _ _ _ => rfl⟩
    | add W₁ W₂ _ _ i₁ i₂ =>
      obtain ⟨U₁, hU₁⟩ := i₁
      obtain ⟨U₂, hU₂⟩ := i₂
      refine ⟨U₁ ⊓ U₂, fun g u hu => ?_⟩
      have hu' : u ∈ U₁ ∧ u ∈ U₂ := by simpa using hu
      simp only [Pi.add_apply, hU₁ g u hu'.1, hU₂ g u hu'.2]
    | smul c W _ i =>
      obtain ⟨U, hU⟩ := i
      exact ⟨U, fun g u hu => by simp only [Pi.smul_apply, hU g u hu]⟩
  · intro W hW ε hε
    induction hW using Submodule.span_induction with
    | mem W hW =>
      obtain ⟨φ, hφ, rfl⟩ := hW
      exact GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ ε hε
    | zero => exact ⟨0, 0, fun a k _ => by simp⟩
    | add W₁ W₂ _ _ i₁ i₂ =>
      obtain ⟨C₁, B₁, hb₁⟩ := i₁
      obtain ⟨C₂, B₂, hb₂⟩ := i₂
      refine ⟨C₁ + C₂, max B₁ B₂, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · simp only [Pi.add_apply]
        calc _ ≤ ‖W₁ (dg2 a 1 * k)‖ + ‖W₂ (dg2 a 1 * k)‖ := norm_add_le _ _
          _ ≤ _ := by rw [add_mul]; exact add_le_add (hb₁ a k hk).1 (hb₂ a k hk).1
      · by_cases h0 : W₁ (dg2 a 1 * k) = 0
        · have : W₂ (dg2 a 1 * k) ≠ 0 := fun h => hne (by simp [h0, h])
          exact le_max_of_le_right ((hb₂ a k hk).2 this)
        · exact le_max_of_le_left ((hb₁ a k hk).2 h0)
    | smul c W _ i =>
      obtain ⟨C, B, hb⟩ := i
      refine ⟨‖c‖ * C, B, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · simp only [Pi.smul_apply, norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hb a k hk).1 (norm_nonneg c)
      · exact (hb a k hk).2 fun h => hne (by simp [h])
  · have key : ∀ W ∈ V2 ψ μ₁ μ₂, ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 →
        Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s)) (multHaar F) ∧
        Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
        ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
          gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
            ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F := by
      intro W hW c hc s hs0 hs1
      induction hW using Submodule.span_induction with
      | mem W hW =>
        obtain ⟨φ, hφ, rfl⟩ := hW
        exact hFe F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1
      | zero => simp [integrable_zero]
      | add W₁ W₂ _ _ i₁ i₂ =>
        obtain ⟨a₁, b₁, e₁⟩ := i₁
        obtain ⟨a₂, b₂, e₂⟩ := i₂
        have ha : (fun a : Fˣ => (W₁ + W₂) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
              mp a (1 / 2 - s)) =
            (fun a : Fˣ => W₁ (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) +
            (fun a : Fˣ => W₂ (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) := by
          funext a
          simp only [Pi.add_apply]
          ring
        have hb : (fun a : Fˣ => (W₁ + W₂) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) =
            (fun a : Fˣ => W₁ (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) +
            (fun a : Fˣ => W₂ (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) := by
          funext a
          simp only [Pi.add_apply]
          ring
        rw [ha, hb]
        refine ⟨a₁.add a₂, b₁.add b₂, ?_⟩
        rw [integral_add' a₁ a₂, integral_add' b₁ b₂, e₁, e₂, mul_add]
      | smul k W _ i =>
        obtain ⟨a₁, b₁, e₁⟩ := i
        have ha : (fun a : Fˣ => (k • W) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
              mp a (1 / 2 - s)) =
            fun a : Fˣ => k * (W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        have hb : (fun a : Fˣ => (k • W) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) =
            fun a : Fˣ => k * (W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [ha, hb]
        refine ⟨a₁.const_mul k, b₁.const_mul k, ?_⟩
        rw [integral_const_mul, integral_const_mul, e₁]
        ring
    intro W hW c hc s hs0 hs1
    exact (key W hW c hc s hs0 hs1).2.2

end GlobalTheory.CompanionTheory.WhittakerInducedSpan
