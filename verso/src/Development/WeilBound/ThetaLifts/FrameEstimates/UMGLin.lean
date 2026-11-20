import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

/- English proof (translation)
The claim follows from `h.trans <| mul_le_mul (le_abs_self C) (pow_le_pow_right₀ hx hk) (pow_nonneg (zero_le_one.trans hx) k) (abs_nonneg C)`.
-/
theorem umgLin_pow_le {x C : ℝ} {z : ℂ} (hx : 1 ≤ x) {k m : ℕ} (hk : k ≤ m) (h : ‖z‖ ≤ C * x ^ k) :
    ‖z‖ ≤ |C| * x ^ m :=
  h.trans <| mul_le_mul (le_abs_self C) (pow_le_pow_right₀ hx hk) (pow_nonneg (zero_le_one.trans hx) k) (abs_nonneg C)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ _ d W _ f f' hf hf' a b`. Take `⟨k, S, hfS, hS⟩` from `hf`. Take `⟨k', S', hfS', hS'⟩` from `hf'`. Use `⟨max k k', {g | ∃ f₁ ∈ S, ∃ f₁' ∈ S', g = a • f₁ + b • f₁'}, ⟨f, hfS, f', hfS', rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, g', hg', rfl⟩`.

Take `⟨hc, ⟨C, hC⟩, hd⟩` from `hS g hg`. Take `⟨hc', ⟨C', hC'⟩, hd'⟩` from `hS' g' hg'`. Use `⟨(hc.const_smul a).add (hc'.const_smul b), ⟨‖a‖ * |C| + ‖b‖ * |C'|, fun h => ?_⟩, fun γ hγ => ?_⟩` and prove the remaining obligations. Establish `hx : (1 : ℝ) ≤ (ht h : ℝ)` using `by exact_mod_cast one_le_ht h`. Establish `h1` using `umgLin_pow_le hx (le_max_left k k') (hC h)`.

Establish `h2` using `umgLin_pow_le hx (le_max_right k k') (hC' h)`. Establish `h3 : ‖(a • g + b • g') h‖ ≤ ‖a‖ * ‖g h‖ + ‖b‖ * ‖g' h‖`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`.

Establish `h4` using `mul_le_mul_of_nonneg_left h1 (norm_nonneg a)`. Establish `h5` using `mul_le_mul_of_nonneg_left h2 (norm_nonneg b)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨g₂, hg₂, e⟩` from `hd γ hγ`. Take `⟨g₂', hg₂', e'⟩` from `hd' γ hγ`.

Conclude with `⟨a • g₂ + b • g₂', ⟨g₂, hg₂, g₂', hg₂', rfl⟩, fun h => ((e h).const_mul a).add ((e' h).const_mul b)⟩`.
-/
theorem umgLin_of : UMGLin := by
  intro F E _ _ _ _ _ σ _ _ d W _ f f' hf hf' a b
  obtain ⟨k, S, hfS, hS⟩ := hf
  obtain ⟨k', S', hfS', hS'⟩ := hf'
  refine ⟨max k k', {g | ∃ f₁ ∈ S, ∃ f₁' ∈ S', g = a • f₁ + b • f₁'}, ⟨f, hfS, f', hfS', rfl⟩, ?_⟩
  rintro _ ⟨g, hg, g', hg', rfl⟩
  obtain ⟨hc, ⟨C, hC⟩, hd⟩ := hS g hg
  obtain ⟨hc', ⟨C', hC'⟩, hd'⟩ := hS' g' hg'
  refine ⟨(hc.const_smul a).add (hc'.const_smul b), ⟨‖a‖ * |C| + ‖b‖ * |C'|, fun h => ?_⟩, fun γ hγ => ?_⟩
  · have hx : (1 : ℝ) ≤ (ht h : ℝ) := by exact_mod_cast one_le_ht h
    have h1 := umgLin_pow_le hx (le_max_left k k') (hC h)
    have h2 := umgLin_pow_le hx (le_max_right k k') (hC' h)
    have h3 : ‖(a • g + b • g') h‖ ≤ ‖a‖ * ‖g h‖ + ‖b‖ * ‖g' h‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h4 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg b)
    linarith
  · obtain ⟨g₂, hg₂, e⟩ := hd γ hγ
    obtain ⟨g₂', hg₂', e'⟩ := hd' γ hγ
    exact ⟨a • g₂ + b • g₂', ⟨g₂, hg₂, g₂', hg₂', rfl⟩, fun h => ((e h).const_mul a).add ((e' h).const_mul b)⟩

end PositivityTheory.ThKEst

end
