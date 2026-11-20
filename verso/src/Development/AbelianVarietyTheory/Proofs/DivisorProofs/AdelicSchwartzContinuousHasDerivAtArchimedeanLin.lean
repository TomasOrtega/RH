import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SchLine

/- English proof (translation)
Unfold `pureA`. Use `Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg.1.continuous.comp (continuous_pi fun i => ?_))` and prove the remaining obligations. Conclude with `(continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))`. Conclude with `continuous_snd.comp (continuous_apply i)`.
-/
theorem continuous_pureA (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : Continuous (pureA F f g) := by
  unfold pureA
  refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg.1.continuous.comp (continuous_pi fun i => ?_))
  · exact (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_snd.comp (continuous_apply i)

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Conclude with `continuous_pureA F f g hg`. Consider the case `zero => exact continuous_const`.

Consider the case `add Φ Ψ _ _ h1 h2 => exact h1.add h2`. Consider the case `smul a Φ _ h => exact h.const_smul a`.
-/
theorem continuous_of_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f g hg
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact h.const_smul a

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply]`. Rewrite using `[add_assoc, ← infAd_add, ← add_smul, add_sub_cancel]`.
-/
theorem line_shift (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t s : ℝ) :
    x + (fun i => infAd F (s • v i)) = (x + fun i => infAd F (t • v i)) + fun i => infAd F ((s - t) • v i) := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, ← infAd_add, ← add_smul, add_sub_cancel]

/- English proof (translation)
Introduce `F _ _ κ _ g hg`. Use `⟨continuous_of_mem F hg, fun v x t => ?_⟩` and prove the remaining obligations. Use `set y : κ → AF F := x + fun i => infAd F (t • v i)`. Establish `h0 : HasDerivAt (fun u : ℝ => g (y + fun i => infAd F (u • v i))) (dD F v g y) (t - t)`. Rewrite using `[sub_self]`.

Conclude with `((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hg).1 y).hasDerivAt`. Establish `h1` using `h0.comp_sub_const t t`. Use `h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show g (x + fun i => infAd F (s • v i)) = g (y + fun i => infAd F ((s - t) • v i))`. Rewrite using `[line_shift F x v t s]`.
-/
theorem schline : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  intro F _ _ κ _ g hg
  refine ⟨continuous_of_mem F hg, fun v x t => ?_⟩
  set y : κ → AF F := x + fun i => infAd F (t • v i)
  have h0 : HasDerivAt (fun u : ℝ => g (y + fun i => infAd F (u • v i))) (dD F v g y) (t - t) := by
    rw [sub_self]
    exact ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hg).1 y).hasDerivAt
  have h1 := h0.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show g (x + fun i => infAd F (s • v i)) = g (y + fun i => infAd F ((s - t) • v i))
  rw [line_shift F x v t s]

end GlobalTheory.ArchDecay.SchLine
