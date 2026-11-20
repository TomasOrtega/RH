import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteRealPointsCommuteStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Unfold `atTau`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `(GinfC V).one_mem`.
-/
private lemma atTau_mem_GinfC_twisted_operators {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

/- English proof (translation)
Introduce `D V S θ M J χ κ hκ hJ T hT`. Use `⟨(LinearMap.funLeft ℂ ℂ (fun g : GA D V => g * κ)).compMultilinearMap T, ⟨fun v => ?_, fun v => ?_, fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v => rfl⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite θ V κ hκ (T v) (hT.aut v)`. Introduce `r C hC μ 𝓕 hμ h𝓕 g`. Establish `h` using `hT.cusp v r C hC μ 𝓕 hμ h𝓕 (g * κ)`.

Simplify `h` using `only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, Function.comp, mul_assoc]`. Take `⟨hk1, hk2⟩` from `hJ k hk`. Use `show T v (g * k * κ) = χ k * T v (g * κ)`. Establish `h` using `hT.lev v _ hk1 (g * κ)`. Rewrite `h` using `[hk2]`.

Rewrite using `[← h]`. Use `congr 1`. Use `group`. Rewrite using `[LinearMap.compMultilinearMap_apply, hT.equiv τ g hg v w hw]`. Use function extensionality and compare the values at `x`.

Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, rTr]`. Rewrite using `[mul_assoc, mul_assoc, GlobalTheory.T.mul_comm_of_mem_GfC_of_mem_GinfC V κ _ hκ (atTau_mem_GinfC_twisted_operators θ V τ g)]`. Take `⟨ℓ, hℓ, hℓw⟩` from `hT.cont τ v (x * κ)`. Conclude with `⟨ℓ, hℓ, fun w => hℓw w⟩`.
-/
theorem isMultMap_rightTranslate_finite : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  intro D V S θ M J χ κ hκ hJ T hT
  refine ⟨(LinearMap.funLeft ℂ ℂ (fun g : GA D V => g * κ)).compMultilinearMap T,
    ⟨fun v => ?_, fun v => ?_, fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v => rfl⟩
  ·
    exact GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite θ V κ hκ (T v) (hT.aut v)
  ·
    intro r C hC μ 𝓕 hμ h𝓕 g
    have h := hT.cusp v r C hC μ 𝓕 hμ h𝓕 (g * κ)
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, Function.comp, mul_assoc] using h
  ·
    obtain ⟨hk1, hk2⟩ := hJ k hk
    show T v (g * k * κ) = χ k * T v (g * κ)
    have h := hT.lev v _ hk1 (g * κ)
    rw [hk2] at h
    rw [← h]
    congr 1
    group
  ·
    rw [LinearMap.compMultilinearMap_apply, hT.equiv τ g hg v w hw]
    funext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.T.mul_comm_of_mem_GfC_of_mem_GinfC V κ _ hκ (atTau_mem_GinfC_twisted_operators θ V τ g)]
  ·
    obtain ⟨ℓ, hℓ, hℓw⟩ := hT.cont τ v (x * κ)
    exact ⟨ℓ, hℓ, fun w => hℓw w⟩

end GlobalTheory
