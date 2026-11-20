import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.GlobalFields.TateThesis.TateMain
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EpConvB

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors
open GroundTheory.Global GroundTheory.Automorphic

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) : ℝ :=
  if y.2 ∈ idealFiniteAdeles L then ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ else 0

/- English proof (translation)
Unfold `adeleWeight`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
theorem adeleWeight_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    0 ≤ adeleWeight L A y := by
  unfold adeleWeight
  split_ifs <;> positivity

/- English proof (translation)
Unfold `adeleWeight`. Use `split_ifs`. Conclude with `inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (homeomorphMixedSpace K y.1)]))`. Conclude with `zero_le_one`.
-/
theorem adeleWeight_le_one (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ 1 := by
  unfold adeleWeight
  split_ifs
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (homeomorphMixedSpace K y.1)]))
  · exact zero_le_one

/- English proof (translation)
Unfold `adeleWeight`. Distinguish the cases in `h1 : y.2 ∈ idealFiniteAdeles L`. Establish `h2 : y.2 ∈ idealFiniteAdeles L'` using `idealFiniteAdeles_subset h h1`. Simplify using `only [if_pos h1, if_pos h2, le_refl]`. Rewrite using `[if_neg h1] split_ifs`.

Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
theorem adeleWeight_mono {L L' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (L : FractionalIdeal (𝓞 K)⁰ K) ≤ L') (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ adeleWeight L' A y := by
  unfold adeleWeight
  by_cases h1 : y.2 ∈ idealFiniteAdeles L
  · have h2 : y.2 ∈ idealFiniteAdeles L' := idealFiniteAdeles_subset h h1
    simp only [if_pos h1, if_pos h2, le_refl]
  · rw [if_neg h1]
    split_ifs
    · positivity
    · exact le_rfl

/- English proof (translation)
Establish `h0 : (0 : 𝔸[K]).2 ∈ idealFiniteAdeles L` using `zero_mem _`. Establish `h1 : homeomorphMixedSpace K (0 : 𝔸[K]).1 = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)`. Unfold `adeleWeight`. Rewrite using `[if_pos h0, h1]`. Simplify using the standard rewrite rules.
-/
@[simp] theorem adeleWeight_zero (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    adeleWeight L A (0 : 𝔸[K]) = 1 := by
  have h0 : (0 : 𝔸[K]).2 ∈ idealFiniteAdeles L := zero_mem _
  have h1 : homeomorphMixedSpace K (0 : 𝔸[K]).1 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  unfold adeleWeight
  rw [if_pos h0, h1]
  simp

/- English proof (translation)
Establish `hc : IsClopen ((idealFiniteAdeles L : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K])` using `⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles L), isOpen_idealFiniteAdeles L⟩`. Establish `hc' : IsClopen {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L}` using `hc.preimage continuous_snd`. Establish `hf : Continuous fun y : 𝔸[K] ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹`. Use `Continuous.inv₀ (by fun_prop) fun y ↦ ?_` and prove the remaining obligations. Use `norm_nonneg (homeomorphMixedSpace K y.1)` as an intermediate fact.

Check the signs of the components of the expression. Establish `: adeleWeight (K` using `K) L A = Set.indicator {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L} (fun y ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹) := by`. Use function extensionality and compare the values at `y`. Simplify using `only [adeleWeight, Set.indicator_apply, Set.mem_setOf_eq]`. Rewrite using `[this]`.

Conclude with `hf.indicator (by rw [hc'.frontier_eq]; simp)`.
-/
theorem continuous_adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    Continuous (adeleWeight (K := K) L A) := by
  have hc : IsClopen ((idealFiniteAdeles L : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles L), isOpen_idealFiniteAdeles L⟩
  have hc' : IsClopen {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L} := hc.preimage continuous_snd
  have hf : Continuous fun y : 𝔸[K] ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun y ↦ ?_
    have := norm_nonneg (homeomorphMixedSpace K y.1)
    positivity
  have : adeleWeight (K := K) L A = Set.indicator {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L}
      (fun y ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹) := by
    funext y
    simp only [adeleWeight, Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact hf.indicator (by rw [hc'.frontier_eq]; simp)
end

end GlobalTheory.CompanionTheory.EpConvB
