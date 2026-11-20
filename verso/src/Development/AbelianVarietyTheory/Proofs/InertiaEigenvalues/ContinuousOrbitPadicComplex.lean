import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

/- English proof (translation)
Establish `hS` using `stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x`. Establish `hc : Continuous fun g : GQ l => g₀⁻¹ * g` using `continuous_const.mul continuous_id`. Establish `hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l))`. Simplify using the standard rewrite rules. Use `filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg`.

Establish `hg' : (g₀⁻¹ * g) x = x` using `hg`. Use `congrArg g₀ hg'` as an intermediate fact. Simplify `this` using `[AlgEquiv.mul_apply]`.
-/
theorem eventually_apply_eq {l : ℕ} [Fact l.Prime] (x : Om l) (g₀ : GQ l) :
    ∀ᶠ g : GQ l in nhds g₀, g x = g₀ x := by
  have hS := stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x
  have hc : Continuous fun g : GQ l => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l)) := by
    simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg
  have hg' : (g₀⁻¹ * g) x = x := hg
  have := congrArg g₀ hg'
  simpa [AlgEquiv.mul_apply] using this

/- English proof (translation)
Take `⟨hext, hiso⟩` from `h`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`.

Take `⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2` from `UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)`. Use `filter_upwards [eventually_apply_eq x g₀] with g hg`. Establish `h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x)`. Rewrite using `[map_sub, map_sub, hext g x, hext g₀ x, hg]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[dist_eq_norm, h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsActC.continuous_orbit (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.Cyc
