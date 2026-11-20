import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock

/- English proof (translation)
Introduce `E _ _ _ a F hf hK X hX φ hφ`. Take `⟨c, -, h0, -, hc, hu⟩` from `GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X`. Set `W' : Submodule ℂ (GA E a → ℂ)` to `F.map (Sm E a).subtype`. Establish `hfin : FiniteDimensional ℂ W'`. Use `hf` as an intermediate fact.

Conclude with `inferInstance`. Establish `hcl : IsClosed (W' : Set (GA E a → ℂ))` using `W'.closed_of_finiteDimensional`. Set `G : ℝ → GA E a → ℂ` to `fun t g => φ.1 (g * infGL E a (c t))`. Establish `hG : ∀ t, G t ∈ W'` using `fun t => ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by`. Establish `: Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t` using `Units.ext rfl`.

Express the relevant statement in the definitionally equal form `φ.1 (g * infGL E a (Unitary.toUnits _)) = _`. Rewrite using `[this]⟩`. Establish `hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1))` using `tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)`. Establish `hm : lieD X φ.1 ∈ W'` using `hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t => W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))`. Take `⟨w, hw, e⟩` from `hm`.

Rewrite using `[show lie E a X φ = w from Subtype.ext e.symm]` and apply the resulting hypothesis.
-/
theorem lie_skew_mem_of_cpt_stable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) →
    ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  intro E _ _ _ a F hf hK X hX φ hφ
  obtain ⟨c, -, h0, -, hc, hu⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  let W' : Submodule ℂ (GA E a → ℂ) := F.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ W' := by
    have := hf
    exact inferInstance
  have hcl : IsClosed (W' : Set (GA E a → ℂ)) := W'.closed_of_finiteDimensional
  let G : ℝ → GA E a → ℂ := fun t g => φ.1 (g * infGL E a (c t))
  have hG : ∀ t, G t ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t := Units.ext rfl
      change φ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)
  have hm : lieD X φ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E a X φ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.Dblock
