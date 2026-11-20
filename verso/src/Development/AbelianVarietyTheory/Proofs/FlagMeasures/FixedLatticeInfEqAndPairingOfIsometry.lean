import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem trip_fixLat_inf_eq_and_pairing : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  intro K V _ _ _ _ _ _ _ _ H _ _ L₀ g j D₀ _ _ _ _ x x' p hp
  obtain ⟨h1, -, -, -, h5⟩ := hp
  have hmem : ∀ (Γ : Submodule (𝓞 K) (V × V)) (y : V), y ∈ fixLat Γ ↔ (y, y) ∈ Γ := fun _ _ => Iff.rfl
  refine ⟨?_, ?_⟩
  · ext y
    have hf : y ∈ rs (𝓞 K) (fixSp p.2.2) ↔ p.2.2 y = y := by
      simp [fixSp, sub_eq_zero]
    rw [Submodule.mem_inf, Submodule.mem_inf, hmem, hmem, hf, h5]
    refine and_congr_left fun h => ?_
    rw [h]
  · intro y hy y' hy'
    rw [hmem] at hy hy'
    rw [h5] at hy'
    obtain ⟨t, ht⟩ := h1.2.2.1.2.2.2.2.2.2 _ hy _ hy'
    refine ⟨-t, ?_⟩
    simp only [map_mul, map_natCast] at ht
    rw [map_sub]
    have : ((-t : 𝓞 K) : K) = -(algebraMap (𝓞 K) K t) := map_neg (algebraMap (𝓞 K) K) t
    rw [this]
    linear_combination -ht

end GlobalTheory.DegCnt
