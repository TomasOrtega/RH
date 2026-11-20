import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsRegular
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsDescend
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartConstantsDetermined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

/- English proof (translation)
Introduce `K _ ι _ Ω _ F _ _ _ y hy`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `hfin : Module.Finite ℤ (intsIn F Ω)` using `Module.Finite.of_surjective ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap (AlgHom.rangeRestrict_surjective _)`. Establish `key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c)`. Introduce `c`.

Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Establish `hfg : (chartRingZ y c).FG` using `⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by`. Simplify using `[chartRingZ, Set.image_univ]⟩`. Take `⟨m, hm, h⟩` from `hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)`. Conclude with `⟨m, hm, fun _ => h⟩`.

Conclude with `⟨1, le_rfl, fun h => absurd h hc⟩`. Use `choose m hm hmem using key`. Use `⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩` and prove the remaining obligations. Introduce `θ c hc`. Establish `ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω` using `(AlgHom.mem_range _).mpr ⟨θ, rfl⟩`.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)`.
-/
theorem ConstantsRegular.proof (hD : ConstantsDescend.Statement)
    (hC : ChartConstantsDetermined.Statement) : ConstantsRegular.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hy
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hfin : Module.Finite ℤ (intsIn F Ω) :=
    Module.Finite.of_surjective
      ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · have hfg : (chartRingZ y c).FG :=
        ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by
          simp [chartRingZ, Set.image_univ]⟩
      obtain ⟨m, hm, h⟩ := hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)
      exact ⟨m, hm, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose m hm hmem using key
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩
  intro θ c hc
  have ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω := (AlgHom.mem_range _).mpr ⟨θ, rfl⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)

end GroundTheory.Heights₂.Heights.HilbertSamuel
