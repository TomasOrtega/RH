import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
open GlobalTheory.WeilM Matrix

noncomputable section
open Filter
open scoped Topology

namespace GlobalTheory.RankChart

/- English proof (translation)
Introduce `k _ _ _ _ R T D _ _ _ _ _ _ f hf`. Take `⟨Λ, hΛo, hΛ⟩` from `GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ f hf`. Establish `hK : IsCompact (tsupport f)` using `hf.2`. Establish `hc : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => fromRows (0 : Matrix R D k) (p.1 * p.2.toRows₁)`. Establish `hm : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => p.1 * p.2.toRows₁` using `continuous_fst.matrix_mul (continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply (Sum.inl i) j).comp continuous_snd)`.

Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Break down `i with i | i` into its components or cases. Simplify using `using continuous_const`. Simplify using `only [fromRows_apply_inr]`. Conclude with `(continuous_apply_apply i j).comp hm`.

Establish `hev : ∀ᶠ c in 𝓝 (0 : Matrix T R k), ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ` using `hK.eventually_forall_of_forall_eventually fun Y _ => by`. Establish `h0 : fromRows (0 : Matrix R D k) ((0 : Matrix T R k) * Y.toRows₁) ∈ Λ`. Simplify using the standard rewrite rules. Conclude with `(hc.tendsto ((0 : Matrix T R k), Y)) (hΛo.mem_nhds h0)`. Take `⟨b, hb⟩` from `GlobalTheory.LocMod.Inhab.exists_box_subset hev`.

Use `⟨b, fun Y c hcb => ?_⟩` and prove the remaining obligations. Establish `hZ : ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ` using `hb c hcb`. Distinguish the cases in `hY : Y ∈ tsupport f`. Rewrite using `[← hΛ Y _ (hZ Y hY), ← shear_sub_self, add_sub_cancel]`. Distinguish the cases in `hY' : shear c Y ∈ tsupport f`.

Establish `h1` using `hZ _ hY'`. Rewrite `h1` using `[toRows₁_shear, ← shear_sub_self]`. Rewrite using `[← hΛ (shear c Y) _ (Λ.neg_mem h1), neg_sub, add_sub_cancel]`. Rewrite using `[image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']`.
-/
theorem sb_shear_invariant :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D],
      ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k),
        ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ f hf
  obtain ⟨Λ, hΛo, hΛ⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ f hf
  have hK : IsCompact (tsupport f) := hf.2
  have hc : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k =>
      fromRows (0 : Matrix R D k) (p.1 * p.2.toRows₁) := by
    have hm : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => p.1 * p.2.toRows₁ :=
      continuous_fst.matrix_mul (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply (Sum.inl i) j).comp continuous_snd)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simp only [fromRows_apply_inr]
      exact (continuous_apply_apply i j).comp hm
  have hev : ∀ᶠ c in 𝓝 (0 : Matrix T R k), ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ :=
    hK.eventually_forall_of_forall_eventually fun Y _ => by
      have h0 : fromRows (0 : Matrix R D k) ((0 : Matrix T R k) * Y.toRows₁) ∈ Λ := by
        simp
      exact (hc.tendsto ((0 : Matrix T R k), Y)) (hΛo.mem_nhds h0)
  obtain ⟨b, hb⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hev
  refine ⟨b, fun Y c hcb => ?_⟩
  have hZ : ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ := hb c hcb
  by_cases hY : Y ∈ tsupport f
  · rw [← hΛ Y _ (hZ Y hY), ← shear_sub_self, add_sub_cancel]
  by_cases hY' : shear c Y ∈ tsupport f
  · have h1 := hZ _ hY'
    rw [toRows₁_shear, ← shear_sub_self] at h1
    rw [← hΛ (shear c Y) _ (Λ.neg_mem h1), neg_sub, add_sub_cancel]
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']

end GlobalTheory.RankChart
