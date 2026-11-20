import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ v p d h ty G γ hB t w hw`. Take `⟨hγ, hγty, hdet⟩` from `hB`. Establish `hdet' : v (PTb.tmat γ).det = 0` using `hdet`. Establish `ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0`. Introduce `b c hc`.

Rewrite using `[PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]`. Conclude with `(hγty b).2 0 c (by simpa using hc)`. Use `set x : Fin d → C := Matrix.vecMul w (PTb.tmat γ)⁻¹ with hx`. Establish `hxw : Matrix.vecMul x (PTb.tmat γ) = w` using `PTb.vecMul_inv_tmat hdet' w`. Establish `hsupp : ∀ b, ty b ≠ t → x b = 0` using `PTb.vecMul_tmat_support ty hdet' ht x t (fun c hc => by rw [hxw]; exact hw c hc)`.

Establish `hsum : w = ∑ b, x b • tangent (γ b)` using `by rw [PTb.sum_smul_tangent, hxw]`. Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : ty b = t`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)`.

Rewrite using `[hsupp b hb, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem span_tangent_of_type : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p d h : ℕ) (ty : Fin d → ZMod h)
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), IsBasis G p ty γ →
    ∀ (t : ZMod h) (w : Fin d → C), (∀ c, ty c ≠ t → w c = 0) →
      w ∈ Submodule.span C (Set.range fun b : {b // ty b = t} => tangent (γ b.1)) := by
  intro C _ v p d h ty G γ hB t w hw
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    rw [PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]
    exact (hγty b).2 0 c (by simpa using hc)
  set x : Fin d → C := Matrix.vecMul w (PTb.tmat γ)⁻¹ with hx
  have hxw : Matrix.vecMul x (PTb.tmat γ) = w := PTb.vecMul_inv_tmat hdet' w
  have hsupp : ∀ b, ty b ≠ t → x b = 0 :=
    PTb.vecMul_tmat_support ty hdet' ht x t (fun c hc => by rw [hxw]; exact hw c hc)
  have hsum : w = ∑ b, x b • tangent (γ b) := by rw [PTb.sum_smul_tangent, hxw]
  rw [hsum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : ty b = t
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)
  · rw [hsupp b hb, zero_smul]; exact Submodule.zero_mem _

end GlobalTheory
