import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.UnitMinorStable

/- English proof (translation)
Introduce `k _ _ _ _ n d E Y hE hY`. Take `⟨hYi, f, hf⟩` from `hY`. Establish `hEi` using `((GlobalTheory.SplitFlip.mem_KO_iff E).1 hE).1`. Use `⟨fun i j => ?_, f, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hEi i l) (hYi l j)`. Establish `hsub : (E.val * Y).submatrix id f = E.val * Y.submatrix id f`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hdet` using `GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hE`.

Establish `hg : ((GlobalTheory.SplitFlip.gdet E : kˣ) : k) = E.val.det` using `rfl`. Rewrite using `[hsub, Matrix.det_mul, map_mul, hf, mul_one, ← hg, hdet]`.
-/
theorem mul_mem_unitMinorSet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  intro k _ _ _ _ n d E Y hE hY
  obtain ⟨hYi, f, hf⟩ := hY
  have hEi := ((GlobalTheory.SplitFlip.mem_KO_iff E).1 hE).1
  refine ⟨fun i j => ?_, f, ?_⟩
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hEi i l) (hYi l j)
  · have hsub : (E.val * Y).submatrix id f = E.val * Y.submatrix id f := by
      ext i j; rfl
    have hdet := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hE
    have hg : ((GlobalTheory.SplitFlip.gdet E : kˣ) : k) = E.val.det := rfl
    rw [hsub, Matrix.det_mul, map_mul, hf, mul_one, ← hg, hdet]

end GlobalTheory.UnitMinorStable
