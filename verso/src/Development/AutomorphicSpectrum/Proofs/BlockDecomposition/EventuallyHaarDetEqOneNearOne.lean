import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DistribHaarCharEqOneOfValuationEqOne

open Matrix ValuativeRel MeasureTheory
open scoped Topology

namespace GlobalTheory.CompanionTheory.LocalModule

/- English proof (translation)
Introduce `k _ _ _ _ n`. Establish `hc : Continuous fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k)`. Establish `: (fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k)) = fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det` using `rfl`. Rewrite using `[this]`. Conclude with `Continuous.matrix_det Units.continuous_val`.

Establish `hO : IsOpen {x : k | valuation k (x - 1) < 1}`. Establish `h : IsOpen {z : k | valuation k z < 1}` using `by simpa using (valuation k).isOpen_ball 1`. Conclude with `h.preimage (continuous_id.sub continuous_const)`. Establish `hm : ∀ᶠ g in nhds (1 : GL (Fin n) k), ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ {x : k | valuation k (x - 1) < 1}`. Use `hc.continuousAt.eventually (hO.mem_nhds ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Use `filter_upwards [hm] with g hg`. Use `distribHaarChar_eq_one_of_valuation_eq_one k _ ?_` and prove the remaining obligations. Establish `hv : valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1` using `hg`. Establish `h1` using `Valuation.map_one_add_of_lt (valuation k) hv`.

Rewrite `h1` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem distribHaarChar_det_eventually_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k),
        MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n
  have hc : Continuous fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k) := by
    have : (fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k)) =
        fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det := rfl
    rw [this]
    exact Continuous.matrix_det Units.continuous_val
  have hO : IsOpen {x : k | valuation k (x - 1) < 1} := by
    have h : IsOpen {z : k | valuation k z < 1} := by simpa using (valuation k).isOpen_ball 1
    exact h.preimage (continuous_id.sub continuous_const)
  have hm : ∀ᶠ g in nhds (1 : GL (Fin n) k),
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ {x : k | valuation k (x - 1) < 1} := by
    refine hc.continuousAt.eventually (hO.mem_nhds ?_)
    simp
  filter_upwards [hm] with g hg
  refine distribHaarChar_eq_one_of_valuation_eq_one k _ ?_
  have hv : valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := hg
  have h1 := Valuation.map_one_add_of_lt (valuation k) hv
  rwa [add_sub_cancel] at h1

end GlobalTheory.CompanionTheory.LocalModule
