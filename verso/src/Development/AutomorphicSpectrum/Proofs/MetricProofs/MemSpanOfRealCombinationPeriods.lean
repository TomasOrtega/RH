import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

/- English proof (translation)
Introduce `g k n Λ _ P b f hli hf x c hx`. Establish `hPx : P x = ∑ j, ((b.repr x j : ℤ) : ℝ) • P (b j)` using `by conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`.

Set `d : Fin n → ℝ` to `fun j => ∑ i, if f i = j then c i else 0`. Establish `hPd : P x = ∑ j, d j • P (b j)`. Rewrite using `[hx]`. Simplify using `only [d, Finset.sum_smul, ite_smul, zero_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Complex.coe_smul]`. Establish `hcoef : ∀ j, ((b.repr x j : ℤ) : ℝ) = d j`. Establish `h0 : ∑ j, (((b.repr x j : ℤ) : ℝ) - d j) • P (b j) = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[← hPx, ← hPd, sub_self]`. Introduce `j`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 j)`. Establish `hzero : ∀ j, j ∉ Set.range f → b.repr x j = 0`. Introduce `j hj`.

Establish `hd : d j = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Conclude with `fun h => hj ⟨i, h⟩`. Use `hcoef j` as an intermediate fact.

Rewrite `this` using `[hd]`. Conclude with `this` after adjusting the coercions. Rewrite using `[← b.sum_repr x]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j ∈ Set.range f`.

Take `⟨i, rfl⟩` from `hj`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[hzero j hj, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_span_part_of_period_real_comb :
    ∀ (g k n : ℕ) (Λ : Type) [AddCommGroup Λ] (P : Λ →+ (Fin g → ℂ))
      (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
      LinearIndependent ℝ (fun j => P (b j)) → Function.Injective f →
      ∀ (x : Λ) (c : Fin k → ℝ), P x = ∑ i, (c i : ℂ) • P (b (f i)) →
        x ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := by
  intro g k n Λ _ P b f hli hf x c hx
  classical

  have hPx : P x = ∑ j, ((b.repr x j : ℤ) : ℝ) • P (b j) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  let d : Fin n → ℝ := fun j => ∑ i, if f i = j then c i else 0
  have hPd : P x = ∑ j, d j • P (b j) := by
    rw [hx]
    simp only [d, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Complex.coe_smul]
  have hcoef : ∀ j, ((b.repr x j : ℤ) : ℝ) = d j := by
    have h0 : ∑ j, (((b.repr x j : ℤ) : ℝ) - d j) • P (b j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hPx, ← hPd, sub_self]
    intro j
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 j)
  have hzero : ∀ j, j ∉ Set.range f → b.repr x j = 0 := by
    intro j hj
    have hd : d j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      exact fun h => hj ⟨i, h⟩
    have := hcoef j
    rw [hd] at this
    exact_mod_cast this
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hzero j hj, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.Ar.Cusp
