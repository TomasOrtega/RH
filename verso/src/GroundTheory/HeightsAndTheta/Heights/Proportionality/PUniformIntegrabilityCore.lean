import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Proportionality.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace Proportionality

open Filter Topology

/- English proof (translation)
Introduce `J j₀ Cst E ⟨hbase, hj, hC, hE, hrec⟩ a`. Proceed by induction on `a with`. Consider the case `zero`. Introduce `η hη`. Take `⟨u, hu, hsub⟩` from `mem_nhdsGT_iff_exists_Ioc_subset.1 ((tendsto_order.1 hj).2 η hη)`.

Use `⟨u, 1, hu, one_pos, ?_⟩` and prove the remaining obligations. Introduce `ε t hε hεu ht _`. Establish `hjε : j₀ ε < η` using `hsub ⟨hε, hεu⟩`. Combine the linear relations using `[hbase ε t hε ht]`. Consider the case `succ a ih`.

Introduce `η hη`. Take `⟨t₀, hEt₀, ht₀⟩` from `(((tendsto_order.1 hE).2 (η / 2) (half_pos hη)).and self_mem_nhdsWithin).exists`. Establish `ht₀' : (0 : ℝ) < t₀` using `ht₀`. Establish `hcpos : 0 < 1 + Cst t₀` using `by linarith [hC t₀]`. Take `⟨ε₀, t₁, hε₀, ht₁, hJ⟩` from `ih (η / (2 * (1 + Cst t₀))) (by positivity)`.

Use `⟨ε₀, min t₁ t₀, hε₀, lt_min ht₁ ht₀', ?_⟩` and prove the remaining obligations. Introduce `ε t hε hεle ht htle`. Establish `h1` using `hrec a ε t₀ t hε ht (htle.trans (min_le_right _ _))`. Establish `h2` using `hJ ε t hε hεle ht (htle.trans (min_le_left _ _))`. Establish `h3 : (1 + Cst t₀) * J a ε t ≤ (1 + Cst t₀) * (η / (2 * (1 + Cst t₀)))` using `mul_le_mul_of_nonneg_left h2 hcpos.le`.

Establish `h4 : (1 + Cst t₀) * (η / (2 * (1 + Cst t₀))) = η / 2`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UniformIntegrabilityCore.proof : UniformIntegrabilityCore.Statement := by
  intro J j₀ Cst E ⟨hbase, hj, hC, hE, hrec⟩ a
  induction a with
  | zero =>
    intro η hη
    obtain ⟨u, hu, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioc_subset.1 ((tendsto_order.1 hj).2 η hη)
    refine ⟨u, 1, hu, one_pos, ?_⟩
    intro ε t hε hεu ht _
    have hjε : j₀ ε < η := hsub ⟨hε, hεu⟩
    linarith [hbase ε t hε ht]
  | succ a ih =>
    intro η hη
    obtain ⟨t₀, hEt₀, ht₀⟩ :=
      (((tendsto_order.1 hE).2 (η / 2) (half_pos hη)).and self_mem_nhdsWithin).exists
    have ht₀' : (0 : ℝ) < t₀ := ht₀
    have hcpos : 0 < 1 + Cst t₀ := by linarith [hC t₀]
    obtain ⟨ε₀, t₁, hε₀, ht₁, hJ⟩ := ih (η / (2 * (1 + Cst t₀))) (by positivity)
    refine ⟨ε₀, min t₁ t₀, hε₀, lt_min ht₁ ht₀', ?_⟩
    intro ε t hε hεle ht htle
    have h1 := hrec a ε t₀ t hε ht (htle.trans (min_le_right _ _))
    have h2 := hJ ε t hε hεle ht (htle.trans (min_le_left _ _))
    have h3 : (1 + Cst t₀) * J a ε t ≤ (1 + Cst t₀) * (η / (2 * (1 + Cst t₀))) :=
      mul_le_mul_of_nonneg_left h2 hcpos.le
    have h4 : (1 + Cst t₀) * (η / (2 * (1 + Cst t₀))) = η / 2 := by
      field_simp
    linarith

end Proportionality

end GroundTheory.Heights₂.Heights
