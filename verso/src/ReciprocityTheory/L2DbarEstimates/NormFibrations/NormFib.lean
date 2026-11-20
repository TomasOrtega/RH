import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormFibStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ y : V n, (z ⁻¹' {y}).Finite) → ConnectedSpace M →
    ∃ δ : ℕ, ∀ y : V n, (z ⁻¹' {y}).encard ≤ δ

/- English proof (translation)
Introduce `n M _ z U hcov himg hfin hconn`. Establish `hloc : ∀ x : M, ∀ᶠ x' in 𝓝 x, (z ⁻¹' {z x'}).encard = (z ⁻¹' {z x}).encard`. Introduce `x`. Take `⟨hd, W, hxW, hW, hzW, H, hH⟩` from `hcov (z x) (himg x)`. Establish `hev : ∀ w ∈ W, IsEvenlyCovered z w (z ⁻¹' {z x})` using `fun w hw => ⟨hd, W, hw, hW, hzW, H, hH⟩`.

Use `filter_upwards [hzW.mem_nhds (show x ∈ z ⁻¹' W from hxW)] with x' hx'`. Conclude with `Set.encard_congr (hev (z x') hx').fiberHomeomorph.toEquiv.symm`. Take `⟨x0⟩` from `(inferInstance : Nonempty M)`. Establish `hS : IsClopen {x : M | (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard}`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `x hx`. Use `filter_upwards [hloc x] with x' hx'`. Simplify using `only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢`. Rewrite using `[hx']`.

Conclude with `hx`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Use `filter_upwards [hloc x] with x' hx'`. Simplify using `only [Set.mem_ofPred_eq] at hx ⊢`.

Rewrite using `[hx', hx]`. Establish `hall` using `hS.eq_univ ⟨x0, rfl⟩`. Use `⟨(z ⁻¹' {z x0}).ncard, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[(hfin (z x0)).cast_ncard_eq]`. Distinguish the cases in `hy : ∃ x, z x = y`.

Take `⟨x, rfl⟩` from `hy`. Establish `hx : (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard` using `Set.eq_univ_iff_forall.1 hall x`. Conclude with `hx.le`. Establish `h0 : z ⁻¹' {y} = ∅`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun h => hy ⟨x, h⟩`. Rewrite using `[h0, Set.encard_empty]`. Conclude with `zero_le`.
-/
theorem normFib : NormFibStatement.{u} := by
  intro n M _ z U hcov himg hfin hconn

  have hloc : ∀ x : M, ∀ᶠ x' in 𝓝 x, (z ⁻¹' {z x'}).encard = (z ⁻¹' {z x}).encard := by
    intro x
    obtain ⟨hd, W, hxW, hW, hzW, H, hH⟩ := hcov (z x) (himg x)
    have hev : ∀ w ∈ W, IsEvenlyCovered z w (z ⁻¹' {z x}) :=
      fun w hw => ⟨hd, W, hw, hW, hzW, H, hH⟩
    filter_upwards [hzW.mem_nhds (show x ∈ z ⁻¹' W from hxW)] with x' hx'
    exact Set.encard_congr (hev (z x') hx').fiberHomeomorph.toEquiv.symm
  obtain ⟨x0⟩ := (inferInstance : Nonempty M)
  have hS : IsClopen {x : M | (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard} := by
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
      rw [hx']
      exact hx
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx', hx]
  have hall := hS.eq_univ ⟨x0, rfl⟩
  refine ⟨(z ⁻¹' {z x0}).ncard, fun y => ?_⟩
  rw [(hfin (z x0)).cast_ncard_eq]
  by_cases hy : ∃ x, z x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx : (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard := Set.eq_univ_iff_forall.1 hall x
    exact hx.le
  · have h0 : z ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hy ⟨x, h⟩
    rw [h0, Set.encard_empty]
    exact zero_le

end ReciprocityTheory.L2DbarEstimates
