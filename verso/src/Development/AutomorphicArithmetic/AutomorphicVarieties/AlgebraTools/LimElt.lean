import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `G ι _ _ _ _ _ U K _`. Use `⟨fun a => ?_, fun a b b' hb hb' => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨b, hl⟩ : ∃ b : G, Tendsto a (U : Filter ι) (nhds b) := by`. Use `⟨(U.map a).lim, ?_⟩` and prove the remaining obligations. Establish `h'` using `(U.map a).le_nhds_lim`.

Rewrite `h'` using `[Ultrafilter.coe_map]`. Conclude with `h'`. Use `⟨b, fun O => ?_⟩` and prove the remaining obligations. Establish `hopen : IsOpen {y : G | b⁻¹ * y ∈ O.toSubgroup}` using `O.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)`. Conclude with `hl.eventually (hopen.mem_nhds (by simp))`.

Rewrite using `[mem_limKer]`. Introduce `O`. Use `filter_upwards [hb O, hb' O] with i h1 h2`. Establish `heq : b⁻¹ * b' = (b⁻¹ * a i) * (b'⁻¹ * a i)⁻¹` using `by group`. Rewrite using `[heq]`.

Conclude with `Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)`.
-/
theorem UpperTheory.V.AlgebraTools.exists_lim_elt :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      (∀ a : ι → G, ∃ b : G, ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ O.toSubgroup) ∧
      (∀ (a : ι → G) (b b' : G), (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ K i ⊔ O.toSubgroup) →
        (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b'⁻¹ * a i ∈ K i ⊔ O.toSubgroup) → b⁻¹ * b' ∈ limKer (U : Filter ι) K) := by
  intro G ι _ _ _ _ _ U K _
  refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
  · obtain ⟨b, hl⟩ : ∃ b : G, Tendsto a (U : Filter ι) (nhds b) := by
      refine ⟨(U.map a).lim, ?_⟩
      have h' := (U.map a).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    refine ⟨b, fun O => ?_⟩
    have hopen : IsOpen {y : G | b⁻¹ * y ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)
    exact hl.eventually (hopen.mem_nhds (by simp))
  · rw [mem_limKer]
    intro O
    filter_upwards [hb O, hb' O] with i h1 h2
    have heq : b⁻¹ * b' = (b⁻¹ * a i) * (b'⁻¹ * a i)⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
