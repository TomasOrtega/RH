import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

/- English proof (translation)
Introduce `G A ι _ _ _ _ _ _ e ρ hρ hlim`. Establish `hsub : ∀ k, tsupport (fun T : G => ∏ i, ρ k (e T i)) ⊆ e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k))`. Introduce `k`. Apply `closure_minimal` to reduce the goal to its premises. Introduce `T hT`.

Simplify using `only [Set.mem_preimage, Set.mem_univ_pi]`. Introduce `i`. Apply `subset_tsupport` to reduce the goal to its premises. Rewrite `hT`, the goal using `[Function.mem_support]`. Conclude with `(Finset.prod_ne_zero_iff.mp hT) i (Finset.mem_univ i)`.

Conclude with `(isClosed_set_pi fun i _ => isClosed_tsupport (ρ k)).preimage (map_continuous e)`. Use `⟨fun k => ⟨?_, ?_, fun T => Finset.prod_nonneg fun i _ => (hρ k).2.2 _⟩, ?_⟩` and prove the remaining obligations. Conclude with `continuous_finsetProd _ fun i _ => (hρ k).1.comp ((continuous_apply i).comp (map_continuous e))`. Establish `hS : IsCompact (e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k)))` using `(Homeomorph.isCompact_preimage (e : G ≃ₜ (ι → A))).mpr (isCompact_univ_pi fun _ => (hρ k).2.1)`. Conclude with `IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub k)`.

Rewrite `hlim`, the goal using `[Filter.tendsto_smallSets_iff]`. Introduce `U hU`. Establish `hV : e.symm ⁻¹' U ∈ nhds (0 : ι → A)` using `(map_continuous e.symm).continuousAt.preimage_mem_nhds (by rwa [map_zero])`. Rewrite `hV` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hIt⟩` from `hV`.

Establish `hW : (⋂ i, t i) ∈ nhds (0 : A)` using `Filter.iInter_mem.mpr fun i => by simpa using ht i`. Use `filter_upwards [hlim _ hW] with k hk`. Introduce `T hT`. Establish `h1` using `hsub k hT`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi] at h1`.

Establish `h2 : e T ∈ I.pi t` using `fun i _ => Set.mem_iInter.mp (hk (h1 i)) i`. Simplify using `using hIt h2`.
-/
theorem prod_coordinate_bumps :
    ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A]
      [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ),
      (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) →
      Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets →
      (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧
        HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧
        ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧
      Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop
        (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ _ e ρ hρ hlim
  have hsub : ∀ k, tsupport (fun T : G => ∏ i, ρ k (e T i)) ⊆
      e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k)) := by
    intro k
    apply closure_minimal
    · intro T hT
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      intro i
      apply subset_tsupport
      rw [Function.mem_support] at hT ⊢
      exact (Finset.prod_ne_zero_iff.mp hT) i (Finset.mem_univ i)
    · exact (isClosed_set_pi fun i _ => isClosed_tsupport (ρ k)).preimage (map_continuous e)
  refine ⟨fun k => ⟨?_, ?_, fun T => Finset.prod_nonneg fun i _ => (hρ k).2.2 _⟩, ?_⟩
  · exact continuous_finsetProd _ fun i _ => (hρ k).1.comp ((continuous_apply i).comp (map_continuous e))
  · have hS : IsCompact (e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k))) :=
      (Homeomorph.isCompact_preimage (e : G ≃ₜ (ι → A))).mpr (isCompact_univ_pi fun _ => (hρ k).2.1)
    exact IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub k)
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro U hU
    have hV : e.symm ⁻¹' U ∈ nhds (0 : ι → A) :=
      (map_continuous e.symm).continuousAt.preimage_mem_nhds (by rwa [map_zero])
    rw [nhds_pi, Filter.mem_pi] at hV
    obtain ⟨I, -, t, ht, hIt⟩ := hV
    have hW : (⋂ i, t i) ∈ nhds (0 : A) := Filter.iInter_mem.mpr fun i => by simpa using ht i
    filter_upwards [hlim _ hW] with k hk
    intro T hT
    have h1 := hsub k hT
    simp only [Set.mem_preimage, Set.mem_univ_pi] at h1
    have h2 : e T ∈ I.pi t := fun i _ => Set.mem_iInter.mp (hk (h1 i)) i
    simpa using hIt h2

end GlobalTheory.CompanionTheory.BigCell
