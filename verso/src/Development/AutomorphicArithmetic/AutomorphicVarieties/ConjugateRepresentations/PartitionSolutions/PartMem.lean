import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
open UpperTheory.V.Cj.A UpperTheory.V.Lit
open scoped ContDiff

/- English proof (translation)
Introduce `Γ V S I _ _ _ _ d G φ hφ q c`. Rewrite using `[Dr.Geo.mem_Om]`. Introduce `s`. Use `⟨fun p hp => ?_, fun p hp => ?_⟩` and prove the remaining obligations. Take `⟨N, hN, hfin⟩` from `hφ.locFin s p hp`.

Establish `hsum : ContDiffAt ℝ ∞ (fun x => ∑ i ∈ hfin.toFinset, φ i s x • (c i).1 s x) p` using `ContDiffAt.sum fun i _ => ((hφ.smooth i s).contDiffAt (G.isOpen.mem_nhds hp)).smul (Dr.Geo.contDiffAt_Om (c i) s hp)`. Use `(hsum.congr_of_eventuallyEq ?_).contDiffWithinAt` and prove the remaining obligations. Use `filter_upwards [hN] with x hx`. Use `finsum_eq_sum_of_support_subset _ fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset]`.

Use `⟨x, hx, fun h => hi ?_⟩` and prove the remaining obligations. Simplify using `only [h, zero_smul]`. Establish `h : ∀ i : I, φ i s p • (c i).1 s p = 0` using `fun i => by`. Rewrite using `[((c i).2 s).2 p hp, smul_zero]`. Simplify using `only [h, finsum_zero]`.
-/
theorem UpperTheory.V.Cj.A.partMem :
    PartMem := by
  intro Γ V S I _ _ _ _ d G φ hφ q c
  rw [Dr.Geo.mem_Om]
  intro s
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨N, hN, hfin⟩ := hφ.locFin s p hp
    have hsum : ContDiffAt ℝ ∞ (fun x => ∑ i ∈ hfin.toFinset, φ i s x • (c i).1 s x) p :=
      ContDiffAt.sum fun i _ =>
        ((hφ.smooth i s).contDiffAt (G.isOpen.mem_nhds hp)).smul (Dr.Geo.contDiffAt_Om (c i) s hp)
    refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hN] with x hx
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hx, fun h => hi ?_⟩
    simp only [h, zero_smul]
  · have h : ∀ i : I, φ i s p • (c i).1 s p = 0 := fun i => by
      rw [((c i).2 s).2 p hp, smul_zero]
    simp only [h, finsum_zero]
