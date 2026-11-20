import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FnIndep

open UpperTheory.V.Hi

/- English proof (translation)
Introduce `O Ω V α _ _ _ _ _ _ _ _ m ψ S hinj hfree hrange hker F hF hψF`. Use `haveI := hfree`. Set `b` to `Module.Free.chooseBasis O S`. Establish `hex : ∀ i g j, ∃ r : O, algebraMap O Ω r = ψ (b i : V) g j` using `fun i g j => RingHom.mem_range.1 (hrange _ (b i).2 g j)`. Use `choose v hv using hex`.

Establish `hvli : LinearIndependent O v`. Rewrite using `[linearIndependent_iff']`. Introduce `s c hsum i hi`. Establish `hx : ψ ((∑ k ∈ s, c k • b k : S) : V) = 0`. Use function extensionality and compare the values at `g j`.

Establish `h0` using `congrFun (congrFun hsum g) j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, Finset.sum_apply, Pi.zero_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul Ω (c k) (b k : V), map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hv]`. Use `_ = 0 := by rw [← map_sum, h0, map_zero]`. Establish `hx0 : (∑ k ∈ s, c k • b k : S) = 0` using `Subtype.ext (hker _ (Submodule.coe_mem _) hx)`. Conclude with `linearIndependent_iff'.1 b.linearIndependent s c hx0 i hi`. Establish `hw : LinearIndependent Ω (fun i => ψ (b i : V))`.

Establish `h1` using `UpperTheory.V.Hi.fnIndep O Ω α _ hinj m v hvli`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i g j`. Conclude with `(hv i g j).symm`. Establish `hS : Submodule.span O (Set.range (fun i => (b i : V))) = S`.

Establish `h2 : Set.range (fun i => (b i : V)) = S.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h2, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hsub : (S : Set V) ⊆ Submodule.span Ω (Set.range (fun i => (b i : V)))`.

Introduce `x hx`. Establish `hx' : x ∈ Submodule.span O (Set.range (fun i => (b i : V)))`. Rewrite using `[hS]`. Conclude with `hx`. Conclude with `Submodule.span_le_restrictScalars O Ω _ hx'`.

Establish `hF'` using `Submodule.span_le.2 hsub hF`. Take `⟨c, rfl⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hF'`. Establish `hc : c = 0`. Use `linearIndependent_iff.1 hw c ?_` and prove the remaining obligations. Rewrite using `[Finsupp.linearCombination_apply]`.

Simplify `hψF` using `only [Finsupp.sum, map_sum, map_smul]`. Rewrite using `[hc, Finsupp.sum_zero_index]`.
-/
theorem UpperTheory.injective_on_span_of_integral_free_submodule :
    ∀ (O Ω V α : Type) [CommRing O] [IsDomain O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] (m : ℕ) (ψ : V →ₗ[Ω] (α → Fin m → Ω)) (S : Submodule O V), Function.Injective (algebraMap O Ω) → Module.Free O S → (∀ F ∈ S, ∀ g i, ψ F g i ∈ (algebraMap O Ω).range) → (∀ F ∈ S, ψ F = 0 → F = 0) → ∀ F ∈ Submodule.span Ω (S : Set V), ψ F = 0 → F = 0 := by
  intro O Ω V α _ _ _ _ _ _ _ _ m ψ S hinj hfree hrange hker F hF hψF
  classical
  haveI := hfree
  let b := Module.Free.chooseBasis O S
  have hex : ∀ i g j, ∃ r : O, algebraMap O Ω r = ψ (b i : V) g j := fun i g j =>
    RingHom.mem_range.1 (hrange _ (b i).2 g j)
  choose v hv using hex
  have hvli : LinearIndependent O v := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have hx : ψ ((∑ k ∈ s, c k • b k : S) : V) = 0 := by
      funext g j
      have h0 := congrFun (congrFun hsum g) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, Finset.sum_apply, Pi.zero_apply]
      calc ∑ k ∈ s, ψ (c k • (b k : V)) g j = ∑ k ∈ s, algebraMap O Ω (c k * v k g j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← algebraMap_smul Ω (c k) (b k : V), map_smul, Pi.smul_apply, Pi.smul_apply,
              smul_eq_mul, map_mul, hv]
        _ = 0 := by rw [← map_sum, h0, map_zero]
    have hx0 : (∑ k ∈ s, c k • b k : S) = 0 := Subtype.ext (hker _ (Submodule.coe_mem _) hx)
    exact linearIndependent_iff'.1 b.linearIndependent s c hx0 i hi
  have hw : LinearIndependent Ω (fun i => ψ (b i : V)) := by
    have h1 := UpperTheory.V.Hi.fnIndep O Ω α _ hinj m v hvli
    convert h1 using 1
    funext i g j
    exact (hv i g j).symm
  have hS : Submodule.span O (Set.range (fun i => (b i : V))) = S := by
    have h2 : Set.range (fun i => (b i : V)) = S.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [h2, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsub : (S : Set V) ⊆ Submodule.span Ω (Set.range (fun i => (b i : V))) := by
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range (fun i => (b i : V))) := by
      rw [hS]
      exact hx
    exact Submodule.span_le_restrictScalars O Ω _ hx'
  have hF' := Submodule.span_le.2 hsub hF
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hF'
  have hc : c = 0 := by
    refine linearIndependent_iff.1 hw c ?_
    rw [Finsupp.linearCombination_apply]
    simpa only [Finsupp.sum, map_sum, map_smul] using hψF
  rw [hc, Finsupp.sum_zero_index]
