import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ O _ _ F n C _ _ _ K _ _ ρ hC`. Establish `off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ), (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2`. Introduce `L j hL hj`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[← hL]`. Apply `List.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`. Take `⟨s, hs, rfl⟩` from `List.mem_map.1 hx`.

Rewrite using `[h s hs, sub_self]`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Establish `hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K)`. Introduce and unpack `_ ⟨L, hL, rfl⟩`.

Distinguish the cases in `hd : ∃ s ∈ L, s.2.1 ≠ s.2.2`. Take `⟨c, -, hc⟩` from `hC.cyc L hL hd`. Conclude with `⟨c, hc⟩`. Use `push_neg at hd`. Establish `hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS`.

Apply `list_prod_mem` to reduce the goal to its premises. Introduce `y hy`. Take `⟨s, hs, rfl⟩` from `List.mem_map.1 hy`. Rewrite using `[← hd s hs]`. Take `⟨c, hc, -⟩` from `hC.dg s.1 s.2.1`.

Conclude with `⟨c, hc⟩`. Take `⟨c, hc⟩` from `hm`. Conclude with `⟨c, hc⟩`. Take `⟨c, hc⟩` from `Submodule.span_le.2 hle hx`. Conclude with `⟨c, hc⟩`.

Introduce `j hj x hx y hy open Pointwise in`. Establish `hle : ρ.mon j * ρ.mon (-j) ⊆ (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K)`. Introduce and unpack `_ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩`. Take `⟨s, hs, hne⟩` from `off L1 j h1 hj`. Take `⟨c, hc, hc'⟩` from `hC.cyc (L1 ++ L2) (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩`.

Use `Submodule.mem_map.2 ⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.linearMap_apply, hc', List.map_append, List.prod_append]`. Use `open Pointwise in`. Establish `hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j))`. Rewrite using `[← Submodule.span_mul_span]`.

Conclude with `Submodule.mul_mem_mul hx hy`. Take `⟨c, hc, hc'⟩` from `Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)`. Conclude with `⟨c, hc, hc'⟩`.
-/
theorem UpperTheory.V.Fr.alg_vertex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → HasVertex (ρ.part C) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hC
  have off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ),
      (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2 := by
    intro L j hL hj
    by_contra h
    push_neg at h
    apply hj
    rw [← hL]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    rw [h s hs, sub_self]
  constructor
  · intro x hx
    have hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K) := by
      rintro _ ⟨L, hL, rfl⟩
      by_cases hd : ∃ s ∈ L, s.2.1 ≠ s.2.2
      · obtain ⟨c, -, hc⟩ := hC.cyc L hL hd
        exact ⟨c, hc⟩
      · push_neg at hd
        have hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS := by
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
          rw [← hd s hs]
          obtain ⟨c, hc, -⟩ := hC.dg s.1 s.2.1
          exact ⟨c, hc⟩
        obtain ⟨c, hc⟩ := hm
        exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := Submodule.span_le.2 hle hx
    exact ⟨c, hc⟩
  · intro j hj x hx y hy
    open Pointwise in
    have hle : ρ.mon j * ρ.mon (-j) ⊆
        (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K) := by
      rintro _ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩
      obtain ⟨s, hs, hne⟩ := off L1 j h1 hj
      obtain ⟨c, hc, hc'⟩ := hC.cyc (L1 ++ L2)
        (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩
      refine Submodule.mem_map.2 ⟨c, hc, ?_⟩
      rw [Algebra.linearMap_apply, hc', List.map_append, List.prod_append]
    open Pointwise in
    have hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j)) := by
      rw [← Submodule.span_mul_span]
      exact Submodule.mul_mem_mul hx hy
    obtain ⟨c, hc, hc'⟩ := Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)
    exact ⟨c, hc, hc'⟩
