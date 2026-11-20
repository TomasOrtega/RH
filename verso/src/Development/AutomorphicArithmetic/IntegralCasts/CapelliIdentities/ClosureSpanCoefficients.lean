import Mathlib

/- English proof (translation)
Introduce `R M L _ _ _ _ O f m x hx z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨a, ha, l, rfl⟩` from `hz`. Establish `hl : l ∈ Submodule.span ℤ (Set.range x)` using `hx ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hl`. Use `⟨fun i => c i • a, fun i => O.zsmul_mem ha _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, smul_assoc, smul_comm]`. Consider the case `zero => exact ⟨0, fun _ => O.zero_mem, by simp⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨a, ha, rfl⟩` from `hu`.

Take `⟨b, hb, rfl⟩` from `hv`. Conclude with `⟨a + b, fun i => O.add_mem (ha i) (hb i), by`. Simplify using `[add_smul, Finset.sum_add_distrib]⟩`. Consider the case `neg u _ hu`. Take `⟨a, ha, rfl⟩` from `hu`.

Conclude with `⟨-a, fun i => O.neg_mem (ha i), by simp⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `sum_mem fun i _ => AddSubgroup.subset_closure ⟨a i, ha i, x i, rfl⟩`.
-/
theorem UpperTheory.closure_span_coefficients :
    ∀ {R M L : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup L] (O : AddSubgroup R) (f : L →+ M) {m : ℕ} (x : Fin m → L),
        Submodule.span ℤ (Set.range x) = ⊤ → ∀ z : M,
          z ∈ AddSubgroup.closure {z : M | ∃ a ∈ O, ∃ l : L, z = a • f l} ↔
            ∃ a : Fin m → R, (∀ i, a i ∈ O) ∧ ∑ i, a i • f (x i) = z := by
  intro R M L _ _ _ _ O f m x hx z
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, rfl⟩ := hz
      have hl : l ∈ Submodule.span ℤ (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hl
      refine ⟨fun i => c i • a, fun i => O.zsmul_mem ha _, ?_⟩
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    | zero => exact ⟨0, fun _ => O.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a + b, fun i => O.add_mem (ha i) (hb i), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg u _ hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      exact ⟨-a, fun i => O.neg_mem (ha i), by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨a i, ha i, x i, rfl⟩
