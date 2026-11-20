import Mathlib

namespace GlobalTheory.FiniteGenIntegerScalar

/- English proof (translation)
Take `⟨S, rfl⟩` from `hM`. Use `choose f hf0 hfL using h`. Use `⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ => hf0 s, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Set `P : Submodule (NumberField.RingOfIntegers E) V` to `{ carrier := {y | (∏ s ∈ S, f s) • y ∈ L} add_mem' := fun {a b} ha hb => by show _ ∈ L`.

Rewrite using `[smul_add]`. Conclude with `L.add_mem ha hb`. Use the proof step `zero_mem' := by show _ ∈ L`. Rewrite using `[smul_zero]`. Conclude with `L.zero_mem`.

Use the proof step `smul_mem' := fun c y hy => by show _ ∈ L`. Rewrite using `[smul_comm (∏ s ∈ S, f s) c y]`. Conclude with `L.smul_mem c hy }`. Establish `hle : Submodule.span _ (S : Set V) ≤ P`. Rewrite using `[Submodule.span_le]`.

Introduce `s hs`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem f hs`. Use `show (∏ s ∈ S, f s) • s ∈ L`. Rewrite using `[hk, mul_comm, mul_smul]`. Conclude with `zsmul_mem (hfL s) k`.

Conclude with `hle hx`.
-/
theorem exists_int_smul_mem_of_fg {E : Type} [Field E] {V : Type} [AddCommGroup V]
    [Module (NumberField.RingOfIntegers E) V]
    {L M : Submodule (NumberField.RingOfIntegers E) V}
    (h : ∀ x : V, ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L) (hM : M.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ M, N • x ∈ L := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose f hf0 hfL using h
  refine ⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ => hf0 s, ?_⟩
  intro x hx
  let P : Submodule (NumberField.RingOfIntegers E) V :=
    { carrier := {y | (∏ s ∈ S, f s) • y ∈ L}
      add_mem' := fun {a b} ha hb => by
        show _ ∈ L
        rw [smul_add]
        exact L.add_mem ha hb
      zero_mem' := by
        show _ ∈ L
        rw [smul_zero]
        exact L.zero_mem
      smul_mem' := fun c y hy => by
        show _ ∈ L
        rw [smul_comm (∏ s ∈ S, f s) c y]
        exact L.smul_mem c hy }
  have hle : Submodule.span _ (S : Set V) ≤ P := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hs
    show (∏ s ∈ S, f s) • s ∈ L
    rw [hk, mul_comm, mul_smul]
    exact zsmul_mem (hfL s) k
  exact hle hx

end GlobalTheory.FiniteGenIntegerScalar
