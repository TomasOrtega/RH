import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qh10.fin_of_hom :
    ∀ {S R M : Type} [inst : CommRing S] [inst_1 : CommRing R]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module S M] [inst_4 : _root_.Module R M] [Module.Finite S M] (f : S → R),
    (∀ (a : S) (m : M), a • m = f a • m) → Module.Finite R M := by
  intro S R M _ _ _ _ _ hfin f hf
  obtain ⟨T, hT⟩ := hfin.fg_top
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro m hm0
  clear hm0
  have hm : m ∈ Submodule.span S (T : Set M) := by
    rw [hT]
    exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [hf]
    exact Submodule.smul_mem _ _ hx
