import Mathlib

/- English proof (translation)
Introduce `S R M _ _ _ _ _ hfin f hf`. Take `⟨T, hT⟩` from `hfin.fg_top`. Use `⟨⟨T, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `m hm0`.

Use `clear hm0`. Establish `hm : m ∈ Submodule.span S (T : Set M)`. Rewrite using `[hT]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[hf]`.

Conclude with `Submodule.smul_mem _ _ hx`.
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
