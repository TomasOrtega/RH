import Mathlib

namespace GlobalTheory.CommonSmulMembership

/- English proof (translation)
Take `⟨S, rfl⟩` from `hL`. Use `choose f hfP hf using h`. Set `g : S → O` to `fun x => f x (Submodule.subset_span x.2)`. Use `⟨∏ x : S, g x, P.prod_mem (fun x _ => hfP _ _), ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Establish `hx' : x ∈ S` using `hx`. Rewrite using `[← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]`. Conclude with `L'.smul_mem _ (hf x _)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `L'.add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `L'.smul_mem a hx`.
-/
theorem exists_common_smul_mem {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (P : Submonoid O) {L L' : Submodule O M} (hL : Submodule.FG L)
    (h : ∀ v ∈ L, ∃ s ∈ P, s • v ∈ L') : ∃ s ∈ P, ∀ v ∈ L, s • v ∈ L' := by
  classical
  obtain ⟨S, rfl⟩ := hL
  choose f hfP hf using h
  let g : S → O := fun x => f x (Submodule.subset_span x.2)
  refine ⟨∏ x : S, g x, P.prod_mem (fun x _ => hfP _ _), ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    have hx' : x ∈ S := hx
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]
    exact L'.smul_mem _ (hf x _)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L'.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L'.smul_mem a hx

end GlobalTheory.CommonSmulMembership
