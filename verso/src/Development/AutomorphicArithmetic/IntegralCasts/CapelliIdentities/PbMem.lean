import Mathlib

namespace UpperTheory.Reformulated.B.Qi43

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite `hx` using `[Subgroup.sup_eq_closure]`. Proceed by induction on `hx using Subgroup.closure_induction with`. Consider the case `mem y hy`.

Break down `hy with hy | hy` into its components or cases. Conclude with `⟨y, hy, 1, K.one_mem, by simp⟩`. Take `⟨k, hk, rfl⟩` from `Subgroup.mem_map.mp hy`. Conclude with `⟨1, UQ.one_mem, k, hk, by simp⟩`. Consider the case `one => exact ⟨1, UQ.one_mem, 1, K.one_mem, by simp⟩`.

Consider the case `mul y z _ _ hy hz`. Take `⟨u, hu, k, hk, rfl⟩` from `hy`. Take `⟨v, hv, l, hl, rfl⟩` from `hz`. Use `⟨u * v, UQ.mul_mem hu hv, k * l, K.mul_mem hk hl, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc, ← mul_assoc (J k), ← (hc v hv k).eq]`.

Simplify using `only [mul_assoc]`. Consider the case `inv y _ hy`. Take `⟨u, hu, k, hk, rfl⟩` from `hy`. Use `⟨u⁻¹, UQ.inv_mem hu, k⁻¹, K.inv_mem hk, ?_⟩` and prove the remaining obligations. Rewrite using `[(hc u hu k).eq, mul_inv_rev, map_inv]`.

Introduce and unpack `⟨u, hu, k, hk, rfl⟩`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem J hk))`.
-/
theorem pb_mem {B C : Type} [Group B] [Group C] (J : B →* C) (UQ : Subgroup C)
    (hc : ∀ u ∈ UQ, ∀ g : B, Commute u (J g)) (K : Subgroup B) (x : C) :
    x ∈ UQ ⊔ Subgroup.map J K ↔ ∃ u ∈ UQ, ∃ k ∈ K, x = u * J k := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨1, UQ.one_mem, k, hk, by simp⟩
    | one => exact ⟨1, UQ.one_mem, 1, K.one_mem, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      obtain ⟨v, hv, l, hl, rfl⟩ := hz
      refine ⟨u * v, UQ.mul_mem hu hv, k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc (J k), ← (hc v hv k).eq]
      simp only [mul_assoc]
    | inv y _ hy =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      refine ⟨u⁻¹, UQ.inv_mem hu, k⁻¹, K.inv_mem hk, ?_⟩
      rw [(hc u hu k).eq, mul_inv_rev, map_inv]
  · rintro ⟨u, hu, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem J hk))

end UpperTheory.Reformulated.B.Qi43
