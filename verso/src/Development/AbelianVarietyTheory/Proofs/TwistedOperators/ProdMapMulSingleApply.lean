import Mathlib

universe u_1 u_2

namespace GlobalTheory.ProdMapMulSingle

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Take `⟨ha, hl'⟩` from `List.nodup_cons.mp hl`. Rewrite using `[List.map_cons, List.prod_cons, Pi.mul_apply, ih hl']`.

Distinguish the cases in `h : w = a`. Substitute `h` using the available equality. Rewrite using `[if_neg ha, if_pos List.mem_cons_self, Pi.mulSingle_eq_same, mul_one]`. Rewrite using `[Pi.mulSingle_eq_of_ne h, one_mul]`. Simplify using `only [List.mem_cons, h, false_or]`.
-/
theorem prod_map_mulSingle_apply {ι : Type u_1} [DecidableEq ι] {M : ι → Type u_2}
    [(i : ι) → Monoid (M i)] (x : (i : ι) → M i) (l : List ι) (hl : List.Nodup l) (w : ι) :
    List.prod (List.map (fun (i : ι) ↦ Pi.mulSingle i (x i)) l) w
      = if w ∈ l then x w else (1 : M w) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl']
    by_cases h : w = a
    · subst h
      rw [if_neg ha, if_pos List.mem_cons_self, Pi.mulSingle_eq_same, mul_one]
    · rw [Pi.mulSingle_eq_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

end GlobalTheory.ProdMapMulSingle
