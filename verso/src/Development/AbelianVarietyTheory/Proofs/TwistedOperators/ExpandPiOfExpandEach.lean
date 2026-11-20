import Mathlib

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `hm : ∃ i, m i = 0`. Take `⟨i0, hi0⟩` from `hm`. Establish `h1 : f g = 0`. Rewrite using `[hf i0 g hg]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `j _`. Conclude with `absurd j.2 (by omega)`. Use `haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩`. Rewrite using `[h1, Finset.univ_eq_empty, Finset.sum_empty]`. Use `push_neg at hm`.

Set `j0 : ∀ i, Fin (m i)` to `fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩`. Set `T : Finset ι → ∀ i, Finset (Fin (m i))` to `fun s i => if i ∈ s then Finset.univ else {j0 i}`. Set `H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i)` to `fun s J g i => if i ∈ s then k i (J i) else g i`. Establish `hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i`. Introduce `s J`.

Rewrite using `[Fintype.mem_piFinset]`. Apply `forall_congr'` to reduce the goal to its premises. Introduce `i`. Apply the tactic sequence `by_cases hi : i ∈ s <;> simp [T, hi]`. Establish `key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) → f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `g hg`. Establish `hT : T ∅ = fun i => {j0 i}` using `by funext i; simp [T]`.

Rewrite using `[hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]`. Use `congr 1`. Consider the case `insert a s ha ih`. Introduce `g hg`. Establish `hHK : ∀ J, ∀ i, H s J g i ∈ K i`.

Introduce `J i`. Simplify using `only [H]`. Use `split_ifs`. Use `exacts [hk _ _, hg i]`. Rewrite using `[ih g hg]`.

Establish `step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) = ∑ j, f (H (insert a s) (Function.update J a j) g) * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i)`. Introduce `J _`. Rewrite using `[hf a _ (hHK J), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using `[H]`. Simplify using `[H, Function.update_of_ne hia, Finset.mem_insert, hia]`.

Establish `e2 : H s J g a = g a` using `by simp [H, ha]`. Rewrite using `[e1, e2, Finset.prod_insert ha, Function.update_self]`. Establish `e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i)`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `: i ≠ a` using `fun h => ha (h ▸ hi)`.

Rewrite using `[Function.update_of_ne this]`. Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl step, ← Finset.sum_product']`. Use `Finset.sum_nbij' (fun p => Function.update p.1 a p.2) (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `⟨J, j⟩ hp`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp`. Simplify using `only [Finset.mem_coe, hmem]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_insert, not_or]`.

Rewrite using `[Function.update_of_ne hi.1]`. Conclude with `hp.1 i hi.2`. Introduce `J' hJ'`. Simplify using `only [Finset.mem_coe, hmem] at hJ'`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true, hmem]`.

Introduce `i hi`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hia]`.

Conclude with `hJ' i (by simp [hia, hi])`. Introduce and unpack `⟨J, j⟩ hp`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp`. Simplify using `only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `(hp.1 _ ha).symm`. Rewrite using `[Function.update_of_ne hia]`.

Introduce `J' _`. Simplify using `only [Function.update_idem, Function.update_eq_self]`. Introduce and unpack `⟨J, j⟩ _`. Both sides reduce to the same expression. Rewrite using `[key Finset.univ g hg]`.

Establish `hTu : T Finset.univ = fun _ => Finset.univ` using `by funext i; simp [T]`. Rewrite using `[hTu, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `[H]`.
-/
theorem expand_pi_of_expand_each {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i) :
    f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  classical
  by_cases hm : ∃ i, m i = 0
  · obtain ⟨i0, hi0⟩ := hm
    have h1 : f g = 0 := by
      rw [hf i0 g hg]
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩
    rw [h1, Finset.univ_eq_empty, Finset.sum_empty]
  push_neg at hm
  let j0 : ∀ i, Fin (m i) := fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩
  let T : Finset ι → ∀ i, Finset (Fin (m i)) := fun s i => if i ∈ s then Finset.univ else {j0 i}
  let H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i) :=
    fun s J g i => if i ∈ s then k i (J i) else g i
  have hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i := by
    intro s J
    rw [Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [T, hi]
  have key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) →
      f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hT : T ∅ = fun i => {j0 i} := by funext i; simp [T]
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]
      congr 1
    | insert a s ha ih =>
      intro g hg
      have hHK : ∀ J, ∀ i, H s J g i ∈ K i := by
        intro J i
        simp only [H]
        split_ifs
        exacts [hk _ _, hg i]
      rw [ih g hg]
      have step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)
          = ∑ j, f (H (insert a s) (Function.update J a j) g)
              * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i) := by
        intro J _
        rw [hf a _ (hHK J), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g := by
          funext i
          by_cases hia : i = a
          · subst hia
            simp [H]
          · simp [H, Function.update_of_ne hia, Finset.mem_insert, hia]
        have e2 : H s J g a = g a := by simp [H, ha]
        rw [e1, e2, Finset.prod_insert ha, Function.update_self]
        have e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne this]
        rw [e3]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_nbij' (fun p => Function.update p.1 a p.2)
        (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Finset.mem_coe, hmem]
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        rw [Function.update_of_ne hi.1]
        exact hp.1 i hi.2
      · intro J' hJ'
        simp only [Finset.mem_coe, hmem] at hJ'
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
          Finset.mem_univ, and_true, hmem]
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · rw [Function.update_of_ne hia]
          exact hJ' i (by simp [hia, hi])
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
        funext i
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact (hp.1 _ ha).symm
        · rw [Function.update_of_ne hia]
      · intro J' _
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨J, j⟩ _
        rfl
  rw [key Finset.univ g hg]
  have hTu : T Finset.univ = fun _ => Finset.univ := by funext i; simp [T]
  rw [hTu, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 2
  funext i
  simp [H]

end GlobalTheory
