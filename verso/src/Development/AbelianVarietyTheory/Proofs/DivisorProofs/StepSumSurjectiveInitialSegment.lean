import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Set `w : ℕ → ℝ` to `fun n => if h : n < r then v ⟨n, h⟩ else 0`. Use `⟨fun k => w k.val - w (k.val + 1), ?_⟩` and prove the remaining obligations. Establish `key : ∀ d : ℕ, ∀ i : Fin r, r - i.val = d → stepSum S (fun k => w k.val - w (k.val + 1)) i = v i`. Introduce `d`. Proceed by induction on `d with`.

Consider the case `zero => intro i hi`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Consider the case `succ d ih`. Introduce `i hi`.

Unfold `stepSum`. Distinguish the cases in `hiS : i ∈ S`. Distinguish the cases in `h : i.val + 1 < r`. Use `set j : Fin r := ⟨i.val + 1, h⟩ with hj`. Establish `hset : S.filter (fun k => i ≤ k) = insert i (S.filter (fun k => j ≤ k))`.

Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_insert, Fin.le_def, hj, Fin.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hk, hik⟩`. Distinguish the cases in `hki : k.val = i.val`.

Conclude with `Or.inl hki`. Conclude with `Or.inr ⟨hk, by omega⟩`. Introduce and unpack `(hki | ⟨hk, hjk⟩)`. Establish `: k = i` using `Fin.ext hki`. Substitute `this` using the available equality.

Conclude with `⟨hiS, le_refl _⟩`. Conclude with `⟨hk, by omega⟩`. Establish `hnot : i ∉ S.filter (fun k => j ≤ k)`. Simplify using `[Fin.le_def, hj]`. Establish `hj'` using `ih j (by simp [hj]; omega)`.

Unfold `stepSum at hj'`. Rewrite using `[hset, Finset.sum_insert hnot, hj']`. Simplify using `only [w, dif_pos i.2, dif_pos h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hset : S.filter (fun k => i ≤ k) = {i}`.

Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_singleton, Fin.le_def]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hk, hik⟩; exact Fin.ext (by have := k.2; omega)`. Introduce and unpack `rfl`.

Conclude with `⟨hiS, le_refl _⟩`. Rewrite using `[hset, Finset.sum_singleton]`. Simplify using `only [w, dif_pos i.2, dif_neg h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hv i hiS]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_filter]`. Conclude with `absurd (hS k hk.1 i hk.2) hiS`. Use function extensionality and compare the values at `i`.

Conclude with `key _ i rfl`.
-/
theorem stepSum_surj_of_initial {r : ℕ} {S : Finset (Fin r)} (hS : ∀ k ∈ S, ∀ i, i ≤ k → i ∈ S)
    (v : Fin r → ℝ) (hv : ∀ i ∉ S, v i = 0) : ∃ u, stepSum S u = v := by
  classical
  let w : ℕ → ℝ := fun n => if h : n < r then v ⟨n, h⟩ else 0
  refine ⟨fun k => w k.val - w (k.val + 1), ?_⟩
  have key : ∀ d : ℕ, ∀ i : Fin r, r - i.val = d → stepSum S (fun k => w k.val - w (k.val + 1)) i = v i := by
    intro d
    induction d with
    | zero => intro i hi; have := i.2; omega
    | succ d ih =>
      intro i hi
      unfold stepSum
      by_cases hiS : i ∈ S
      · by_cases h : i.val + 1 < r
        · set j : Fin r := ⟨i.val + 1, h⟩ with hj
          have hset : S.filter (fun k => i ≤ k) = insert i (S.filter (fun k => j ≤ k)) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_insert, Fin.le_def, hj, Fin.ext_iff]
            constructor
            · rintro ⟨hk, hik⟩
              by_cases hki : k.val = i.val
              · exact Or.inl hki
              · exact Or.inr ⟨hk, by omega⟩
            · rintro (hki | ⟨hk, hjk⟩)
              · have : k = i := Fin.ext hki
                subst this; exact ⟨hiS, le_refl _⟩
              · exact ⟨hk, by omega⟩
          have hnot : i ∉ S.filter (fun k => j ≤ k) := by
            simp [Fin.le_def, hj]
          have hj' := ih j (by simp [hj]; omega)
          unfold stepSum at hj'
          rw [hset, Finset.sum_insert hnot, hj']
          simp only [w, dif_pos i.2, dif_pos h]
          ring
        · have hset : S.filter (fun k => i ≤ k) = {i} := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_singleton, Fin.le_def]
            constructor
            · rintro ⟨hk, hik⟩; exact Fin.ext (by have := k.2; omega)
            · rintro rfl; exact ⟨hiS, le_refl _⟩
          rw [hset, Finset.sum_singleton]
          simp only [w, dif_pos i.2, dif_neg h]
          ring
      · rw [hv i hiS]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        exact absurd (hS k hk.1 i hk.2) hiS
  funext i
  exact key _ i rfl

end GlobalTheory
