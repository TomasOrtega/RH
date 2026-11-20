import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ n ρ κ hn hρ a ha V hV hT hU`. Establish `hsc : ∀ (i : Fin n) (c : k), c ≠ 0 → Pi.single i c ∈ V → Pi.single i (1 : k) ∈ V`. Introduce `i c hc h`. Establish `e : c⁻¹ • Pi.single i c = Pi.single i (1 : k)`. Apply the tactic sequence `ext j; by_cases hj : j = i <;> simp [hj, hc]`.

Rewrite using `[← e]`. Conclude with `V.smul_mem _ h`. Set `i0 : Fin n` to `⟨0, by omega⟩`. Establish `h0 : Pi.single i0 (1 : k) ∈ V`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hV`.

Distinguish the cases in `hex : ∃ j : Fin n, 0 < j.val ∧ w j ≠ 0`. Take `⟨j, hj, hwj⟩` from `hex`. Conclude with `hsc i0 (w j) hwj (hU i0 j (Fin.lt_def.2 hj) (by simp [i0]; omega) w hw)`. Use `push_neg at hex`. Establish `hwe : w = Pi.single i0 (w i0)`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i0`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Establish `: 0 < j.val`.

Break down `Nat.eq_zero_or_pos j.val with h | h` into its components or cases. Conclude with `absurd (Fin.ext h) hj`. Conclude with `h`. Rewrite using `[hex j this, Pi.single_eq_of_ne hj]`. Establish `hne : w i0 ≠ 0` using `fun h => hw0 (by rw [hwe, h, Pi.single_zero])`.

Conclude with `hsc i0 _ hne (hwe ▸ hw)`. Establish `hstep : ∀ x y : Fin n, symEdge ρ κ x y → (∀ j : Fin n, symEdge ρ κ x j → j = y) → Pi.single x (1 : k) ∈ V → Pi.single y (1 : k) ∈ V`. Introduce `x y hxy huniq hx`. Use `hsc y (a x y) (ha x y hxy) ?_` and prove the remaining obligations. Establish `hu` using `hT _ hx`.

Use `hu using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_eq_single x]`. Distinguish the cases in `hj : j = y`. Substitute `hj` using the available equality.

Simplify using `[hxy]`. Establish `: ¬ symEdge ρ κ x j` using `fun h => hj (huniq j h)`. Simplify using `[this, Pi.single_eq_of_ne hj]`. Introduce `i _ hi`. Simplify using `[Pi.single_eq_of_ne hi]`.

Simplify using the standard rewrite rules. Establish `hwalk : ∀ t, t ≤ 2 * ρ → ∀ x : Fin n, x.val = (if t < ρ then t else t + κ) → Pi.single x (1 : k) ∈ V`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`.

Introduce `_ x hx`. Apply the tactic sequence `have : x = i0 := Fin.ext (by simp [i0] at hx ⊢; split_ifs at hx <;> omega)`. Rewrite using `[this]`. Conclude with `h0`. Consider the case `succ t ih`.

Introduce `ht y hy`. Apply the tactic sequence `have hxlt : (if t < ρ then t else t + κ) < n := by split_ifs <;> omega`. Set `x : Fin n` to `⟨_, hxlt⟩`. Use `hstep x y ?_ ?_ (ih (by omega) x rfl)` and prove the remaining obligations. Unfold `symEdge`.

Simplify using `only [x]`. Apply the tactic sequence `split_ifs at hy ⊢ <;> omega`. Introduce `j hj`. Apply `Fin.ext` to reduce the goal to its premises. Unfold `symEdge at hj`.

Simplify using `only [x] at hj`. Apply the tactic sequence `split_ifs at hy hj <;> omega`. Set `last : Fin n` to `⟨2 * ρ + κ, by omega⟩`. Establish `hlast : Pi.single last (1 : k) ∈ V` using `hwalk (2 * ρ) le_rfl last (by simp [last]; omega)`. Establish `hall : ∀ i : Fin n, Pi.single i (1 : k) ∈ V`.

Introduce `i`. Distinguish the cases in `hi : i = last`. Rewrite using `[hi]`. Conclude with `hlast`. Establish `hlt : i < last`.

Rewrite using `[Fin.lt_def]`. Use `i.2` as an intermediate fact. Establish `: i.val ≠ 2 * ρ + κ` using `fun h => hi (Fin.ext h)`. Simplify using `[last]`. Use linear arithmetic over natural numbers and integers.

Use `hU i last hlt (by simp [last]; omega) _ hlast` as an intermediate fact. Simplify using `using this`. Rewrite using `[eq_top_iff, ← (Pi.basisFun k (Fin n)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[Pi.basisFun_apply]`.

Conclude with `hall i`.
-/
theorem symEdge_span_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  intro k _ n ρ κ hn hρ a ha V hV hT hU
  have hsc : ∀ (i : Fin n) (c : k), c ≠ 0 → Pi.single i c ∈ V → Pi.single i (1 : k) ∈ V := by
    intro i c hc h
    have e : c⁻¹ • Pi.single i c = Pi.single i (1 : k) := by
      ext j; by_cases hj : j = i <;> simp [hj, hc]
    rw [← e]; exact V.smul_mem _ h
  let i0 : Fin n := ⟨0, by omega⟩
  have h0 : Pi.single i0 (1 : k) ∈ V := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    by_cases hex : ∃ j : Fin n, 0 < j.val ∧ w j ≠ 0
    · obtain ⟨j, hj, hwj⟩ := hex
      exact hsc i0 (w j) hwj (hU i0 j (Fin.lt_def.2 hj) (by simp [i0]; omega) w hw)
    · push_neg at hex
      have hwe : w = Pi.single i0 (w i0) := by
        funext j
        by_cases hj : j = i0
        · subst hj; simp
        · have : 0 < j.val := by
            rcases Nat.eq_zero_or_pos j.val with h | h
            · exact absurd (Fin.ext h) hj
            · exact h
          rw [hex j this, Pi.single_eq_of_ne hj]
      have hne : w i0 ≠ 0 := fun h => hw0 (by rw [hwe, h, Pi.single_zero])
      exact hsc i0 _ hne (hwe ▸ hw)
  have hstep : ∀ x y : Fin n, symEdge ρ κ x y → (∀ j : Fin n, symEdge ρ κ x j → j = y) →
      Pi.single x (1 : k) ∈ V → Pi.single y (1 : k) ∈ V := by
    intro x y hxy huniq hx
    refine hsc y (a x y) (ha x y hxy) ?_
    have hu := hT _ hx
    convert hu using 1
    funext j
    rw [Finset.sum_eq_single x]
    · by_cases hj : j = y
      · subst hj; simp [hxy]
      · have : ¬ symEdge ρ κ x j := fun h => hj (huniq j h)
        simp [this, Pi.single_eq_of_ne hj]
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  have hwalk : ∀ t, t ≤ 2 * ρ → ∀ x : Fin n, x.val = (if t < ρ then t else t + κ) → Pi.single x (1 : k) ∈ V := by
    intro t
    induction t with
    | zero =>
      intro _ x hx
      have : x = i0 := Fin.ext (by simp [i0] at hx ⊢; split_ifs at hx <;> omega)
      rw [this]; exact h0
    | succ t ih =>
      intro ht y hy
      have hxlt : (if t < ρ then t else t + κ) < n := by split_ifs <;> omega
      let x : Fin n := ⟨_, hxlt⟩
      refine hstep x y ?_ ?_ (ih (by omega) x rfl)
      · unfold symEdge
        simp only [x]
        split_ifs at hy ⊢ <;> omega
      · intro j hj
        apply Fin.ext
        unfold symEdge at hj
        simp only [x] at hj
        split_ifs at hy hj <;> omega
  let last : Fin n := ⟨2 * ρ + κ, by omega⟩
  have hlast : Pi.single last (1 : k) ∈ V := hwalk (2 * ρ) le_rfl last (by simp [last]; omega)
  have hall : ∀ i : Fin n, Pi.single i (1 : k) ∈ V := by
    intro i
    by_cases hi : i = last
    · rw [hi]; exact hlast
    · have hlt : i < last := by
        rw [Fin.lt_def]; have := i.2; have : i.val ≠ 2 * ρ + κ := fun h => hi (Fin.ext h); simp [last]; omega
      have := hU i last hlt (by simp [last]; omega) _ hlast
      simpa using this
  rw [eq_top_iff, ← (Pi.basisFun k (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact hall i

end GlobalTheory
