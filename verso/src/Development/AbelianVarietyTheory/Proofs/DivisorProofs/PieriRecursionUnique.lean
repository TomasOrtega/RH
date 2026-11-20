import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Establish `main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s → n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0`. Introduce `s`. Use `Nat.strong_induction_on s ?_` and prove the remaining obligations. Introduce `s ihs k`. Use `Nat.strong_induction_on k ?_` and prove the remaining obligations.

Introduce `k ihk μ hs hk`. Distinguish the cases in `hμ : Antitone μ`. Use `swap`. Conclude with `hD μ hμ`. Distinguish the cases in `hz : μ = 0`.

Substitute `hz` using the available equality. Conclude with `h0`. Use `set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0`. Use `set l : Fin n → ℕ := fun i => μ i - 1 with hl`. Establish `hla : Antitone l` using `fun a b hab => Nat.sub_le_sub_right (hμ hab) 1`.

Establish `hj : J0.card ≤ n` using `by simpa using Finset.card_le_univ J0`. Establish `hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]`. Apply the tactic sequence `split_ifs with h <;> omega`.

Establish `hsum : ∀ J : Finset (Fin n), ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card`. Introduce `J`. Simplify using `[Finset.sum_add_distrib, Finset.sum_boole]`. Establish `hDl : D l = 0`. Establish `hlt : ∑ i, l i < s`.

Rewrite using `[← hs]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hz (funext h)`.

Conclude with `Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _) ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩`. Conclude with `ihs _ hlt _ l rfl rfl`. Establish `hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card), D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0))`. Use `Finset.sum_eq_single_of_mem J0 (by simp) ?_` and prove the remaining obligations. Introduce `J hJ hne`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ`. Use `set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν`. Distinguish the cases in `hνa : Antitone ν`. Use `swap`. Conclude with `hD ν hνa`.

Establish `hnsub : ¬ J ⊆ J0` using `fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))`. Take `⟨i, hiJ, hiJ0⟩` from `Finset.not_subset.mp hnsub`. Establish `hμi : μ i = 0` using `by simpa [hJ0] using hiJ0`. Establish `hνi : 1 ≤ ν i` using `by simp [hν, hiJ]`. Establish `hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0)`.

Introduce `k hk`. Rewrite `hk` using `[Finset.mem_insert]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Break down `hk with rfl | hk` into its components or cases. Use linear arithmetic over natural numbers and integers.

Establish `hk' : μ k ≠ 0` using `by simpa [hJ0] using hk`. Establish `hki : k ≤ i`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `hμ h.le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `hνa hki` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hcard` using `Finset.card_le_card hsub`. Rewrite `hcard` using `[Finset.card_insert_of_notMem hiJ0]`.

Establish `hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n`. Simplify using `using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))`. Use `ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hsum J`.

Establish `h2` using `hsum J0`. Rewrite `h2` using `[hlμ]`. Rewrite using `[hν, h1, hJ, ← h2, hs]`. Establish `hrec` using `hr l hla J0.card hj`. Rewrite `hrec` using `[hsingle, hDl, mul_zero, hlμ]`.

Conclude with `hrec`. Introduce `μ`. Conclude with `main _ _ μ rfl rfl`.
-/
theorem pieri_recursion_zero (n : ℕ) (c : ℕ → ℂ) (D : (Fin n → ℕ) → ℂ)
    (hD : ∀ l, ¬ Antitone l → D l = 0)
    (hr : ∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), D (l + (fun i => if i ∈ J then 1 else 0)) = c j * D l)
    (h0 : D 0 = 0) : ∀ μ, D μ = 0 := by
  have main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s →
      n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0 := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ihs k
    refine Nat.strong_induction_on k ?_
    intro k ihk μ hs hk
    by_cases hμ : Antitone μ
    swap
    · exact hD μ hμ
    by_cases hz : μ = 0
    · subst hz; exact h0
    set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0
    set l : Fin n → ℕ := fun i => μ i - 1 with hl
    have hla : Antitone l := fun a b hab => Nat.sub_le_sub_right (hμ hab) 1
    have hj : J0.card ≤ n := by simpa using Finset.card_le_univ J0
    have hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ := by
      funext i
      simp only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> omega
    have hsum : ∀ J : Finset (Fin n),
        ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card := by
      intro J
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    have hDl : D l = 0 := by
      have hlt : ∑ i, l i < s := by
        rw [← hs]
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (funext h)
        exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _)
          ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩
      exact ihs _ hlt _ l rfl rfl
    have hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card),
        D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0)) := by
      refine Finset.sum_eq_single_of_mem J0 (by simp) ?_
      intro J hJ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν
      by_cases hνa : Antitone ν
      swap
      · exact hD ν hνa
      have hnsub : ¬ J ⊆ J0 := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
      obtain ⟨i, hiJ, hiJ0⟩ := Finset.not_subset.mp hnsub
      have hμi : μ i = 0 := by simpa [hJ0] using hiJ0
      have hνi : 1 ≤ ν i := by simp [hν, hiJ]
      have hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hk with rfl | hk
        · omega
        · have hk' : μ k ≠ 0 := by simpa [hJ0] using hk
          have hki : k ≤ i := by
            by_contra h
            push_neg at h
            have := hμ h.le
            omega
          have := hνa hki
          omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hiJ0] at hcard
      have hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))
      refine ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl
      · omega
      · have h1 := hsum J
        have h2 := hsum J0
        rw [hlμ] at h2
        rw [hν, h1, hJ, ← h2, hs]
    have hrec := hr l hla J0.card hj
    rw [hsingle, hDl, mul_zero, hlμ] at hrec
    exact hrec
  intro μ
  exact main _ _ μ rfl rfl

/- English proof (translation)
Introduce `n c V U hV hU hrV hrU h0`. Establish `h` using `pieri_recursion_zero n c (fun l => V l - U l) (fun l hl => by simp [hV l hl, hU l hl]) (fun l hl j hj => by`. Simplify using `only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])`. Use the proof step `(by simp [h0])`. Use function extensionality and compare the values at `μ`.

Conclude with `sub_eq_zero.mp (h μ)`.
-/
theorem pieri_recursion_unique : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ),
    (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) →
    V 0 = U 0 → V = U := by
  intro n c V U hV hU hrV hrU h0
  have h := pieri_recursion_zero n c (fun l => V l - U l)
    (fun l hl => by simp [hV l hl, hU l hl])
    (fun l hl j hj => by
      simp only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])
    (by simp [h0])
  funext μ
  exact sub_eq_zero.mp (h μ)

end GlobalTheory
