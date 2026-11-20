import Mathlib

open Finset

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on_max_value lv with`. Consider the case `empty`. Introduce `_ T _ hT`. Establish `: T.card ≤ 1` using `Finset.card_le_one.2 fun x hx y hy => hT x hx y hy (by simp)`. Simplify using `using this`.

Consider the case `insert a s ha hmax ih`. Introduce `hp T hTS hT`. Establish `hps : ∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) → (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b`. Introduce `b hb T' h1 h2 h3`. Use `hp b (mem_insert_of_mem hb) T' h1 ?_ h3` and prove the remaining obligations.

Introduce `x hx y hy b' hb' hlt`. Break down `mem_insert.1 hb' with rfl | hb'` into its components or cases. Conclude with `absurd (hmax b hb) (by omega)`. Conclude with `h2 x hx y hy b' hb' hlt`. Establish `hBa : 0 ≤ B a`.

Simplify using `using hp a (mem_insert_self _ _) ∅ (by simp) (by simp) (by simp)`. Rewrite using `[prod_insert ha]`. Break down `T.eq_empty_or_nonempty with rfl | ⟨x0, -⟩` into its components or cases. Use `ih hps ∅ (by simp) (by simp)` as an intermediate fact. Simplify using `only [card_empty, Nat.cast_zero] at this ⊢`.

Check the signs of the components of the expression. Use `haveI : Nonempty α := ⟨x0⟩`. Set `q : α → Set α` to `fun x => {y | ∀ b ∈ s, r b x y}`. Establish `hq : ∀ x y, q x = q y ↔ ∀ b ∈ s, r b x y`. Introduce `x y`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: y ∈ q y` using `fun b _ => (hr b).refl y`. Rewrite `this` using `[← h]`. Conclude with `this`.

Introduce `h`. Use extensionality with `z`. Conclude with `⟨fun hz b hb => (hr b).trans ((hr b).symm (h b hb)) (hz b hb), fun hz b hb => (hr b).trans (h b hb) (hz b hb)⟩`. Set `ρ : α → α` to `fun x => Function.invFunOn q (↑T : Set α) (q x)`. Establish `hρ : ∀ x ∈ T, ρ x ∈ T ∧ q (ρ x) = q x` using `fun x hx => Function.invFunOn_pos (f := q) (s := (↑T : Set α)) ⟨x, hx, rfl⟩`.

Establish `him : ((T.image ρ).card : ℝ) ≤ ∏ b ∈ s, B b`. Use `ih hps _ ?_ ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨x, hx, rfl⟩` from `mem_image.1 (mem_coe.1 hz)`. Conclude with `hTS (hρ x hx).1`.

Introduce `z hz w hw h`. Take `⟨x, hx, rfl⟩` from `mem_image.1 hz`. Take `⟨y, hy, rfl⟩` from `mem_image.1 hw`. Establish `h'` using `(hq _ _).2 h`. Rewrite `h'` using `[(hρ x hx).2, (hρ y hy).2]`.

Simplify using `only [ρ, h']`. Establish `hfib : ∀ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ) ≤ B a`. Introduce `z _`. Establish `key : ∀ x ∈ T.filter (fun x => ρ x = z), ∀ y ∈ T.filter (fun x => ρ x = z), ∀ b ∈ s, r b x y`. Introduce `x hx y hy`.

Take `⟨hx, hx'⟩` from `mem_filter.1 hx`. Take `⟨hy, hy'⟩` from `mem_filter.1 hy`. Rewrite using `[← hq, ← (hρ x hx).2, ← (hρ y hy).2, hx', hy']`. Use `hp a (mem_insert_self _ _) _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Conclude with `hTS (mem_filter.1 (mem_coe.1 hx)).1`. Introduce `x hx y hy b' hb' hlt`. Break down `mem_insert.1 hb' with rfl | hb'` into its components or cases. Conclude with `absurd hlt (lt_irrefl _)`. Conclude with `key x hx y hy b' hb'`.

Introduce `x hx y hy h`. Use `hT x (mem_filter.1 hx).1 y (mem_filter.1 hy).1 ?_` and prove the remaining obligations. Introduce `b hb`. Break down `mem_insert.1 hb with rfl | hb` into its components or cases. Conclude with `h`.

Conclude with `key x hx y hy b hb`. Rewrite using `[Finset.card_eq_sum_card_image ρ T]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le_prod_of_separated_levels {α β : Type} (S : Set α) (lv : β → ℕ)
    (r : β → α → α → Prop) (B : β → ℝ) (hr : ∀ b, Equivalence (r b)) (s : Finset β) :
    (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
      (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
      (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) →
    ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, (∀ b ∈ s, r b x y) → x = y) →
      (T.card : ℝ) ≤ ∏ b ∈ s, B b := by
  classical
  induction s using Finset.induction_on_max_value lv with
  | empty =>
    intro _ T _ hT
    have : T.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => hT x hx y hy (by simp)
    simpa using this
  | insert a s ha hmax ih =>
    intro hp T hTS hT
    have hps : ∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
        (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
        (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b := by
      intro b hb T' h1 h2 h3
      refine hp b (mem_insert_of_mem hb) T' h1 ?_ h3
      intro x hx y hy b' hb' hlt
      rcases mem_insert.1 hb' with rfl | hb'
      · exact absurd (hmax b hb) (by omega)
      · exact h2 x hx y hy b' hb' hlt
    have hBa : 0 ≤ B a := by
      simpa using hp a (mem_insert_self _ _) ∅ (by simp) (by simp) (by simp)
    rw [prod_insert ha]
    rcases T.eq_empty_or_nonempty with rfl | ⟨x0, -⟩
    · have := ih hps ∅ (by simp) (by simp)
      simp only [card_empty, Nat.cast_zero] at this ⊢
      positivity
    haveI : Nonempty α := ⟨x0⟩
    let q : α → Set α := fun x => {y | ∀ b ∈ s, r b x y}
    have hq : ∀ x y, q x = q y ↔ ∀ b ∈ s, r b x y := by
      intro x y
      constructor
      · intro h
        have : y ∈ q y := fun b _ => (hr b).refl y
        rw [← h] at this
        exact this
      · intro h
        ext z
        exact ⟨fun hz b hb => (hr b).trans ((hr b).symm (h b hb)) (hz b hb),
          fun hz b hb => (hr b).trans (h b hb) (hz b hb)⟩
    let ρ : α → α := fun x => Function.invFunOn q (↑T : Set α) (q x)
    have hρ : ∀ x ∈ T, ρ x ∈ T ∧ q (ρ x) = q x := fun x hx =>
      Function.invFunOn_pos (f := q) (s := (↑T : Set α)) ⟨x, hx, rfl⟩
    have him : ((T.image ρ).card : ℝ) ≤ ∏ b ∈ s, B b := by
      refine ih hps _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hz)
        exact hTS (hρ x hx).1
      · intro z hz w hw h
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
        obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
        have h' := (hq _ _).2 h
        rw [(hρ x hx).2, (hρ y hy).2] at h'
        simp only [ρ, h']
    have hfib : ∀ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ) ≤ B a := by
      intro z _
      have key : ∀ x ∈ T.filter (fun x => ρ x = z), ∀ y ∈ T.filter (fun x => ρ x = z),
          ∀ b ∈ s, r b x y := by
        intro x hx y hy
        obtain ⟨hx, hx'⟩ := mem_filter.1 hx
        obtain ⟨hy, hy'⟩ := mem_filter.1 hy
        rw [← hq, ← (hρ x hx).2, ← (hρ y hy).2, hx', hy']
      refine hp a (mem_insert_self _ _) _ ?_ ?_ ?_
      · intro x hx
        exact hTS (mem_filter.1 (mem_coe.1 hx)).1
      · intro x hx y hy b' hb' hlt
        rcases mem_insert.1 hb' with rfl | hb'
        · exact absurd hlt (lt_irrefl _)
        · exact key x hx y hy b' hb'
      · intro x hx y hy h
        refine hT x (mem_filter.1 hx).1 y (mem_filter.1 hy).1 ?_
        intro b hb
        rcases mem_insert.1 hb with rfl | hb
        · exact h
        · exact key x hx y hy b hb
    rw [Finset.card_eq_sum_card_image ρ T]
    push_cast
    calc ∑ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ)
        ≤ ∑ _z ∈ T.image ρ, B a := sum_le_sum hfib
      _ = B a * ((T.image ρ).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ B a * ∏ b ∈ s, B b := mul_le_mul_of_nonneg_left him hBa

/- English proof (translation)
Introduce `α β S s lv r B hr hinj hp`. Establish `h : ∀ T : Finset α, (↑T : Set α) ⊆ S → (T.card : ℝ) ≤ ∏ b ∈ s, B b` using `fun T hT => card_le_prod_of_separated_levels S lv r B hr s hp T hT fun x hx y hy => hinj x (hT hx) y (hT hy)`. Establish `hS : S.Finite`. Assume the negation of the conclusion as `hinf`. Take `⟨n, hn⟩` from `exists_nat_gt (∏ b ∈ s, B b)`.

Take `⟨T, hT, hc⟩` from `Set.Infinite.exists_subset_card_eq hinf n`. Use `h T hT` as an intermediate fact. Rewrite `this` using `[hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hS, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.ncard_eq_toFinset_card S hS]`. Conclude with `h _ (by simp)`.
-/
theorem finite_and_ncard_le_prod_of_levels :
    ∀ (α β : Type) (S : Set α) (s : Finset β) (lv : β → ℕ) (r : β → α → α → Prop) (B : β → ℝ), (∀ b, Equivalence (r b)) → (∀ x ∈ S, ∀ y ∈ S, (∀ b ∈ s, r b x y) → x = y) → (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) → (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) → S.Finite ∧ ((S.ncard : ℕ) : ℝ) ≤ ∏ b ∈ s, B b := by
  intro α β S s lv r B hr hinj hp
  have h : ∀ T : Finset α, (↑T : Set α) ⊆ S → (T.card : ℝ) ≤ ∏ b ∈ s, B b := fun T hT =>
    card_le_prod_of_separated_levels S lv r B hr s hp T hT
      fun x hx y hy => hinj x (hT hx) y (hT hy)
  have hS : S.Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (∏ b ∈ s, B b)
    obtain ⟨T, hT, hc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := h T hT
    rw [hc] at this
    linarith
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hS]
  exact h _ (by simp)

end GlobalTheory
