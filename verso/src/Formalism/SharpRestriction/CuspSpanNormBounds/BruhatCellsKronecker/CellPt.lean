import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `σ τ hmap hinj hsurj hτ hP`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases.

Substitute `h0` using the available equality. Conclude with `⟨[], by simp, by simp, fun a ha => absurd ha (Nat.not_lt_zero a)⟩`. Take `⟨s, hs⟩ : ∃ s, s = σ 0 + 1` from `⟨_, rfl⟩`. Establish `hsn : s ≤ n` using `by have := hmap 0 hpos; omega`. Establish `hs1 : 1 ≤ s` using `by omega`.

Establish `c1 : ∀ i, i < s → σ i = s - 1 - i ∧ τ i = τ 0`. Introduce `i`. Proceed by induction on `i using Nat.strong_induction_on with`. Consider the case `_ i ihi`. Introduce `hi`.

Break down `Nat.eq_zero_or_pos i with hi0 | hipos` into its components or cases. Substitute `hi0` using the available equality. Conclude with `⟨by omega, rfl⟩`. Take `⟨i', rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Take `⟨e1, e2⟩` from `ihi i' (by omega) (by omega)`.

Take `⟨b, hbn, hb⟩` from `hsurj (s - 1 - (i' + 1)) (by omega)`. Establish `hbi : i' + 1 ≤ b`. Assume the negation of the conclusion as `hlt`. Use `(ihi b (by omega) (by omega)).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨f1, f2⟩` from `hP i' b (by omega) hbn (by omega)`. Substitute `f1` using the available equality. Conclude with `⟨hb, f2.trans e2⟩`. Establish `c2 : ∀ i, s ≤ i → i < n → s ≤ σ i`. Introduce `i hi hin`.

Assume the negation of the conclusion as `hlt`. Establish `hj : s - 1 - σ i < s` using `by omega`. Establish `e` using `(c1 (s - 1 - σ i) hj).1`. Use `hinj i hin (s - 1 - σ i) (by omega) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨bs, hb1, hb2, hb3⟩` from `ih (n - s) (by omega) (fun i => σ (i + s) - s) (fun i => τ (i + s)) (fun i hi => by`. Establish `h1` using `hmap (i + s) (by omega)`. Establish `h2` using `c2 (i + s) (by omega) (by omega)`. Use `show σ (i + s) - s < n - s`. Use the proof step `omega)`.

Use the proof step `(fun i hi j hj hij => by`. Establish `h1` using `c2 (i + s) (by omega) (by omega)`. Establish `h2` using `c2 (j + s) (by omega) (by omega)`. Establish `h3 : σ (i + s) - s = σ (j + s) - s` using `hij`. Use `hinj (i + s) (by omega) (j + s) (by omega) (by omega)` as an intermediate fact.

Use the proof step `omega)`. Use the proof step `(fun v hv => by`. Take `⟨i, hin, hi⟩` from `hsurj (v + s) (by omega)`. Establish `his : s ≤ i`. Assume the negation of the conclusion as `hlt`.

Use `(c1 i (by omega)).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨i - s, by omega, ?_⟩` and prove the remaining obligations. Use `show σ (i - s + s) - s = v`. Rewrite using `[Nat.sub_add_cancel his, hi]`.

Use the proof step `omega)`. Use the proof step `(fun i hi => hτ (i + s) (by omega))`. Use the proof step `(fun c b hcb hbn hv => by`. Establish `h1` using `c2 (c + s) (by omega) (by omega)`. Establish `h2` using `c2 (b + s) (by omega) (by omega)`.

Establish `h3 : σ (c + s) - s = σ (b + s) - s + 1` using `hv`. Take `⟨f1, f2⟩` from `hP (c + s) (b + s) (by omega) (by omega) (by omega)`. Conclude with `⟨by omega, f2⟩)`. Use `⟨(τ 0, s) :: bs, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Conclude with `⟨hτ 0 hpos, hs1⟩`. Conclude with `hb1 x hx`. Simplify using `only [List.map_cons, List.sum_cons, hb2]`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha b hb`. Simplify using `only [ptEntry]`. Distinguish the cases in `h1 : a < s ∧ b < s`. Rewrite using `[if_pos h1]`. Take `⟨e1, e2⟩` from `c1 b h1.2`.

Distinguish the cases in `h2 : a + b + 1 = s`. Rewrite using `[if_pos h2, if_pos (by omega), e2]`. Rewrite using `[if_neg h2, if_neg (by omega)]`. Rewrite using `[if_neg h1]`. Distinguish the cases in `h2 : s ≤ a ∧ s ≤ b`.

Rewrite using `[if_pos h2, hb3 (a - s) (by omega) (b - s) (by omega)]`. Establish `e0 : b - s + s = b` using `Nat.sub_add_cancel h2.2`. Establish `h3` using `c2 b h2.2 hb`. Simplify using `only [e0]`. Distinguish the cases in `h4 : a = σ b`.

Rewrite using `[if_pos h4, if_pos (by omega)]`. Rewrite using `[if_neg h4, if_neg (by omega)]`. Rewrite using `[if_neg h2]`. Break down `Nat.lt_or_ge b s with hbs | hbs` into its components or cases. Use `(c1 b hbs).1` as an intermediate fact.

Rewrite using `[if_neg (by omega)]`. Use `c2 b hbs hb` as an intermediate fact. Rewrite using `[if_neg (by omega)]`.
-/
theorem cpt_nat {K : Type} [Field K] : ∀ (n : ℕ) (σ : ℕ → ℕ) (τ : ℕ → K),
    (∀ i, i < n → σ i < n) → (∀ i, i < n → ∀ j, j < n → σ i = σ j → i = j) → (∀ v, v < n → ∃ i, i < n ∧ σ i = v) →
    (∀ i, i < n → τ i ≠ 0) →
    (∀ c b, c < b → b < n → σ c = σ b + 1 → b = c + 1 ∧ τ b = τ c) →
    ∃ bs : List (K × ℕ), (∀ x ∈ bs, x.1 ≠ 0 ∧ 1 ≤ x.2) ∧ (bs.map Prod.snd).sum = n ∧
      ∀ a, a < n → ∀ b, b < n → ptEntry bs a b = if a = σ b then τ b else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ hmap hinj hsurj hτ hP
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact ⟨[], by simp, by simp, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
    · obtain ⟨s, hs⟩ : ∃ s, s = σ 0 + 1 := ⟨_, rfl⟩
      have hsn : s ≤ n := by have := hmap 0 hpos; omega
      have hs1 : 1 ≤ s := by omega

      have c1 : ∀ i, i < s → σ i = s - 1 - i ∧ τ i = τ 0 := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ihi =>
          intro hi
          rcases Nat.eq_zero_or_pos i with hi0 | hipos
          · subst hi0
            exact ⟨by omega, rfl⟩
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            obtain ⟨e1, e2⟩ := ihi i' (by omega) (by omega)
            obtain ⟨b, hbn, hb⟩ := hsurj (s - 1 - (i' + 1)) (by omega)
            have hbi : i' + 1 ≤ b := by
              by_contra hlt
              have := (ihi b (by omega) (by omega)).1
              omega
            obtain ⟨f1, f2⟩ := hP i' b (by omega) hbn (by omega)
            subst f1
            exact ⟨hb, f2.trans e2⟩

      have c2 : ∀ i, s ≤ i → i < n → s ≤ σ i := by
        intro i hi hin
        by_contra hlt
        have hj : s - 1 - σ i < s := by omega
        have e := (c1 (s - 1 - σ i) hj).1
        have := hinj i hin (s - 1 - σ i) (by omega) (by omega)
        omega
      obtain ⟨bs, hb1, hb2, hb3⟩ := ih (n - s) (by omega) (fun i => σ (i + s) - s) (fun i => τ (i + s))
        (fun i hi => by
          have h1 := hmap (i + s) (by omega)
          have h2 := c2 (i + s) (by omega) (by omega)
          show σ (i + s) - s < n - s
          omega)
        (fun i hi j hj hij => by
          have h1 := c2 (i + s) (by omega) (by omega)
          have h2 := c2 (j + s) (by omega) (by omega)
          have h3 : σ (i + s) - s = σ (j + s) - s := hij
          have := hinj (i + s) (by omega) (j + s) (by omega) (by omega)
          omega)
        (fun v hv => by
          obtain ⟨i, hin, hi⟩ := hsurj (v + s) (by omega)
          have his : s ≤ i := by
            by_contra hlt
            have := (c1 i (by omega)).1
            omega
          refine ⟨i - s, by omega, ?_⟩
          show σ (i - s + s) - s = v
          rw [Nat.sub_add_cancel his, hi]
          omega)
        (fun i hi => hτ (i + s) (by omega))
        (fun c b hcb hbn hv => by
          have h1 := c2 (c + s) (by omega) (by omega)
          have h2 := c2 (b + s) (by omega) (by omega)
          have h3 : σ (c + s) - s = σ (b + s) - s + 1 := hv
          obtain ⟨f1, f2⟩ := hP (c + s) (b + s) (by omega) (by omega) (by omega)
          exact ⟨by omega, f2⟩)
      refine ⟨(τ 0, s) :: bs, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hτ 0 hpos, hs1⟩
        · exact hb1 x hx
      · simp only [List.map_cons, List.sum_cons, hb2]
        omega
      · intro a ha b hb
        simp only [ptEntry]
        by_cases h1 : a < s ∧ b < s
        · rw [if_pos h1]
          obtain ⟨e1, e2⟩ := c1 b h1.2
          by_cases h2 : a + b + 1 = s
          · rw [if_pos h2, if_pos (by omega), e2]
          · rw [if_neg h2, if_neg (by omega)]
        · rw [if_neg h1]
          by_cases h2 : s ≤ a ∧ s ≤ b
          · rw [if_pos h2, hb3 (a - s) (by omega) (b - s) (by omega)]
            have e0 : b - s + s = b := Nat.sub_add_cancel h2.2
            have h3 := c2 b h2.2 hb
            simp only [e0]
            by_cases h4 : a = σ b
            · rw [if_pos h4, if_pos (by omega)]
            · rw [if_neg h4, if_neg (by omega)]
          · rw [if_neg h2]
            rcases Nat.lt_or_ge b s with hbs | hbs
            · have := (c1 b hbs).1
              rw [if_neg (by omega)]
            · have := c2 b hbs hb
              rw [if_neg (by omega)]

/- English proof (translation)
Introduce `K _ n σ τ hσ hτ hP`. Take `⟨bs, h1, h2, h3⟩` from `cpt_nat n (fun i => if h : i < n then (σ ⟨i, h⟩).val else 0) (fun i => if h : i < n then τ ⟨i, h⟩ else 0) (fun i hi => by simp only [dif_pos hi]; exact (σ ⟨i, hi⟩).isLt) (fun i hi j hj hij => by`. Simplify using `only [dif_pos hi, dif_pos hj] at hij`. Use `hσ.1 (Fin.ext hij)` as an intermediate fact. Conclude with `congrArg Fin.val this)`.

Use the proof step `(fun v hv => by`. Take `⟨i, hi⟩` from `hσ.2 ⟨v, hv⟩`. Use `⟨i.val, i.isLt, ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos i.isLt, Fin.eta, hi])`. Use the proof step `(fun i hi => by simp only [dif_pos hi]; exact hτ _)`.

Use the proof step `(fun c b hcb hbn hv => by`. Establish `hcn : c < n` using `lt_trans hcb hbn`. Simplify using `only [dif_pos hcn, dif_pos hbn] at hv ⊢`. Conclude with `hP ⟨c, hcn⟩ ⟨b, hbn⟩ hcb hv)`. Use `⟨⟨bs, h1, h2⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `a b`. Apply the tactic sequence `show ptEntry bs a.val b.val = mono σ τ a b`. Rewrite using `[h3 a.val a.isLt b.val b.isLt]`. Simplify using `only [dif_pos b.isLt, Fin.eta, mono, Fin.ext_iff]`.
-/
theorem cell_point : MonomialMatrixIsPoint := by
  intro K _ n σ τ hσ hτ hP
  obtain ⟨bs, h1, h2, h3⟩ := cpt_nat n (fun i => if h : i < n then (σ ⟨i, h⟩).val else 0)
    (fun i => if h : i < n then τ ⟨i, h⟩ else 0)
    (fun i hi => by simp only [dif_pos hi]; exact (σ ⟨i, hi⟩).isLt)
    (fun i hi j hj hij => by
      simp only [dif_pos hi, dif_pos hj] at hij
      have := hσ.1 (Fin.ext hij)
      exact congrArg Fin.val this)
    (fun v hv => by
      obtain ⟨i, hi⟩ := hσ.2 ⟨v, hv⟩
      refine ⟨i.val, i.isLt, ?_⟩
      simp only [dif_pos i.isLt, Fin.eta, hi])
    (fun i hi => by simp only [dif_pos hi]; exact hτ _)
    (fun c b hcb hbn hv => by
      have hcn : c < n := lt_trans hcb hbn
      simp only [dif_pos hcn, dif_pos hbn] at hv ⊢
      exact hP ⟨c, hcn⟩ ⟨b, hbn⟩ hcb hv)
  refine ⟨⟨bs, h1, h2⟩, ?_⟩
  ext a b
  show ptEntry bs a.val b.val = mono σ τ a b
  rw [h3 a.val a.isLt b.val b.isLt]
  simp only [dif_pos b.isLt, Fin.eta, mono, Fin.ext_iff]

end Formalism.MainNotions.BridgeLemma

end
