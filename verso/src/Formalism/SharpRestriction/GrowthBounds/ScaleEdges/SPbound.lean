import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPtrueHom
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.GainBoundAt

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Pos

variable {n' : ℕ} [NeZero n']

/- English proof (translation)
Establish `h0 : (0:ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `h1` using `Int.emod_nonneg x h0.ne'`. Establish `h2` using `Int.emod_lt_of_pos x h0`. Simplify using `only [posOf]`. Rewrite using `[Nat.mod_eq_of_lt (by omega)]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem posOf_val (x : ℤ) : ((posOf n' x).val : ℤ) = x % n' := by
  have h0 : (0:ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h1 := Int.emod_nonneg x h0.ne'
  have h2 := Int.emod_lt_of_pos x h0
  simp only [posOf]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/- English proof (translation)
Establish `h'` using `congrArg (fun s : Fin n' => (s.val : ℤ)) h`. Simplify using `only [posOf_val] at h'`. Establish `hd : (n' : ℤ) ∣ a - b` using `(Int.ModEq.dvd h'.symm)`. Take `⟨k, hk⟩` from `hd`. Establish `h0 : (0:ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`.

Break down `lt_trichotomy k 0 with hk0 | hk0 | hk0` into its components or cases. Establish `: (n' : ℤ) * k ≤ -(n' : ℤ)` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Substitute `hk0` using the available equality. Simplify using `at hk`.

Use linear arithmetic over natural numbers and integers. Establish `: (n' : ℤ) ≤ (n' : ℤ) * k` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem posOf_inj {y a b : ℤ} (ha : y ≤ a ∧ a < y + n') (hb : y ≤ b ∧ b < y + n') (h : posOf n' a = posOf n' b) :
    a = b := by
  have h' := congrArg (fun s : Fin n' => (s.val : ℤ)) h
  simp only [posOf_val] at h'
  have hd : (n' : ℤ) ∣ a - b := (Int.ModEq.dvd h'.symm)
  obtain ⟨k, hk⟩ := hd
  have h0 : (0:ℤ) < n' := by exact_mod_cast NeZero.pos n'
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : (n' : ℤ) * k ≤ -(n' : ℤ) := by nlinarith
    omega
  · subst hk0; simp at hk; omega
  · have : (n' : ℤ) ≤ (n' : ℤ) * k := by nlinarith
    omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Establish `h` using `posOf_val (n' := n') (s.val : ℤ)`. Establish `hs` using `s.isLt`. Establish `: ((s.val : ℤ) % (n' : ℤ)) = s.val` using `Int.emod_eq_of_lt (by omega) (by exact_mod_cast hs)`. Use linear arithmetic over natural numbers and integers.
-/
theorem posOf_self (s : Fin n') : posOf n' (s.val : ℤ) = s := by
  apply Fin.ext
  have h := posOf_val (n' := n') (s.val : ℤ)
  have hs := s.isLt
  have : ((s.val : ℤ) % (n' : ℤ)) = s.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hs)
  omega

end Pos

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hx` using `[Finset.mem_filter]`. Conclude with `hf x hx.1 hx.2)`. Use `_ = (s.filter c).card * M := by rw [Finset.sum_const, smul_eq_mul]`.

Use `_ ≤ n * M := Nat.mul_le_mul_right _ hc`.
-/
theorem sum_ite_le {α : Type} (s : Finset α) (c : α → Prop) [DecidablePred c] (f : α → ℕ) (M n : ℕ)
    (hf : ∀ x ∈ s, c x → f x ≤ M) (hc : (s.filter c).card ≤ n) : ∑ x ∈ s, (if c x then f x else 0) ≤ n * M := by
  rw [← Finset.sum_filter]
  calc ∑ x ∈ s.filter c, f x ≤ ∑ _x ∈ s.filter c, M :=
        Finset.sum_le_sum (fun x hx => by
          rw [Finset.mem_filter] at hx
          exact hf x hx.1 hx.2)
    _ = (s.filter c).card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * M := Nat.mul_le_mul_right _ hc

section Fr

variable {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Take `⟨-, -, hinc, -⟩` from `hV`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_lt hll`. Proceed by induction on `m with`. Consider the case `zero => exact hinc j l (by omega)`. Consider the case `succ m ih`.

Establish `h1` using `ih (by omega) (by omega)`. Establish `h2` using `hinc j (l + m + 1) (by omega)`. Use `show F.fr j l < F.fr j (l + m + 1 + 1)`. Conclude with `lt_trans h1 h2`.
-/
private theorem fr_lt_fr_of_lt (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l < l') (hl' : l' < r) :
    F.fr j l < F.fr j l' := by
  obtain ⟨-, -, hinc, -⟩ := hV
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hll
  induction m with
  | zero => exact hinc j l (by omega)
  | succ m ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hinc j (l + m + 1) (by omega)
    show F.fr j l < F.fr j (l + m + 1 + 1)
    exact lt_trans h1 h2

/- English proof (translation)
Break down `Nat.lt_or_eq_of_le hll with h | rfl` into its components or cases. Conclude with `le_of_lt (fr_lt_fr_of_lt hV j h hl')`. Conclude with `le_rfl`.
-/
private theorem fr_le_fr_of_le (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l ≤ l') (hl' : l' < r) :
    F.fr j l ≤ F.fr j l' := by
  rcases Nat.lt_or_eq_of_le hll with h | rfl
  · exact le_of_lt (fr_lt_fr_of_lt hV j h hl')
  · exact le_rfl

/- English proof (translation)
Establish `h0 : ∀ i : ℤ, F.fr i 0 ≤ F.fr i (r - 1)` using `fun i => fr_le_fr_of_le hV i (Nat.zero_le _) (by omega)`. Take `⟨-, -, -, hnx, -⟩` from `hV`. Proceed by induction on `d with`. Consider the case `zero => simpa using hnx j`. Consider the case `succ d ih`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem fr_next (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (d : ℕ) : F.fr j (r - 1) < F.fr (j + 1 + d) 0 := by
  have h0 : ∀ i : ℤ, F.fr i 0 ≤ F.fr i (r - 1) := fun i => fr_le_fr_of_le hV i (Nat.zero_le _) (by omega)
  obtain ⟨-, -, -, hnx, -⟩ := hV
  induction d with
  | zero => simpa using hnx j
  | succ d ih =>
    calc F.fr j (r - 1) < F.fr (j + 1 + d) 0 := ih
      _ ≤ F.fr (j + 1 + d) (r - 1) := h0 _
      _ < F.fr (j + 1 + d + 1) 0 := hnx _
      _ = F.fr (j + 1 + ((d + 1 : ℕ) : ℤ)) 0 := by congr 1; push_cast; ring

/- English proof (translation)
Conclude with `fr_le_fr_of_le hV j (by omega) (by omega)`.
-/
theorem fr_le_last (hV : F.Valid L₁ N₁) (j : ℤ) {l : ℕ} (hl : l < r) : F.fr j l ≤ F.fr j (r - 1) := by
  exact fr_le_fr_of_le hV j (by omega) (by omega)

/- English proof (translation)
Take `⟨d, hd⟩ : ∃ d : ℕ, j' = j + 1 + d` from `⟨(j' - j - 1).toNat, by omega⟩`. Substitute `hd` using the available equality. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fr_lex (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) {j j' : ℤ} (hjj : j < j') {l l' : ℕ} (hl : l < r) (hl' : l' < r) :
    F.fr j l < F.fr j' l' := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j' = j + 1 + d := ⟨(j' - j - 1).toNat, by omega⟩
  subst hd
  calc F.fr j l ≤ F.fr j (r - 1) := fr_le_fr_of_le hV j (by omega) (by omega)
    _ < F.fr (j + 1 + d) 0 := fr_next hV hr j d
    _ ≤ F.fr (j + 1 + d) l' := fr_le_fr_of_le hV _ (Nat.zero_le _) hl'

/- English proof (translation)
Establish `hr0 : 0 < r` using `hr`. Establish `hlt : ∀ {c c' : ℕ} {i i' : Fin r}, (c < c' ∨ (c = c' ∧ i.val < i'.val)) → F.fr (c : ℤ) i.val < F.fr (c' : ℤ) i'.val`. Introduce `c c' i i' h`. Break down `h with h | ⟨rfl, h⟩` into its components or cases. Conclude with `fr_lex hV hr (by exact_mod_cast h) i.isLt i'.isLt`.

Conclude with `fr_lt_fr_of_lt hV _ h i'.isLt`. Establish `hper : F.fr (F.J : ℤ) 0 = F.fr 0 0 + n'`. Use `hV.2.1 0 0` as an intermediate fact. Simplify using `using this`. Establish `win : ∀ (c : ℕ) (i : Fin r), c < F.J → F.fr 0 0 ≤ F.fr c i.val ∧ F.fr c i.val < F.fr 0 0 + n'`.

Introduce `c i hc`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos c with rfl | hc0` into its components or cases. Break down `Nat.eq_zero_or_pos i.val with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Use `hlt (c := 0) (c' := 0) (i := ⟨0, hr0⟩) (i' := i) (Or.inr ⟨rfl, h0⟩)` as an intermediate fact. Simplify using `using le_of_lt this`. Use `hlt (c := 0) (c' := c) (i := ⟨0, hr0⟩) (i' := i) (Or.inl hc0)` as an intermediate fact. Simplify using `using le_of_lt this`.

Rewrite using `[← hper]`. Conclude with `hlt (c := c) (c' := F.J) (i := i) (i' := ⟨0, hr0⟩) (Or.inl hc)`. Rewrite using `[Finset.card_le_one]`. Introduce and unpack `⟨a1, a2⟩ ha ⟨b1, b2⟩ hb`. Simplify using `only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at ha hb`.

Establish `heq : F.fr (a1 : ℤ) a2.val = F.fr (b1 : ℤ) b2.val`. Establish `wa` using `win a1 a2 ha.1`. Establish `wb` using `win b1 b2 hb.1`. Conclude with `posOf_inj ⟨wa.1, wa.2⟩ ⟨wb.1, wb.2⟩ (ha.2.symm.trans hb.2)`. Break down `lt_trichotomy a1 b1 with h | rfl | h` into its components or cases.

Conclude with `absurd heq (ne_of_lt (hlt (Or.inl h)))`. Break down `lt_trichotomy a2.val b2.val with h2 | h2 | h2` into its components or cases. Conclude with `absurd heq (ne_of_lt (hlt (Or.inr ⟨rfl, h2⟩)))`. Rewrite using `[Fin.ext h2]`. Conclude with `absurd heq.symm (ne_of_lt (hlt (Or.inr ⟨rfl, h2⟩)))`.

Conclude with `absurd heq.symm (ne_of_lt (hlt (Or.inl h)))`.
-/
theorem frame_pairs (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (t : Fin n') :
    (((Finset.range F.J) ×ˢ (Finset.univ : Finset (Fin r))).filter
      (fun x => t = posOf n' (F.fr (x.1 : ℤ) x.2.val))).card ≤ 1 := by
  have hr0 : 0 < r := hr
  have hlt : ∀ {c c' : ℕ} {i i' : Fin r}, (c < c' ∨ (c = c' ∧ i.val < i'.val)) →
      F.fr (c : ℤ) i.val < F.fr (c' : ℤ) i'.val := by
    intro c c' i i' h
    rcases h with h | ⟨rfl, h⟩
    · exact fr_lex hV hr (by exact_mod_cast h) i.isLt i'.isLt
    · exact fr_lt_fr_of_lt hV _ h i'.isLt
  have hper : F.fr (F.J : ℤ) 0 = F.fr 0 0 + n' := by
    have := hV.2.1 0 0
    simpa using this
  have win : ∀ (c : ℕ) (i : Fin r), c < F.J →
      F.fr 0 0 ≤ F.fr c i.val ∧ F.fr c i.val < F.fr 0 0 + n' := by
    intro c i hc
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc0
      · rcases Nat.eq_zero_or_pos i.val with h0 | h0
        · rw [h0]; simp
        · have := hlt (c := 0) (c' := 0) (i := ⟨0, hr0⟩) (i' := i) (Or.inr ⟨rfl, h0⟩)
          simpa using le_of_lt this
      · have := hlt (c := 0) (c' := c) (i := ⟨0, hr0⟩) (i' := i) (Or.inl hc0)
        simpa using le_of_lt this
    · rw [← hper]
      exact hlt (c := c) (c' := F.J) (i := i) (i' := ⟨0, hr0⟩) (Or.inl hc)
  rw [Finset.card_le_one]
  rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at ha hb
  have heq : F.fr (a1 : ℤ) a2.val = F.fr (b1 : ℤ) b2.val := by
    have wa := win a1 a2 ha.1
    have wb := win b1 b2 hb.1
    exact posOf_inj ⟨wa.1, wa.2⟩ ⟨wb.1, wb.2⟩ (ha.2.symm.trans hb.2)
  rcases lt_trichotomy a1 b1 with h | rfl | h
  · exact absurd heq (ne_of_lt (hlt (Or.inl h)))
  · rcases lt_trichotomy a2.val b2.val with h2 | h2 | h2
    · exact absurd heq (ne_of_lt (hlt (Or.inr ⟨rfl, h2⟩)))
    · rw [Fin.ext h2]
    · exact absurd heq.symm (ne_of_lt (hlt (Or.inr ⟨rfl, h2⟩)))
  · exact absurd heq.symm (ne_of_lt (hlt (Or.inl h)))

/- English proof (translation)
Unfold `Arow`. Rewrite using `[List.getD_eq_getElem?_getD]`. Consider the cases of `h : (evensBefore F s)[l]? with`. Consider the case `none => left`. Simplify using the standard rewrite rules.

Consider the case `some y => right`. Establish `hm : y ∈ evensBefore F s` using `List.mem_of_getElem? h`. Rewrite `hm` using `[Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem]`. Simplify using `only [Option.getD_some]`. Conclude with `⟨hm.1.2, hm.2.1⟩`.
-/
theorem arow_cases (F : Frames n' r) (s : ℤ) (l : ℕ) :
    Arow F s l = s ∨ (Arow F s l < s ∧ posOf n' (Arow F s l) ∈ F.TT) := by
  unfold Arow
  rw [List.getD_eq_getElem?_getD]
  cases h : (evensBefore F s)[l]? with
  | none => left; simp
  | some y =>
    right
    have hm : y ∈ evensBefore F s := List.mem_of_getElem? h
    rw [Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem] at hm
    simp only [Option.getD_some]
    exact ⟨hm.1.2, hm.2.1⟩

end Fr

end Formalism.MainNotions.Pf14
