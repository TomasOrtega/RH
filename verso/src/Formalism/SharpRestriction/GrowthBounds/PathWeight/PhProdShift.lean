import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeOldest
import Formalism.SharpRestriction.GrowthBounds.PathWeight.LeadingDepthOneMemClosure

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

/- English proof (translation)
Establish `hpos : ∀ a : ℤ, posOf n' (a + n' * t) = posOf n' a` using `fun a => posOf_add_mul_alt a t`. Establish `hev : Even ((n' : ℤ) * t)`. Establish `: Even (n' : ℤ)` using `by exact_mod_cast hn`. Conclude with `this.mul_right t`. Generalize the expression as in `(n' : ℤ) * t = s at hpos hev`.

Unfold `geN`. Apply `Finset.card_bij (fun a _ => a - s)` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [mem_filter, mem_Ioo] at ha ⊢`. Use `⟨⟨by omega, by omega⟩, ?_, ha.2.2.sub hev⟩` and prove the remaining obligations.

Use `hpos (a - s)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[← this]`. Conclude with `ha.2.1`. Introduce `a _ b _ h`.

Simplify using `using h`. Introduce `b hb`. Simplify using `only [mem_filter, mem_Ioo] at hb`. Use `⟨b + s, ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [mem_filter, mem_Ioo]`.

Conclude with `⟨⟨by omega, by omega⟩, by rw [hpos]; exact hb.2.1, hb.2.2.add hev⟩`.
-/
theorem ph_geN_shift (hn : Even n') (x y t : ℤ) : geN F (x + n' * t) (y + n' * t) = geN F x y := by
  have hpos : ∀ a : ℤ, posOf n' (a + n' * t) = posOf n' a := fun a => posOf_add_mul_alt a t
  have hev : Even ((n' : ℤ) * t) := by
    have : Even (n' : ℤ) := by exact_mod_cast hn
    exact this.mul_right t
  generalize (n' : ℤ) * t = s at hpos hev
  unfold geN
  apply Finset.card_bij (fun a _ => a - s)
  · intro a ha
    simp only [mem_filter, mem_Ioo] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, ?_, ha.2.2.sub hev⟩
    have := hpos (a - s)
    rw [sub_add_cancel] at this
    rw [← this]; exact ha.2.1
  · intro a _ b _ h
    simpa using h
  · intro b hb
    simp only [mem_filter, mem_Ioo] at hb
    refine ⟨b + s, ?_, by simp⟩
    simp only [mem_filter, mem_Ioo]
    exact ⟨⟨by omega, by omega⟩, by rw [hpos]; exact hb.2.1, hb.2.2.add hev⟩

/- English proof (translation)
Establish `h1` using `window_holds_even_tops n' r F L₁ N₁ hV hn hr (x + n' * t) l hl`. Establish `h2` using `window_holds_even_tops n' r F L₁ N₁ hV hn hr x l hl`. Establish `g1` using `ge_Arow F L₁ N₁ hV hn hr (x + n' * t) l hl`. Establish `g2` using `ge_Arow F L₁ N₁ hV hn hr x l hl`. Establish `hev : Even ((n' : ℤ) * t)`.

Establish `: Even (n' : ℤ)` using `by exact_mod_cast hn`. Conclude with `this.mul_right t`. Establish `e : Arow F (x + n' * t) l = (Arow F (x + n' * t) l - n' * t) + n' * t` using `by ring`. Establish `g3 : geN F x (Arow F (x + n' * t) l - n' * t) = l`. Rewrite using `[← ph_geN_shift F hn x _ t, ← e]`.

Conclude with `g1`. Establish `hT : posOf n' (Arow F (x + n' * t) l - n' * t) ∈ F.TT`. Rewrite using `[← posOf_add_mul_alt _ t, ← e]`. Conclude with `h1.2.1`. Use `ge_N_inj F (by linarith [h1.2.2]) h2.2.2 hT (h1.1.sub hev) h2.2.1 h2.1 (g3.trans g2.symm)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ph_Arow_shift (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r) (x t : ℤ) (l : ℕ) (hl : l < r) :
    Arow F (x + n' * t) l = Arow F x l + n' * t := by
  have h1 := window_holds_even_tops n' r F L₁ N₁ hV hn hr (x + n' * t) l hl
  have h2 := window_holds_even_tops n' r F L₁ N₁ hV hn hr x l hl
  have g1 := ge_Arow F L₁ N₁ hV hn hr (x + n' * t) l hl
  have g2 := ge_Arow F L₁ N₁ hV hn hr x l hl
  have hev : Even ((n' : ℤ) * t) := by
    have : Even (n' : ℤ) := by exact_mod_cast hn
    exact this.mul_right t
  have e : Arow F (x + n' * t) l = (Arow F (x + n' * t) l - n' * t) + n' * t := by ring
  have g3 : geN F x (Arow F (x + n' * t) l - n' * t) = l := by
    rw [← ph_geN_shift F hn x _ t, ← e]; exact g1
  have hT : posOf n' (Arow F (x + n' * t) l - n' * t) ∈ F.TT := by
    rw [← posOf_add_mul_alt _ t, ← e]; exact h1.2.1
  have := ge_N_inj F (by linarith [h1.2.2]) h2.2.2 hT (h1.1.sub hev) h2.2.1 h2.1 (g3.trans g2.symm)
  linarith

/- English proof (translation)
The claim follows from `lt_of_lt_of_le (hV.2.2.2.1 j) (frame_row_monotone F L₁ N₁ hV (j + 1) (r - 1) (by omega))`.
-/
theorem ph_z_step (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) : F.fr j (r - 1) < F.fr (j + 1) (r - 1) :=
  lt_of_lt_of_le (hV.2.2.2.1 j) (frame_row_monotone F L₁ N₁ hV (j + 1) (r - 1) (by omega))

/- English proof (translation)
Take `⟨t, rfl⟩ : ∃ t : ℕ, j' = j + t` from `⟨(j' - j).toNat, by omega⟩`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `succ t ih`. Use `ph_z_step F hV hr (j + t)` as an intermediate fact.

Establish `e : j + ((t + 1 : ℕ) : ℤ) = j + t + 1` using `by push_cast; ring`. Rewrite using `[e]`. Use `ih (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem ph_z_mono (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) {j j' : ℤ} (h : j ≤ j') : F.fr j (r - 1) ≤ F.fr j' (r - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, j' = j + t := ⟨(j' - j).toNat, by omega⟩
  induction t with
  | zero => simp
  | succ t ih =>
    have := ph_z_step F hV hr (j + t)
    have e : j + ((t + 1 : ℕ) : ℤ) = j + t + 1 := by push_cast; ring
    rw [e]
    have := ih (by omega)
    omega

/- English proof (translation)
Unfold `nonW Frames.letters Frames.IsW`. Simplify using `only [mem_filter, mem_Icc, not_le]`. Use `frame_row_monotone F L₁ N₁ hV (j - 1) (r - 1) (by omega)` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨_, b⟩, c⟩, d⟩`.

Conclude with `⟨d, b, c⟩`. Introduce and unpack `⟨a, b, c⟩; exact ⟨⟨⟨by omega, b⟩, c⟩, a⟩`.
-/
theorem ph_mem_nonW (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (j x : ℤ) :
    x ∈ nonW F j ↔ F.fr (j - 1) (r - 1) < x ∧ x ≤ F.fr j (r - 1) ∧ posOf n' x ∈ F.TT := by
  unfold nonW Frames.letters Frames.IsW
  simp only [mem_filter, mem_Icc, not_le]
  have := frame_row_monotone F L₁ N₁ hV (j - 1) (r - 1) (by omega)
  constructor
  · rintro ⟨⟨⟨_, b⟩, c⟩, d⟩; exact ⟨d, b, c⟩
  · rintro ⟨a, b, c⟩; exact ⟨⟨⟨by omega, b⟩, c⟩, a⟩

/- English proof (translation)
Establish `hper : F.fr ((F.J : ℤ) - 1) (r - 1) = F.fr (-1) (r - 1) + n'`. Use `hV.2.1 (-1) (r - 1)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Establish `hwin : ∀ j ∈ Finset.range F.J, ∀ x ∈ nonW F (j : ℤ), F.fr (-1) (r - 1) + 1 ≤ x ∧ x < F.fr (-1) (r - 1) + 1 + n'`.

Introduce `j hj x hx`. Rewrite `hx` using `[ph_mem_nonW F hV hr]`. Establish `hj'` using `Finset.mem_range.1 hj`. Establish `a1` using `ph_z_mono F hV hr (j := -1) (j' := (j : ℤ) - 1) (by omega)`. Establish `a2` using `ph_z_mono F hV hr (j := (j : ℤ)) (j' := (F.J : ℤ) - 1) (by omega)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.prod_biUnion]`. Apply `Finset.prod_bij (fun x _ => posOf n' x)` to reduce the goal to its premises. Introduce `x hx`. Take `⟨j, _, hx⟩` from `Finset.mem_biUnion.1 hx`.

Conclude with `((ph_mem_nonW F hV hr _ _).1 hx).2.2`. Introduce `x hx y hy h`. Take `⟨j, hj, hx⟩` from `Finset.mem_biUnion.1 hx`. Take `⟨j', hj', hy⟩` from `Finset.mem_biUnion.1 hy`. Conclude with `residue_position_injective_window n' _ x y (hwin j hj x hx) (hwin j' hj' y hy) h`.

Introduce `s hs set c : ℤ := F.fr (-1) (r - 1) + 1 with hc`. Establish `hn0 : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `b1` using `Int.emod_nonneg ((s.val : ℤ) - c) hn0.ne'`. Establish `b2` using `Int.emod_lt_of_pos ((s.val : ℤ) - c) hn0`. Establish `b3` using `Int.emod_def ((s.val : ℤ) - c) n'`.

Establish `hx0 : c + ((s.val : ℤ) - c) % n' = (s.val : ℤ) + n' * (-(((s.val : ℤ) - c) / n'))`. Rewrite using `[b3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp : posOf n' (c + ((s.val : ℤ) - c) % n') = s`. Rewrite using `[hx0, posOf_add_mul_alt, posOf_natCast_self]`.

Take `⟨j, h1, h2⟩` from `mn_cover F L₁ N₁ hV hr (c + ((s.val : ℤ) - c) % n') (by rw [hp]; exact hs)`. Establish `h3 : c + ((s.val : ℤ) - c) % n' ∈ nonW F j`. Unfold `nonW`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨h1, h2⟩`.

Establish `h4` using `(ph_mem_nonW F hV hr _ _).1 h3`. Establish `j0 : 0 ≤ j`. Assume the negation of the conclusion as `h`. Use `ph_z_mono F hV hr (j := j) (j' := -1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `j1 : j < F.J`. Assume the negation of the conclusion as `h`. Use `ph_z_mono F hV hr (j := (F.J : ℤ) - 1) (j' := j - 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨_, Finset.mem_biUnion.2 ⟨j.toNat, Finset.mem_range.2 (by omega), ?_⟩, hp⟩` and prove the remaining obligations.

Rewrite using `[Int.toNat_of_nonneg j0]`. Conclude with `h3`. Introduce `x _`. Both sides reduce to the same expression. Introduce `j _ j' _ hne`.

Rewrite using `[Function.onFun, Finset.disjoint_left]`. Introduce `x hx hy`. Rewrite `hx`, `hy` using `[ph_mem_nonW F hV hr]`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Use `ph_z_mono F hV hr (j := (j : ℤ)) (j' := (j' : ℤ) - 1) (by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `ph_z_mono F hV hr (j := (j' : ℤ)) (j' := (j : ℤ) - 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem ph_prod_tops {M : Type*} [CommMonoid M] (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (f : Fin n' → M) :
    ∏ j ∈ Finset.range F.J, ∏ x ∈ nonW F (j : ℤ), f (posOf n' x) = ∏ s ∈ F.TT, f s := by
  have hper : F.fr ((F.J : ℤ) - 1) (r - 1) = F.fr (-1) (r - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    rw [← this]; congr 1
  have hwin : ∀ j ∈ Finset.range F.J, ∀ x ∈ nonW F (j : ℤ),
      F.fr (-1) (r - 1) + 1 ≤ x ∧ x < F.fr (-1) (r - 1) + 1 + n' := by
    intro j hj x hx
    rw [ph_mem_nonW F hV hr] at hx
    have hj' := Finset.mem_range.1 hj
    have a1 := ph_z_mono F hV hr (j := -1) (j' := (j : ℤ) - 1) (by omega)
    have a2 := ph_z_mono F hV hr (j := (j : ℤ)) (j' := (F.J : ℤ) - 1) (by omega)
    omega
  rw [← Finset.prod_biUnion]
  · apply Finset.prod_bij (fun x _ => posOf n' x)
    · intro x hx
      obtain ⟨j, _, hx⟩ := Finset.mem_biUnion.1 hx
      exact ((ph_mem_nonW F hV hr _ _).1 hx).2.2
    · intro x hx y hy h
      obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨j', hj', hy⟩ := Finset.mem_biUnion.1 hy
      exact residue_position_injective_window n' _ x y (hwin j hj x hx) (hwin j' hj' y hy) h
    · intro s hs
      set c : ℤ := F.fr (-1) (r - 1) + 1 with hc
      have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
      have b1 := Int.emod_nonneg ((s.val : ℤ) - c) hn0.ne'
      have b2 := Int.emod_lt_of_pos ((s.val : ℤ) - c) hn0
      have b3 := Int.emod_def ((s.val : ℤ) - c) n'
      have hx0 : c + ((s.val : ℤ) - c) % n' = (s.val : ℤ) + n' * (-(((s.val : ℤ) - c) / n')) := by
        rw [b3]; ring
      have hp : posOf n' (c + ((s.val : ℤ) - c) % n') = s := by
        rw [hx0, posOf_add_mul_alt, posOf_natCast_self]
      obtain ⟨j, h1, h2⟩ := mn_cover F L₁ N₁ hV hr (c + ((s.val : ℤ) - c) % n') (by rw [hp]; exact hs)
      have h3 : c + ((s.val : ℤ) - c) % n' ∈ nonW F j := by
        unfold nonW; rw [Finset.mem_filter]; exact ⟨h1, h2⟩
      have h4 := (ph_mem_nonW F hV hr _ _).1 h3
      have j0 : 0 ≤ j := by
        by_contra h
        have := ph_z_mono F hV hr (j := j) (j' := -1) (by omega)
        omega
      have j1 : j < F.J := by
        by_contra h
        have := ph_z_mono F hV hr (j := (F.J : ℤ) - 1) (j' := j - 1) (by omega)
        omega
      refine ⟨_, Finset.mem_biUnion.2 ⟨j.toNat, Finset.mem_range.2 (by omega), ?_⟩, hp⟩
      rw [Int.toNat_of_nonneg j0]; exact h3
    · intro x _; rfl
  · intro j _ j' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hy
    rw [ph_mem_nonW F hV hr] at hx hy
    rcases lt_or_gt_of_ne hne with h | h
    · have := ph_z_mono F hV hr (j := (j : ℤ)) (j' := (j' : ℤ) - 1) (by omega)
      omega
    · have := ph_z_mono F hV hr (j := (j' : ℤ)) (j' := (j : ℤ) - 1) (by omega)
      omega

end

/- English proof (translation)
Take `⟨J', rfl⟩ : ∃ J', J = J' + 1` from `⟨J - 1, by omega⟩`. Rewrite using `[Finset.prod_range_succ', Finset.prod_range_succ]`. Establish `e1 : g (((0 : ℕ) : ℤ) - 1) = g (J' : ℤ)`. Rewrite using `[← hg]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ph_prod_shift {M : Type*} [CommMonoid M] (J : ℕ) (hJ : 1 ≤ J) (g : ℤ → M) (hg : ∀ j, g (j + J) = g j) :
    ∏ j ∈ Finset.range J, g ((j : ℤ) - 1) = ∏ j ∈ Finset.range J, g (j : ℤ) := by
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  have e1 : g (((0 : ℕ) : ℤ) - 1) = g (J' : ℤ) := by
    rw [← hg]; congr 1; push_cast; ring
  rw [e1]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1; push_cast; ring

end Formalism.MainNotions.G.symbolGeneratorData
