import Formalism.SubspaceCounting.StatementC

namespace Formalism.G0

namespace TailSumsP

/- English proof (translation)
Simplify using `[tailK]`.
-/
theorem tailK_zero {K : ℕ} (α : Fin K → ℕ) : tailK α 0 = ∑ l, α l := by
  simp [tailK]

/- English proof (translation)
Simplify using `[tailK]`.
-/
theorem tailK_zero_fun {K : ℕ} (u : ℕ) : tailK (0 : Fin K → ℕ) u = 0 := by
  simp [tailK]

/- English proof (translation)
Unfold `tailK`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l _`. Use `split_ifs`. Conclude with `h l`.

Conclude with `le_rfl`.
-/
theorem tailK_shrink {K : ℕ} {α α' : Fin K → ℕ} (h : ShrinkStep α α') (u : ℕ) :
    tailK α' u ≤ tailK α u := by
  unfold tailK
  apply Finset.sum_le_sum
  intro l _
  split_ifs
  · exact h l
  · exact le_rfl

/- English proof (translation)
Take `⟨-, h2, -⟩` from `h`. Consider the cases of `K with`. Consider the case `zero => simp [tailK]`. Consider the case `succ k`. Unfold `tailK`.

Rewrite using `[Fin.sum_univ_succ, Fin.sum_univ_castSucc (f := fun l : Fin (k + 1) => if u ≤ l.val then α l else 0)]`. Simplify using `only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Nat.add_le_add_iff_right, Nat.le_zero, Nat.add_one_ne_zero, if_false, zero_add]`. Use `le_trans ?_ (Nat.le_add_right _ _)` and prove the remaining obligations. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`.

Distinguish the cases in `hu : u ≤ i.val`. Rewrite using `[if_pos (by omega), if_pos hu]`. Establish `hh : i.castSucc.val + 1 < k + 1` using `by simp`. Establish `e : (⟨i.castSucc.val + 1, hh⟩ : Fin (k + 1)) = i.succ` using `Fin.ext (by simp)`. Use `h2 i.castSucc hh` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Rewrite using `[if_neg (by omega), if_neg hu]`.
-/
theorem tailK_vec_succ {K : ℕ} {α α' : Fin K → ℕ} {B : ℕ} (h : VecStep α α' B) (u : ℕ) :
    tailK α' (u + 1) ≤ tailK α u := by
  obtain ⟨-, h2, -⟩ := h
  cases K with
  | zero => simp [tailK]
  | succ k =>
    unfold tailK
    rw [Fin.sum_univ_succ,
      Fin.sum_univ_castSucc (f := fun l : Fin (k + 1) => if u ≤ l.val then α l else 0)]
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Nat.add_le_add_iff_right,
      Nat.le_zero, Nat.add_one_ne_zero, if_false, zero_add]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Finset.sum_le_sum
    intro i _
    by_cases hu : u ≤ i.val
    · rw [if_pos (by omega), if_pos hu]
      have hh : i.castSucc.val + 1 < k + 1 := by simp
      have e : (⟨i.castSucc.val + 1, hh⟩ : Fin (k + 1)) = i.succ := Fin.ext (by simp)
      have := h2 i.castSucc hh
      rw [e] at this
      exact this
    · rw [if_neg (by omega), if_neg hu]

/- English proof (translation)
Rewrite using `[tailK_zero, tailK_zero]`. Conclude with `h.2.2`.
-/
theorem tailK_vec_zero {K : ℕ} {α α' : Fin K → ℕ} {B : ℕ} (h : VecStep α α' B) :
    tailK α' 0 ≤ tailK α 0 + B := by
  rw [tailK_zero, tailK_zero]; exact h.2.2

/- English proof (translation)
Unfold `latestDegrees`. Rewrite using `[List.take_add_one, List.getElem?_eq_getElem hi, h]`. Simplify using the standard rewrite rules.
-/
theorem latestDegrees_succ_some (steps : List (Option ℕ)) (i : ℕ) (hi : i < steps.length)
    {B : ℕ} (h : steps[i] = some B) :
    latestDegrees steps (i + 1) = B :: latestDegrees steps i := by
  unfold latestDegrees
  rw [List.take_add_one, List.getElem?_eq_getElem hi, h]
  simp

/- English proof (translation)
Unfold `latestDegrees`. Rewrite using `[List.take_add_one, List.getElem?_eq_getElem hi, h]`. Simplify using the standard rewrite rules.
-/
theorem latestDegrees_succ_none (steps : List (Option ℕ)) (i : ℕ) (hi : i < steps.length)
    (h : steps[i] = none) :
    latestDegrees steps (i + 1) = latestDegrees steps i := by
  unfold latestDegrees
  rw [List.take_add_one, List.getElem?_eq_getElem hi, h]
  simp

def cnt (steps : List (Option ℕ)) (i j : ℕ) : ℕ :=
  (((steps.drop i).take (j - i)).filterMap id).length

/- English proof (translation)
Simplify using `[cnt]`.
-/
theorem cnt_self (steps : List (Option ℕ)) (i : ℕ) : cnt steps i i = 0 := by
  simp [cnt]

/- English proof (translation)
Unfold `cnt`. Rewrite using `[show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop, show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]`. Simplify using the standard rewrite rules.
-/
theorem cnt_succ_some (steps : List (Option ℕ)) (i j : ℕ) (hij : i ≤ j) (hj : j < steps.length)
    {B : ℕ} (h : steps[j] = some B) : cnt steps i (j + 1) = cnt steps i j + 1 := by
  unfold cnt
  rw [show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]
  simp

/- English proof (translation)
Unfold `cnt`. Rewrite using `[show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop, show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]`. Simplify using the standard rewrite rules.
-/
theorem cnt_succ_none (steps : List (Option ℕ)) (i j : ℕ) (hij : i ≤ j) (hj : j < steps.length)
    (h : steps[j] = none) : cnt steps i (j + 1) = cnt steps i j := by
  unfold cnt
  rw [show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]
  simp

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _ u`. Rewrite using `[hp.1, tailK_zero_fun]`. Conclude with `Nat.zero_le _`.

Consider the case `succ i ih`. Introduce `hi u`. Establish `hi' : i < steps.length` using `by omega`. Establish `hstep` using `hp.2 i hi'`. Consider the cases of `hs : steps[i] with`.

Consider the case `none`. Simplify using `only [hs] at hstep`. Rewrite using `[latestDegrees_succ_none steps i hi' hs]`. Conclude with `le_trans (tailK_shrink hstep u) (ih (by omega) u)`. Consider the case `some B`.

Simplify using `only [hs] at hstep`. Rewrite using `[latestDegrees_succ_some steps i hi' hs]`. Consider the cases of `u with`. Consider the case `zero`. Simplify using `only [List.drop_zero, List.sum_cons]`.

Establish `h1` using `ih (by omega) 0`. Simplify using `only [List.drop_zero] at h1`. Establish `h2` using `tailK_vec_zero hstep`. Use linear arithmetic over natural numbers and integers. Consider the case `succ u`.

Simplify using `only [List.drop_succ_cons]`. Conclude with `le_trans (tailK_vec_succ hstep u) (ih (by omega) u)`.
-/
theorem clause1 {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) :
    ∀ i ≤ steps.length, ∀ u, tailK (what₂ i) u ≤ ((latestDegrees steps i).drop u).sum := by
  intro i
  induction i with
  | zero => intro _ u; rw [hp.1, tailK_zero_fun]; exact Nat.zero_le _
  | succ i ih =>
    intro hi u
    have hi' : i < steps.length := by omega
    have hstep := hp.2 i hi'
    cases hs : steps[i] with
    | none =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_none steps i hi' hs]
      exact le_trans (tailK_shrink hstep u) (ih (by omega) u)
    | some B =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_some steps i hi' hs]
      cases u with
      | zero =>
        simp only [List.drop_zero, List.sum_cons]
        have h1 := ih (by omega) 0
        simp only [List.drop_zero] at h1
        have h2 := tailK_vec_zero hstep
        omega
      | succ u =>
        simp only [List.drop_succ_cons]
        exact le_trans (tailK_vec_succ hstep u) (ih (by omega) u)

/- English proof (translation)
Introduce `j hij`. Proceed by induction on `j, hij using Nat.le_induction with`. Consider the case `base => intro _`. Rewrite using `[cnt_self, Nat.add_zero]`. Conclude with `hX`.

Consider the case `succ j hij ih`. Introduce `hj`. Establish `hj' : j < steps.length` using `by omega`. Establish `hstep` using `hp.2 j hj'`. Consider the cases of `hs : steps[j] with`.

Consider the case `none`. Simplify using `only [hs] at hstep`. Rewrite using `[latestDegrees_succ_none steps j hj' hs, cnt_succ_none steps i j hij hj' hs]`. Use `tailK_shrink hstep (u + cnt steps i j)` as an intermediate fact. Use `ih (by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Consider the case `some B`. Simplify using `only [hs] at hstep`. Rewrite using `[latestDegrees_succ_some steps j hj' hs, cnt_succ_some steps i j hij hj' hs, ← Nat.add_assoc, List.drop_succ_cons]`. Use `tailK_vec_succ hstep (u + cnt steps i j)` as an intermediate fact.

Use `ih (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem clause2 {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) (i u X : ℕ)
    (hX : tailK (what₂ i) u + X ≤ ((latestDegrees steps i).drop u).sum) :
    ∀ j, i ≤ j → j ≤ steps.length →
      tailK (what₂ j) (u + cnt steps i j) + X ≤
        ((latestDegrees steps j).drop (u + cnt steps i j)).sum := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; rw [cnt_self, Nat.add_zero]; exact hX
  | succ j hij ih =>
    intro hj
    have hj' : j < steps.length := by omega
    have hstep := hp.2 j hj'
    cases hs : steps[j] with
    | none =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_none steps j hj' hs, cnt_succ_none steps i j hij hj' hs]
      have := tailK_shrink hstep (u + cnt steps i j)
      have := ih (by omega)
      omega
    | some B =>
      simp only [hs] at hstep
      rw [latestDegrees_succ_some steps j hj' hs, cnt_succ_some steps i j hij hj' hs,
        ← Nat.add_assoc, List.drop_succ_cons]
      have := tailK_vec_succ hstep (u + cnt steps i j)
      have := ih (by omega)
      omega

end TailSumsP

/- English proof (translation)
Introduce `K steps what₂ hp`. Use `⟨TailSumsP.clause1 steps what₂ hp, ?_⟩` and prove the remaining obligations. Introduce `i j u X hij hj hX`. Conclude with `TailSumsP.clause2 steps what₂ hp i u X hX j hij hj`.
-/
theorem tail_sums : TailSums := by
  intro K steps what₂ hp
  refine ⟨TailSumsP.clause1 steps what₂ hp, ?_⟩
  intro i j u X hij hj hX
  exact TailSumsP.clause2 steps what₂ hp i u X hX j hij hj

end Formalism.G0
