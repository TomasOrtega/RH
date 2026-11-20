import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

/- English proof (translation)
Unfold `hwt`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp`. Consider the case `succ j`. Rewrite using `[Fin.cons_succ, if_neg (Fin.succ_ne_zero j)]`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [Fin.succ_last]`. Consider the case `cast j`. Rewrite using `[Fin.snoc_castSucc, if_neg]`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem hwt_apply (m A B : ℕ) (i : Fin (m + 2)) :
    hwt m A B i = if i = 0 then (A : ℤ) else if i = Fin.last (m + 1) then -(B : ℤ) else 0 := by
  unfold hwt
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
    rw [Fin.cons_succ, if_neg (Fin.succ_ne_zero j)]
    induction j using Fin.lastCases with
    | last => simp [Fin.succ_last]
    | cast j =>
      rw [Fin.snoc_castSucc, if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega

/- English proof (translation)
Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Rewrite using `[Fin.cons_zero, if_neg]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Consider the case `succ j`. Rewrite using `[Fin.cons_succ]`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [Fin.succ_last]`.

Consider the case `cast j`. Rewrite using `[Fin.snoc_castSucc, if_neg]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem cov_apply (m : ℕ) (d : ℤ) (i : Fin (m + 2)) :
    (Fin.cons d (Fin.snoc (fun _ : Fin m => d) 0) : Fin (m + 2) → ℤ) i =
      if i = Fin.last (m + 1) then 0 else d := by
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  | succ j =>
    rw [Fin.cons_succ]
    induction j using Fin.lastCases with
    | last => simp [Fin.succ_last]
    | cast j =>
      rw [Fin.snoc_castSucc, if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega

/- English proof (translation)
Unfold `dimHar`. Rewrite using `[mul_comm (dimPol k A), mul_comm (dimPol k (A - 1))]`. Simplify using `only [or_comm]`.
-/
theorem dimHar_comm (k A B : ℕ) : dimHar k A B = dimHar k B A := by
  unfold dimHar
  rw [mul_comm (dimPol k A), mul_comm (dimPol k (A - 1))]
  simp only [or_comm]

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`.
-/
theorem last_ne_zero' (m : ℕ) : Fin.last (m + 1) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

/- English proof (translation)
Establish `h1 : ∏ s : Fin n', (if h : s ∈ TT then f ⟨s, h⟩ else 1) = ∏ s ∈ TT, (if h : s ∈ TT then f ⟨s, h⟩ else 1)`. Use `symm`. Apply `Finset.prod_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `s _ hs`. Rewrite using `[dif_neg hs]`.

Rewrite using `[h1, ← Finset.prod_attach, Finset.univ_eq_attach]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos s.2]`.
-/
theorem prod_tops {n' : ℕ} (TT : Finset (Fin n')) (f : TT → ℚ) :
    ∏ s : Fin n', (if h : s ∈ TT then f ⟨s, h⟩ else 1) = ∏ s : TT, f s := by
  classical
  have h1 : ∏ s : Fin n', (if h : s ∈ TT then f ⟨s, h⟩ else 1) =
      ∏ s ∈ TT, (if h : s ∈ TT then f ⟨s, h⟩ else 1) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro s _ hs
    rw [dif_neg hs]
  rw [h1, ← Finset.prod_attach, Finset.univ_eq_attach]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [dif_pos s.2]

/- English proof (translation)
Introduce `s i j hij`. Unfold `flatW`. Apply the tactic sequence `split_ifs with hs h1 h2 h3 h4 h5 h6 h7 <;> first | omega | skip`. Apply the tactic sequence `all_goals first`. Consider the case `(exfalso subst_vars first`.

Consider the case `exact absurd (Fin.le_zero_iff.1 hij) (by assumption)`. Consider the case `exact absurd (le_antisymm (Fin.le_last _) hij) (by assumption))`.
-/
theorem flatW_dom {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (A B : TT → ℕ) : IsDominant (flatW (m + 1) A B) := by
  intro s i j hij
  unfold flatW
  split_ifs with hs h1 h2 h3 h4 h5 h6 h7 <;> first | omega | skip
  all_goals
    first
    | (exfalso
       subst_vars
       first
       | exact absurd (Fin.le_zero_iff.1 hij) (by assumption)
       | exact absurd (le_antisymm (Fin.le_last _) hij) (by assumption))

/- English proof (translation)
Distinguish the cases in `hs : s ∈ TT`. Rewrite using `[dif_pos hs]`. Unfold `lamAt`. Use `split_ifs with he`. Establish `: flatW (m + 1) A B s = hwt m (A ⟨s, hs⟩) (B ⟨s, hs⟩)`.

Use function extensionality and compare the values at `i`. Rewrite using `[hwt_apply]`. Simplify using `[flatW, hs]`. Rewrite using `[this, weylDim_hwt_eq]`. Establish `: (fun i : Fin (m + 1 + 1) => -flatW (m + 1) A B s i.rev) = hwt m (B ⟨s, hs⟩) (A ⟨s, hs⟩)`.

Use function extensionality and compare the values at `i`. Rewrite using `[hwt_apply]`. Simplify using `only [flatW, hs, dif_pos]`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality.

Rewrite using `[Fin.rev_zero, if_neg (last_ne_zero' m)]`. Simplify using the standard rewrite rules. Distinguish the cases in `hl : i = Fin.last (m + 1)`. Substitute `hl` using the available equality. Rewrite using `[Fin.rev_last]`.

Simplify using `[last_ne_zero' m]`. Establish `h1 : i.rev ≠ 0`. Introduce `h`. Apply `hl` to reduce the goal to its premises. Rewrite using `[← Fin.rev_rev i, h, Fin.rev_zero]`.

Establish `h2 : i.rev ≠ Fin.last (m + 1)`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← Fin.rev_rev i, h, Fin.rev_last]`. Rewrite using `[if_neg h1, if_neg h2, if_neg h0, if_neg hl, neg_zero]`.

Rewrite using `[this, weylDim_hwt_eq, dimHar_comm]`. Rewrite using `[dif_neg hs]`. Establish `: lamAt (flatW (m + 1) A B) s = fun _ => (0 : ℤ)`. Unfold `lamAt`. Apply the tactic sequence `split_ifs <;> funext i <;> simp [flatW, hs]`.

Rewrite using `[this, weylDim_zero]`.
-/
theorem lamAt_flat {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (A B : TT → ℕ) (s : Fin n') :
    weylDim (m + 2) (lamAt (flatW (m + 1) A B) s) =
      if h : s ∈ TT then (dimHar (m + 1) (A ⟨s, h⟩) (B ⟨s, h⟩) : ℚ) else 1 := by
  by_cases hs : s ∈ TT
  · rw [dif_pos hs]
    unfold lamAt
    split_ifs with he
    · have : flatW (m + 1) A B s = hwt m (A ⟨s, hs⟩) (B ⟨s, hs⟩) := by
        funext i
        rw [hwt_apply]
        simp [flatW, hs]
      rw [this, weylDim_hwt_eq]
    · have : (fun i : Fin (m + 1 + 1) => -flatW (m + 1) A B s i.rev) = hwt m (B ⟨s, hs⟩) (A ⟨s, hs⟩) := by
        funext i
        rw [hwt_apply]
        simp only [flatW, hs, dif_pos]
        by_cases h0 : i = 0
        · subst h0
          rw [Fin.rev_zero, if_neg (last_ne_zero' m)]
          simp
        · by_cases hl : i = Fin.last (m + 1)
          · subst hl
            rw [Fin.rev_last]
            simp [last_ne_zero' m]
          · have h1 : i.rev ≠ 0 := by
              intro h
              apply hl
              rw [← Fin.rev_rev i, h, Fin.rev_zero]
            have h2 : i.rev ≠ Fin.last (m + 1) := by
              intro h
              apply h0
              rw [← Fin.rev_rev i, h, Fin.rev_last]
            rw [if_neg h1, if_neg h2, if_neg h0, if_neg hl, neg_zero]
      rw [this, weylDim_hwt_eq, dimHar_comm]
  · rw [dif_neg hs]
    have : lamAt (flatW (m + 1) A B) s = fun _ => (0 : ℤ) := by
      unfold lamAt
      split_ifs <;> funext i <;> simp [flatW, hs]
    rw [this, weylDim_zero]

/- English proof (translation)
Rewrite using `[h3 K n nu hnu]`. Unfold `weylDim`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem finrank_weyl (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (n : ℕ)
    (nu : Fin n → ℕ) (hnu : Antitone nu) :
    (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K n n nu) : ℚ) = weylDim n (fun i => (nu i : ℤ)) := by
  rw [h3 K n nu hnu]
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

/- English proof (translation)
Establish `hq : (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (letterWt (m + 1) d vec))) : ℚ) = (dimPol (m + 1) d : ℚ)`. Consider the cases of `vec with`. Consider the case `true`. Establish `hnu : nuOf (letterWt (m + 1) d true) = fun i => if i = 0 then d else 0`. Use function extensionality and compare the values at `i`.

Simplify using `only [nuOf, letterWt, if_true, if_neg (last_ne_zero' m), sub_zero]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hanti : Antitone (nuOf (letterWt (m + 1) d true))`. Rewrite using `[hnu]`. Introduce `i j hij`.

Simplify using `only`. Apply the tactic sequence `split_ifs with h1 h2 <;> first | omega | skip`. Conclude with `absurd (Fin.le_zero_iff.1 (h1 ▸ hij)) h2`. Rewrite using `[finrank_weyl D h3 K _ _ hanti, ← weylDim_vec]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `hwt_apply m d 0 i` as an intermediate fact. Unfold `hwt at this`. Simplify using `only [Nat.cast_zero, neg_zero] at this`. Rewrite using `[this, hnu]`.

Apply the tactic sequence `by_cases h : i = 0 <;> simp [h]`. Consider the case `false`. Establish `hnu : nuOf (letterWt (m + 1) d false) = fun i => if i = Fin.last (m + 1) then 0 else d`. Use function extensionality and compare the values at `i`. Simplify using `only [nuOf, letterWt, Bool.false_eq_true, if_false, if_true]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hanti : Antitone (nuOf (letterWt (m + 1) d false))`. Rewrite using `[hnu]`. Introduce `i j hij`. Simplify using `only`.

Distinguish the cases in `hj : j = Fin.last (m + 1)`. Rewrite using `[if_pos hj]`. Conclude with `Nat.zero_le _`. Establish `hi : i ≠ Fin.last (m + 1)` using `fun h => hj (le_antisymm (Fin.le_last _) (h ▸ hij))`. Rewrite using `[if_neg hj, if_neg hi]`.

Rewrite using `[finrank_weyl D h3 K _ _ hanti, ← weylDim_cov]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[cov_apply, hnu]`. Apply the tactic sequence `by_cases h : i = Fin.last (m + 1) <;> simp [h]`.

Conclude with `hq` after adjusting the coercions.
-/
theorem finrank_letter (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (m d : ℕ)
    (vec : Bool) :
    Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (letterWt (m + 1) d vec))) =
      dimPol (m + 1) d := by
  have hq : (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (letterWt (m + 1) d vec))) : ℚ) =
      (dimPol (m + 1) d : ℚ) := by
    cases vec with
    | true =>
      have hnu : nuOf (letterWt (m + 1) d true) = fun i => if i = 0 then d else 0 := by
        funext i
        simp only [nuOf, letterWt, if_true, if_neg (last_ne_zero' m), sub_zero]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt (m + 1) d true)) := by
        rw [hnu]
        intro i j hij
        simp only
        split_ifs with h1 h2 <;> first | omega | skip
        exact absurd (Fin.le_zero_iff.1 (h1 ▸ hij)) h2
      rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_vec]
      congr 1
      funext i
      have := hwt_apply m d 0 i
      unfold hwt at this
      simp only [Nat.cast_zero, neg_zero] at this
      rw [this, hnu]
      by_cases h : i = 0 <;> simp [h]
    | false =>
      have hnu : nuOf (letterWt (m + 1) d false) = fun i => if i = Fin.last (m + 1) then 0 else d := by
        funext i
        simp only [nuOf, letterWt, Bool.false_eq_true, if_false, if_true]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt (m + 1) d false)) := by
        rw [hnu]
        intro i j hij
        simp only
        by_cases hj : j = Fin.last (m + 1)
        · rw [if_pos hj]; exact Nat.zero_le _
        · have hi : i ≠ Fin.last (m + 1) := fun h => hj (le_antisymm (Fin.le_last _) (h ▸ hij))
          rw [if_neg hj, if_neg hi]
      rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_cov]
      congr 1
      funext i
      rw [cov_apply, hnu]
      by_cases h : i = Fin.last (m + 1) <;> simp [h]
  exact_mod_cast hq

/- English proof (translation)
Introduce `p n' R m hm TT A B`. Take `⟨m, rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by omega⟩`. Use `R.charZero` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Unfold `dimHH VHH`.

Rewrite using `[finrank_tensor, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_bool]`. Unfold `hhWt`. Rewrite using `[finrank_letter D h3, finrank_letter D h3]`.

Establish `hA : ex A s.val = A s` using `by unfold ex; rw [dif_pos s.2]`. Establish `hB : ex B s.val = B s` using `by unfold ex; rw [dif_pos s.2]`. Unfold `hhDeg`. Simplify using `only [if_true, Bool.false_eq_true, if_false, hA, hB]`. Use `split_ifs`.

Both sides reduce to the same expression. Conclude with `mul_comm _ _`. Establish `h` using `hW R.Kf n' (m + 1) (flatW (m + 1) A B) (flatW_dom m A B)`. Establish `h2 : ((dimV R.Kf (flatW (m + 1) A B) : ℕ) : ℚ) = ∏ s : Fin n', weylDim (m + 2) (lamAt (flatW (m + 1) A B) s)`. Rewrite using `[h]`.

Unfold `weylDim`. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [lamAt_flat] at h2`.

Rewrite `h2` using `[prod_tops TT (fun s => (dimHar (m + 1) (A s) (B s) : ℚ))]`. Conclude with `h2` after adjusting the coercions.
-/
theorem restDims_of (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (hW : WeylV) : RestDims := by
  classical
  intro p n' R m hm TT A B
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have := R.charZero
  constructor
  · unfold dimHH VHH
    rw [finrank_tensor, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Fintype.prod_bool]
    unfold hhWt
    rw [finrank_letter D h3, finrank_letter D h3]
    have hA : ex A s.val = A s := by unfold ex; rw [dif_pos s.2]
    have hB : ex B s.val = B s := by unfold ex; rw [dif_pos s.2]
    unfold hhDeg
    simp only [if_true, Bool.false_eq_true, if_false, hA, hB]
    split_ifs
    · rfl
    · exact mul_comm _ _
  · have h := hW R.Kf n' (m + 1) (flatW (m + 1) A B) (flatW_dom m A B)
    have h2 : ((dimV R.Kf (flatW (m + 1) A B) : ℕ) : ℚ) =
        ∏ s : Fin n', weylDim (m + 2) (lamAt (flatW (m + 1) A B) s) := by
      rw [h]
      unfold weylDim
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      push_cast
      rfl
    simp only [lamAt_flat] at h2
    rw [prod_tops TT (fun s => (dimHar (m + 1) (A s) (B s) : ℚ))] at h2
    exact_mod_cast h2

end Formalism.MainNotions.flipOneThree.Pf

end
