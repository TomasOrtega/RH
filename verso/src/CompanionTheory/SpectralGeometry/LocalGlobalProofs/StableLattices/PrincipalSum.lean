import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PrinSumP

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)

variable {A : Type*} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `f g d _ hd`. Establish `hd0 : d = 0` using `Fin.fin_one_eq_zero d`.

Substitute `hd0` using the available equality. Simplify using `[hd]`. Consider the case `succ m ih`. Introduce `f g d h hd`. Rewrite using `[List.ofFn_succ (f := f), List.ofFn_succ (f := g), List.prod_cons, List.prod_cons]`.

Proceed by induction on `d using Fin.cases with`. Consider the case `zero`. Establish `ht : (fun i : Fin (m + 1) => f i.succ) = fun i => g i.succ`. Use function extensionality and compare the values at `fun i => h _ (Fin.succ_ne_zero i)`. Rewrite using `[ht, hd, add_mul, one_mul, add_sub_cancel_left]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `[ht, congrFun ht i]`. Consider the case `succ e`. Establish `h0 : f 0 = g 0` using `h 0 (Fin.succ_ne_zero e).symm`.

Establish `key` using `ih (fun i => f i.succ) (fun i => g i.succ) e (fun j hj => h _ (fun hh => hj (Fin.succ_injective _ hh))) hd`. Rewrite using `[← h0, ← mul_sub, key, List.ofFn_succ, List.prod_cons]`. Use `congr 2`. Simplify using `[Function.comp_def, Fin.succ_succAbove_succ]`.
-/
theorem prod_ofFn_sub : ∀ (m : ℕ) (f g : Fin (m + 1) → A) (d : Fin (m + 1)),
    (∀ j, j ≠ d → f j = g j) → f d = g d + 1 →
    (List.ofFn f).prod - (List.ofFn g).prod = (List.ofFn (f ∘ d.succAbove)).prod := by
  intro m
  induction m with
  | zero =>
    intro f g d _ hd
    have hd0 : d = 0 := Fin.fin_one_eq_zero d
    subst hd0
    simp [hd]
  | succ m ih =>
    intro f g d h hd
    rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g), List.prod_cons, List.prod_cons]
    induction d using Fin.cases with
    | zero =>
      have ht : (fun i : Fin (m + 1) => f i.succ) = fun i => g i.succ :=
        funext fun i => h _ (Fin.succ_ne_zero i)
      rw [ht, hd, add_mul, one_mul, add_sub_cancel_left]
      congr 2
      funext i
      simp [ht, congrFun ht i]
    | succ e =>
      have h0 : f 0 = g 0 := h 0 (Fin.succ_ne_zero e).symm
      have key := ih (fun i => f i.succ) (fun i => g i.succ) e
        (fun j hj => h _ (fun hh => hj (Fin.succ_injective _ hh))) hd
      rw [← h0, ← mul_sub, key, List.ofFn_succ, List.prod_cons]
      congr 2
      simp [Function.comp_def, Fin.succ_succAbove_succ]

def colDet {n : ℕ} (E : Fin n → Fin n → A) (c : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin n => capEntry E (c j) (σ j) j).prod

/- English proof (translation)
The claim follows from `add_comm _ _`.
-/
theorem Tm_eq_capEntry {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    Tm E u a b = capEntry E u a b := add_comm _ _

/- English proof (translation)
Unfold `qdet qminor colDet`. Use `sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← zsmul_eq_mul]`. Use `congr 2`. Simplify using `only [Tm_eq_capEntry, id]`.
-/
theorem qdet_eq_colDet {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    qdet E u = colDet E (fun j => u - ((j : ℕ) : ℂ)) := by
  unfold qdet qminor colDet
  refine sum_congr rfl fun σ _ => ?_
  rw [← zsmul_eq_mul]
  congr 2
  simp only [Tm_eq_capEntry, id]

def ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquiv' d).symm.permCongr (Equiv.Perm.decomposeOption.symm (none, τ))

/- English proof (translation)
Simplify using `[ins, Equiv.permCongr_apply]`.
-/
theorem ins_self {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : ins d τ d = d := by
  simp [ins, Equiv.permCongr_apply]

/- English proof (translation)
Simplify using `[ins, Equiv.permCongr_apply]`.
-/
theorem ins_succAbove {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    ins d τ (d.succAbove i) = d.succAbove (τ i) := by
  simp [ins, Equiv.permCongr_apply]

/- English proof (translation)
Simplify using `[ins, Equiv.Perm.decomposeOption_symm_sign]`.
-/
theorem sign_ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ins d τ) = Equiv.Perm.sign τ := by
  simp [ins, Equiv.Perm.decomposeOption_symm_sign]

/- English proof (translation)
Introduce `τ τ' h`. Use extensionality with `i`. Use `congrArg (fun s : Equiv.Perm (Fin (m + 1)) => s (d.succAbove i)) h` as an intermediate fact. Simplify using `only [ins_succAbove] at this`. Conclude with `congrArg Fin.val (Fin.succAbove_right_injective this)`.
-/
theorem ins_injective {m : ℕ} (d : Fin (m + 1)) : Function.Injective (ins d) := by
  intro τ τ' h
  ext i
  have := congrArg (fun s : Equiv.Perm (Fin (m + 1)) => s (d.succAbove i)) h
  simp only [ins_succAbove] at this
  exact congrArg Fin.val (Fin.succAbove_right_injective this)

/- English proof (translation)
Use `set s : Equiv.Perm (Option (Fin m)) := (finSuccEquiv' d).permCongr σ with hs`. Establish `hnone : s none = none`. Simplify using `[hs, Equiv.permCongr_apply, h]`. Take `⟨⟨o, τ⟩, hq⟩` from `Equiv.Perm.decomposeOption.symm.surjective s`. Establish `ho : o = none`.

Rewrite using `[← hnone, ← hq]`. Simplify using the standard rewrite rules. Substitute `ho` using the available equality. Use `⟨τ, ?_⟩` and prove the remaining obligations. Unfold `ins`.

Rewrite using `[hq, hs]`. Use extensionality with `x`. Simplify using `[Equiv.permCongr_apply]`.
-/
theorem exists_ins {m : ℕ} (d : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) (h : σ d = d) :
    ∃ τ, ins d τ = σ := by
  set s : Equiv.Perm (Option (Fin m)) := (finSuccEquiv' d).permCongr σ with hs
  have hnone : s none = none := by
    simp [hs, Equiv.permCongr_apply, h]
  obtain ⟨⟨o, τ⟩, hq⟩ := Equiv.Perm.decomposeOption.symm.surjective s
  have ho : o = none := by
    rw [← hnone, ← hq]
    simp
  subst ho
  refine ⟨τ, ?_⟩
  unfold ins
  rw [hq, hs]
  ext x
  simp [Equiv.permCongr_apply]

/- English proof (translation)
Apply the tactic sequence `have each : ∀ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c j) (σ j) j).prod - ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c' j) (σ j) j).prod = if σ d = d then ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn ((f …`. Introduce `σ`. Rewrite using `[← smul_sub]`. Use `split_ifs with hσ`. Apply the tactic sequence `rw [prod_ofFn_sub m _ (fun j => capEntry E (c' j) (σ j) j) d]`.

Introduce `j hj`. Simplify using `only [h j hj]`. Simplify using `only [capEntry, hσ, if_true, hd, map_add, map_one]`. Normalize the expressions using the abelian group laws. Apply the tactic sequence `have : (fun j => capEntry E (c j) (σ j) j) = fun j => capEntry E (c' j) (σ j) j := by`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = d`. Substitute `hj` using the available equality. Simplify using `[capEntry, hσ]`. Simplify using `only [h j hj]`.

Rewrite using `[this, sub_self, smul_zero]`. Unfold `colDet`. Rewrite using `[← sum_sub_distrib, sum_congr rfl fun σ _ => each σ, ← sum_filter]`. Use `symm`. Use `sum_bij (fun τ _ => ins d τ) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `τ _`. Simplify using `[ins_self]`. Introduce `τ _ τ' _ hh`. Conclude with `ins_injective d hh`. Introduce `σ hσ`.

Take `⟨τ, rfl⟩` from `exists_ins d σ (by simpa using hσ)`. Conclude with `⟨τ, mem_univ _, rfl⟩`. Introduce `τ _`. Rewrite using `[sign_ins]`. Use `congr 2`.

Use `congrArg List.ofFn (funext fun i => ?_)` and prove the remaining obligations. Simplify using `[ins_succAbove]`.
-/
theorem colDet_sub {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (c c' : Fin (m + 1) → ℂ)
    (d : Fin (m + 1)) (h : ∀ j, j ≠ d → c j = c' j) (hd : c d = c' d + 1) :
    colDet E c - colDet E c' = ∑ τ : Equiv.Perm (Fin m), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      (List.ofFn fun i : Fin m =>
        capEntry E (c (d.succAbove i)) (d.succAbove (τ i)) (d.succAbove i)).prod := by
  have each : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c j) (σ j) j).prod -
        ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c' j) (σ j) j).prod =
      if σ d = d then ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (List.ofFn ((fun j => capEntry E (c j) (σ j) j) ∘ d.succAbove)).prod else 0 := by
    intro σ
    rw [← smul_sub]
    split_ifs with hσ
    · rw [prod_ofFn_sub m _ (fun j => capEntry E (c' j) (σ j) j) d]
      · intro j hj
        simp only [h j hj]
      · simp only [capEntry, hσ, if_true, hd, map_add, map_one]
        abel
    · have : (fun j => capEntry E (c j) (σ j) j) = fun j => capEntry E (c' j) (σ j) j := by
        funext j
        by_cases hj : j = d
        · subst hj
          simp [capEntry, hσ]
        · simp only [h j hj]
      rw [this, sub_self, smul_zero]
  unfold colDet
  rw [← sum_sub_distrib, sum_congr rfl fun σ _ => each σ, ← sum_filter]
  symm
  refine sum_bij (fun τ _ => ins d τ) ?_ ?_ ?_ ?_
  · intro τ _
    simp [ins_self]
  · intro τ _ τ' _ hh
    exact ins_injective d hh
  · intro σ hσ
    obtain ⟨τ, rfl⟩ := exists_ins d σ (by simpa using hσ)
    exact ⟨τ, mem_univ _, rfl⟩
  · intro τ _
    rw [sign_ins]
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    simp [ins_succAbove]

def hyb {n : ℕ} (x : ℂ) (k : ℕ) (j : Fin n) : ℂ :=
  if (j : ℕ) < k then x - 1 - ((j : ℕ) : ℂ) else x - ((j : ℕ) : ℂ)

/- English proof (translation)
Rewrite using `[colDet_sub E _ _ d]`. Unfold `cminor`. Use `sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 2`. Use `congrArg List.ofFn (funext fun i => ?_)` and prove the remaining obligations.

Use `congr 1`. Unfold `hyb`. Break down `lt_or_ge (i : ℕ) (d : ℕ) with hi | hi` into its components or cases. Establish `e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hi)]`.

Simplify using the standard rewrite rules. Rewrite using `[e, if_pos hi]`. Establish `e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i + 1`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hi)]`. Simplify using the standard rewrite rules.

Rewrite using `[e, if_neg (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `j hj`. Establish `: (j : ℕ) ≠ d` using `fun hh => hj (Fin.ext hh)`.

Unfold `hyb`. Distinguish the cases in `h1 : (j : ℕ) < d`. Rewrite using `[if_pos h1, if_pos (by omega)]`. Rewrite using `[if_neg h1, if_neg (by omega)]`. Unfold `hyb`.

Rewrite using `[if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hyb_step {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) (d : Fin (m + 1)) :
    colDet E (hyb x (d : ℕ)) - colDet E (hyb x ((d : ℕ) + 1)) =
      cminor E d.succAbove d.succAbove (x - 1) := by
  rw [colDet_sub E _ _ d]
  · unfold cminor
    refine sum_congr rfl fun τ _ => ?_
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    congr 1
    unfold hyb
    rcases lt_or_ge (i : ℕ) (d : ℕ) with hi | hi
    · have e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hi)]
        simp
      rw [e, if_pos hi]
    · have e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hi)]
        simp
      rw [e, if_neg (by omega)]
      push_cast
      ring
  · intro j hj
    have : (j : ℕ) ≠ d := fun hh => hj (Fin.ext hh)
    unfold hyb
    by_cases h1 : (j : ℕ) < d
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · unfold hyb
    rw [if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
    ring

/- English proof (translation)
Establish `h0 : qdet E x = colDet E (hyb x 0)`. Rewrite using `[qdet_eq_colDet]`. Use `congr 1`. Establish `h1 : qdet E (x - 1) = colDet E (hyb x (m + 1))`. Rewrite using `[qdet_eq_colDet]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `[hyb, j.2]`. Rewrite using `[h0, h1, ← sum_congr rfl fun d _ => hyb_step E x d, Fin.sum_univ_eq_sum_range (fun k => colDet E (hyb x k) - colDet E (hyb x (k + 1))) (m + 1), sum_range_sub']`.
-/
theorem sum_principal {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) :
    ∑ d : Fin (m + 1), cminor E d.succAbove d.succAbove (x - 1) = qdet E x - qdet E (x - 1) := by
  have h0 : qdet E x = colDet E (hyb x 0) := by
    rw [qdet_eq_colDet]
    congr 1
  have h1 : qdet E (x - 1) = colDet E (hyb x (m + 1)) := by
    rw [qdet_eq_colDet]
    congr 1
    funext j
    simp [hyb, j.2]
  rw [h0, h1, ← sum_congr rfl fun d _ => hyb_step E x d,
    Fin.sum_univ_eq_sum_range (fun k => colDet E (hyb x k) - colDet E (hyb x (k + 1))) (m + 1),
    sum_range_sub']

/- English proof (translation)
Introduce `m M _ _ E _ x`. Conclude with `sum_principal E x`.
-/
theorem prinSum : CompanionTheory.RgExh.Hk.PrinSum := by
  intro m M _ _ E _ x
  exact sum_principal E x

end GlobalTheory.CompanionTheory.PrinSumP
