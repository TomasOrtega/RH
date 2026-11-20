import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Comb

open MvPolynomial Finset Equiv

noncomputable section

open scoped Classical

variable {m : ℕ}

def pcnt {n : ℕ} (w : Fin n → Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = i)).card

def IsLattice {n : ℕ} (w : Fin n → Fin m) : Prop :=
  ∀ t ≤ n, ∀ i j : Fin m, i ≤ j → pcnt w t j ≤ pcnt w t i

def latticeWords (n : ℕ) (lam : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  univ.filter (fun w => IsLattice w ∧ ∀ i, pcnt w n i = lam i)

/- English proof (translation)
Unfold `pcnt`. Rewrite using `[Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]`. Rewrite using `[if_neg (by omega), add_zero]`.
-/
theorem pcnt_castSucc_snoc {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) t i = pcnt w t i := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_neg (by omega), add_zero]

/- English proof (translation)
Unfold `pcnt`. Rewrite using `[Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]`. Use `congr 1`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Use `s.isLt` as an intermediate fact. Apply the tactic sequence `by_cases h : w s = i <;> simp [h, this, Nat.lt_succ_of_lt this]`. Simplify using the standard rewrite rules.
-/
theorem pcnt_snoc_last {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) (n + 1) i = pcnt w n i + if a = i then 1 else 0 := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have := s.isLt
    by_cases h : w s = i <;> simp [h, this, Nat.lt_succ_of_lt this]
  · simp

/- English proof (translation)
Unfold `pcnt`. Simplify using the standard rewrite rules.
-/
theorem pcnt_zero {n : ℕ} (w : Fin n → Fin m) (i : Fin m) : pcnt w 0 i = 0 := by
  unfold pcnt; simp

/- English proof (translation)
Unfold `pcnt`. Conclude with `Finset.card_le_card (fun s => by simp only [mem_filter, mem_univ, true_and]; omega)`.
-/
theorem pcnt_le_of_le {n : ℕ} (w : Fin n → Fin m) {t t' : ℕ} (h : t ≤ t') (i : Fin m) :
    pcnt w t i ≤ pcnt w t' i := by
  unfold pcnt
  exact Finset.card_le_card (fun s => by simp only [mem_filter, mem_univ, true_and]; omega)

/- English proof (translation)
Unfold `pcnt`. Rewrite using `[← Finset.card_biUnion]`. Establish `: (univ : Finset (Fin m)).biUnion (fun i => univ.filter (fun s : Fin n => (s : ℕ) < n ∧ w s = i)) = univ`. Use extensionality with `s`. Simplify using the standard rewrite rules.

Rewrite using `[this, Finset.card_univ, Fintype.card_fin]`. Introduce `i _ j _ hij`. Rewrite using `[Function.onFun, Finset.disjoint_filter]`. Introduce and unpack `s _ ⟨_, h1⟩ ⟨_, h2⟩`. Conclude with `hij (h1 ▸ h2)`.
-/
theorem sum_pcnt {n : ℕ} (w : Fin n → Fin m) : ∑ i, pcnt w n i = n := by
  unfold pcnt
  rw [← Finset.card_biUnion]
  · have : (univ : Finset (Fin m)).biUnion (fun i => univ.filter (fun s : Fin n => (s : ℕ) < n ∧ w s = i))
        = univ := by
      ext s; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    rintro s _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hij (h1 ▸ h2)

/- English proof (translation)
Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[Function.update_of_ne (Ne.symm hai), hai]`.
-/
theorem update_pred_sub (lam : Fin m → ℕ) (a i : Fin m) (h : 1 ≤ lam a) :
    Function.update lam a (lam a - 1) i + (if a = i then 1 else 0) = lam i := by
  by_cases hai : a = i
  · subst hai; simp; omega
  · simp [Function.update_of_ne (Ne.symm hai), hai]

/- English proof (translation)
Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ) (fun _ _ => mem_univ _)]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with ha`. Use `Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `w hw`.

Simplify using `only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢`. Take `⟨⟨hlat, hcont⟩, hlast⟩` from `hw`. Establish `hw' : w = Fin.snoc (Fin.init w) a`. Rewrite using `[← hlast]`. Conclude with `(Fin.snoc_init_self w).symm`.

Use `⟨fun t ht i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `hlat t (by omega) i j hij` as an intermediate fact. Rewrite `this` using `[hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht]`. Then use the resulting hypothesis. Use `hcont i` as an intermediate fact. Rewrite `this` using `[hw', pcnt_snoc_last]`.

Establish `h2` using `update_pred_sub lam a i ha`. Use linear arithmetic over natural numbers and integers. Introduce `w hw`. Simplify using `only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢`. Take `⟨hlat, hcont⟩` from `hw`.

Use `⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge t (n + 1) with htn | htn` into its components or cases. Rewrite using `[pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]`. Conclude with `hlat t (by omega) i j hij`. Establish `ht' : t = n + 1` using `by omega`.

Substitute `ht'` using the available equality. Rewrite using `[pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha, update_pred_sub lam a j ha]`. Conclude with `hlam hij`. Rewrite using `[pcnt_snoc_last, hcont, update_pred_sub lam a i ha]`. Introduce `w hw`.

Simplify using `only [coe_filter, Set.mem_ofPred_eq] at hw`. Rewrite using `[← hw.2]`. Conclude with `Fin.snoc_init_self w`. Introduce `w hw`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `w hw hlast`. Simplify using `only [latticeWords, mem_filter, mem_univ, true_and] at hw`. Use `hw.2 a` as an intermediate fact. Establish `h1 : 1 ≤ pcnt w (n + 1) a`.

Unfold `pcnt`. Conclude with `Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_latticeWords_succ (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨⟨hlat, hcont⟩, hlast⟩ := hw
      have hw' : w = Fin.snoc (Fin.init w) a := by
        rw [← hlast]; exact (Fin.snoc_init_self w).symm
      refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
      · have := hlat t (by omega) i j hij
        rwa [hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht] at this
      · have := hcont i
        rw [hw', pcnt_snoc_last] at this
        have h2 := update_pred_sub lam a i ha
        omega
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hlat, hcont⟩ := hw
      refine ⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩
      · rcases Nat.lt_or_ge t (n + 1) with htn | htn
        · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
          exact hlat t (by omega) i j hij
        · have ht' : t = n + 1 := by omega
          subst ht'
          rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha,
            update_pred_sub lam a j ha]
          exact hlam hij
      · rw [pcnt_snoc_last, hcont, update_pred_sub lam a i ha]
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      rw [← hw.2]; exact Fin.snoc_init_self w
    · intro w hw
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hlast
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
    have := hw.2 a
    have h1 : 1 ≤ pcnt w (n + 1) a := by
      unfold pcnt
      exact Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩
    omega

/- English proof (translation)
Rewrite using `[Finset.eq_empty_iff_forall_notMem]`. Introduce `w hw`. Simplify using `only [latticeWords, mem_filter, mem_univ, true_and] at hw`. Apply `h` to reduce the goal to its premises. Rewrite using `[← sum_pcnt w]`.

Conclude with `Finset.sum_congr rfl fun i _ => (hw.2 i).symm`.
-/
theorem latticeWords_eq_empty_of_sum_ne (n : ℕ) (lam : Fin m → ℕ) (h : ∑ i, lam i ≠ n) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  rw [← sum_pcnt w]
  exact Finset.sum_congr rfl fun i _ => (hw.2 i).symm

/- English proof (translation)
Rewrite using `[Finset.eq_empty_iff_forall_notMem]`. Introduce `w hw`. Simplify using `only [latticeWords, mem_filter, mem_univ, true_and] at hw`. Apply `h` to reduce the goal to its premises. Introduce `i j hij`.

Rewrite using `[← hw.2 i, ← hw.2 j]`. Conclude with `hw.1 n le_rfl i j hij`.
-/
theorem latticeWords_eq_empty_of_not_antitone (n : ℕ) (lam : Fin m → ℕ) (h : ¬ Antitone lam) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  intro i j hij
  rw [← hw.2 i, ← hw.2 j]
  exact hw.1 n le_rfl i j hij

end

end GroundTheory.Heights₂.Heights.RestTerms.Comb
