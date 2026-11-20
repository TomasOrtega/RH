import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.FarRegularityLevels

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (rhoC rhoN lowK nsq vNormSq)

variable {n : ℕ}

/- English proof (translation)
Unfold `rhoN rhoC`. Establish `kgt` using `Finset.card_filter_add_card_filter_not (s := Ioi a) (fun b => ε b = ε a)`. Establish `e1 : (Ioi a).filter (fun b => ε b = ε a) = univ.filter (fun b => a < b ∧ ε b = ε a)`. Use extensionality with `b`. Simplify using the standard rewrite rules.

Establish `e2 : (Ioi a).filter (fun b => ¬ ε b = ε a) = univ.filter (fun b => a < b ∧ ε b ≠ ε a)`. Use extensionality with `b`. Simplify using the standard rewrite rules. Rewrite `kgt` using `[e1, e2, Fin.card_Ioi]`. Establish `klt` using `Finset.card_filter_add_card_filter_not (s := Iio a) (fun b => ε b = ε a)`.

Establish `e3 : (Iio a).filter (fun b => ε b = ε a) = univ.filter (fun b => b < a ∧ ε b = ε a)`. Use extensionality with `b`. Simplify using the standard rewrite rules. Establish `e4 : (Iio a).filter (fun b => ¬ ε b = ε a) = univ.filter (fun b => b < a ∧ ε b ≠ ε a)`. Use extensionality with `b`.

Simplify using the standard rewrite rules. Rewrite `klt` using `[e3, e4, Fin.card_Iio]`. Establish `ha` using `a.isLt`. Establish `kgt' : (univ.filter (fun b => a < b ∧ ε b = ε a)).card + (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card + (a : ℕ) + 1 = n` using `by omega`. Establish `rgt : ((univ.filter (fun b => a < b ∧ ε b = ε a)).card : ℝ) + ((univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card : ℝ) + ((a : ℕ) : ℝ) + 1 = n`.

Conclude with `kgt'` after adjusting the coercions. Establish `rlt : ((univ.filter (fun b => b < a ∧ ε b = ε a)).card : ℝ) + ((univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card : ℝ) = ((a : ℕ) : ℝ)`. Conclude with `klt` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_sum (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  unfold rhoN rhoC
  have kgt := Finset.card_filter_add_card_filter_not (s := Ioi a) (fun b => ε b = ε a)
  have e1 : (Ioi a).filter (fun b => ε b = ε a) = univ.filter (fun b => a < b ∧ ε b = ε a) := by
    ext b; simp
  have e2 : (Ioi a).filter (fun b => ¬ ε b = ε a) = univ.filter (fun b => a < b ∧ ε b ≠ ε a) := by
    ext b; simp
  rw [e1, e2, Fin.card_Ioi] at kgt
  have klt := Finset.card_filter_add_card_filter_not (s := Iio a) (fun b => ε b = ε a)
  have e3 : (Iio a).filter (fun b => ε b = ε a) = univ.filter (fun b => b < a ∧ ε b = ε a) := by
    ext b; simp
  have e4 : (Iio a).filter (fun b => ¬ ε b = ε a) = univ.filter (fun b => b < a ∧ ε b ≠ ε a) := by
    ext b; simp
  rw [e3, e4, Fin.card_Iio] at klt
  have ha := a.isLt
  have kgt' : (univ.filter (fun b => a < b ∧ ε b = ε a)).card +
      (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card + (a : ℕ) + 1 = n := by omega
  have rgt : ((univ.filter (fun b => a < b ∧ ε b = ε a)).card : ℝ) +
      ((univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card : ℝ) + ((a : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast kgt'
  have rlt : ((univ.filter (fun b => b < a ∧ ε b = ε a)).card : ℝ) +
      ((univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card : ℝ) = ((a : ℕ) : ℝ) := by
    exact_mod_cast klt
  linarith

/- English proof (translation)
Unfold `rhoC`. Establish `h1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n`. Use `card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)` as an intermediate fact. Rewrite `this` using `[card_univ, Fintype.card_fin]`. Conclude with `this` after adjusting the coercions.

Establish `h2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n`. Use `card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)` as an intermediate fact. Rewrite `this` using `[card_univ, Fintype.card_fin]`. Conclude with `this` after adjusting the coercions. Establish `h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ)` using `Nat.cast_nonneg _`.

Establish `h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ)` using `Nat.cast_nonneg _`. Establish `h5 : (0 : ℝ) ≤ (n : ℝ)` using `Nat.cast_nonneg _`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem abs_rhoC_le (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by
  unfold rhoC
  have h1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by
    have := card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by
    have := card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), by unfold rhoC; push_cast; ring⟩`.
-/
theorem two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, 2 * rhoC ε a = m :=
  ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), by
    unfold rhoC; push_cast; ring⟩

/- English proof (translation)
Unfold `rhoC`. Establish `h1 : (univ.filter fun c => b < c ∧ ε c = ε b).card < (univ.filter fun c => a < c ∧ ε c = ε a).card`. Apply `card_lt_card` to reduce the goal to its premises. Rewrite using `[ssubset_iff_of_subset]`. Conclude with `⟨b, by simp [hab, he], by simp⟩`.

Introduce `c hc`. Simplify using `only [mem_filter, mem_univ, true_and] at hc ⊢`. Conclude with `⟨hab.trans hc.1, hc.2.trans he.symm⟩`. Establish `h2 : (univ.filter fun c => c < a ∧ ε c = ε a).card ≤ (univ.filter fun c => c < b ∧ ε c = ε b).card`. Apply `card_le_card` to reduce the goal to its premises.

Introduce `c hc`. Simplify using `only [mem_filter, mem_univ, true_and] at hc ⊢`. Conclude with `⟨hc.1.trans hab, hc.2.trans he⟩`. Establish `h1' : ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) < ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ)` using `by exact_mod_cast h1`. Establish `h2' : ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) ≤ ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ)` using `by exact_mod_cast h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rhoC_lt (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) : rhoC ε b < rhoC ε a := by
  unfold rhoC
  have h1 : (univ.filter fun c => b < c ∧ ε c = ε b).card < (univ.filter fun c => a < c ∧ ε c = ε a).card := by
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · exact ⟨b, by simp [hab, he], by simp⟩
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact ⟨hab.trans hc.1, hc.2.trans he.symm⟩
  have h2 : (univ.filter fun c => c < a ∧ ε c = ε a).card ≤ (univ.filter fun c => c < b ∧ ε c = ε b).card := by
    apply card_le_card
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.trans hab, hc.2.trans he⟩
  have h1' : ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) <
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) ≤
      ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) := by exact_mod_cast h2
  linarith

open Classical in

def levS (y : ℕ → ℝ) (L : ℝ) (m : ℕ) : ℕ := ((range m).filter fun i => L ≤ y i - y (i + 1)).card

/- English proof (translation)
Introduce `a b hab`. Conclude with `card_le_card (filter_subset_filter _ (range_mono hab))`.
-/
theorem levS_mono (y : ℕ → ℝ) (L : ℝ) : Monotone (levS y L) := by
  classical
  intro a b hab
  exact card_le_card (filter_subset_filter _ (range_mono hab))

/- English proof (translation)
Take `⟨i, hi, hi'⟩` from `Finset.exists_mem_notMem_of_card_lt_card h`. Simplify using `only [mem_filter, mem_range, not_and] at hi hi'`. Establish `hai : a ≤ i`. Assume the negation of the conclusion as `hc`. Conclude with `hi' (by omega) hi.2`.

Establish `h1 : y i ≤ y a` using `hy hai`. Establish `h2 : y b ≤ y (i + 1)` using `hy (by omega)`. Combine the linear relations using `[hi.2]`.
-/
theorem levS_gap {y : ℕ → ℝ} (hy : Antitone y) {L : ℝ} {a b : ℕ} (h : levS y L a < levS y L b) :
    L ≤ y a - y b := by
  classical
  obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [mem_filter, mem_range, not_and] at hi hi'
  have hai : a ≤ i := by
    by_contra hc
    exact hi' (by omega) hi.2
  have h1 : y i ≤ y a := hy hai
  have h2 : y b ≤ y (i + 1) := hy (by omega)
  linarith [hi.2]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `h1 : levS y L a ≤ levS y L (a + m)` using `levS_mono y L (by omega)`. Establish `h2 : levS y L (a + m) ≤ levS y L (a + (m + 1))` using `levS_mono y L (by omega)`.

Establish `h3 : levS y L a = levS y L (a + m)` using `by omega`. Establish `h4` using `ih h3`. Establish `h5 : ¬ L ≤ y (a + m) - y (a + m + 1)`. Introduce `hP`. Establish `: levS y L (a + m) < levS y L (a + (m + 1))`.

Unfold `levS`. Apply `card_lt_card` to reduce the goal to its premises. Rewrite using `[ssubset_iff_of_subset]`. Conclude with `⟨a + m, by simp [hP], by simp⟩`. Conclude with `filter_subset_filter _ (range_mono (by omega))`.

Use linear arithmetic over natural numbers and integers. Use `push_neg at h5`. Establish `e : a + (m + 1) = a + m + 1` using `rfl`. Rewrite using `[e]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levS_flat (y : ℕ → ℝ) (L : ℝ) (a m : ℕ) (h : levS y L a = levS y L (a + m)) :
    y a - y (a + m) ≤ m * L := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : levS y L a ≤ levS y L (a + m) := levS_mono y L (by omega)
    have h2 : levS y L (a + m) ≤ levS y L (a + (m + 1)) := levS_mono y L (by omega)
    have h3 : levS y L a = levS y L (a + m) := by omega
    have h4 := ih h3
    have h5 : ¬ L ≤ y (a + m) - y (a + m + 1) := by
      intro hP
      have : levS y L (a + m) < levS y L (a + (m + 1)) := by
        unfold levS
        apply card_lt_card
        rw [ssubset_iff_of_subset]
        · exact ⟨a + m, by simp [hP], by simp⟩
        · exact filter_subset_filter _ (range_mono (by omega))
      omega
    push_neg at h5
    have e : a + (m + 1) = a + m + 1 := rfl
    rw [e]
    push_cast
    linarith

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩`. Consider the case `succ m`. Set `y : ℕ → ℝ` to `fun i => x ⟨min i m, by omega⟩`. Establish `hy : Antitone y`.

Introduce `i j hij`. Apply `hx` to reduce the goal to its premises. Simplify using `only [Fin.mk_le_mk]`. Use linear arithmetic over natural numbers and integers. Establish `hya : ∀ a : Fin (m + 1), y a = x a`.

Introduce `a`. Establish `ha` using `a.isLt`. Simplify using `only [y]`. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ a b : Fin (m + 1), a ≤ b → levS y L a = levS y L b → x a - x b ≤ ((m + 1 : ℕ) : ℝ) * L`. Introduce `a b hab h`. Establish `hab' : (a : ℕ) ≤ b` using `hab`.

Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hab'`. Rewrite `h` using `[hk]`. Establish `h1` using `levS_flat y L a k h`. Rewrite `h1` using `[← hk, hya, hya]`. Establish `h2 : (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ)`.

Use `b.isLt` as an intermediate fact. Conclude with `(by omega : k ≤ m + 1)` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities. Use `⟨fun a => levS y L a, fun a b hab => levS_mono y L hab, fun a b h => ?_, fun a b h => ?_⟩` and prove the remaining obligations. Use `levS_gap hy h` as an intermediate fact.

Rewrite `this` using `[hya, hya]`. Then use the resulting hypothesis. Break down `le_total a b with hab | hab` into its components or cases. Establish `h0 : 0 ≤ x a - x b` using `sub_nonneg.2 (hx hab)`. Rewrite using `[abs_of_nonneg h0]`. Conclude with `key a b hab h`.

Establish `h0 : 0 ≤ x b - x a` using `sub_nonneg.2 (hx hab)`. Rewrite using `[abs_sub_comm, abs_of_nonneg h0]`. Conclude with `key b a hab h.symm`.
-/
theorem exists_lev (x : Fin n → ℝ) (hx : Antitone x) {L : ℝ} (hL : 0 ≤ L) :
    ∃ lev : Fin n → ℕ, Monotone lev ∧ (∀ a b, lev a < lev b → L ≤ x a - x b) ∧
      ∀ a b, lev a = lev b → |x a - x b| ≤ n * L := by
  cases n with
  | zero => exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ m =>
    let y : ℕ → ℝ := fun i => x ⟨min i m, by omega⟩
    have hy : Antitone y := by
      intro i j hij
      apply hx
      simp only [Fin.mk_le_mk]
      omega
    have hya : ∀ a : Fin (m + 1), y a = x a := by
      intro a
      have ha := a.isLt
      simp only [y]
      congr 1
      apply Fin.ext
      simp only
      omega
    have key : ∀ a b : Fin (m + 1), a ≤ b → levS y L a = levS y L b → x a - x b ≤ ((m + 1 : ℕ) : ℝ) * L := by
      intro a b hab h
      have hab' : (a : ℕ) ≤ b := hab
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hab'
      rw [hk] at h
      have h1 := levS_flat y L a k h
      rw [← hk, hya, hya] at h1
      have h2 : (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        have := b.isLt
        exact_mod_cast (by omega : k ≤ m + 1)
      nlinarith
    refine ⟨fun a => levS y L a, fun a b hab => levS_mono y L hab, fun a b h => ?_, fun a b h => ?_⟩
    · have := levS_gap hy h
      rwa [hya, hya] at this
    · rcases le_total a b with hab | hab
      · have h0 : 0 ≤ x a - x b := sub_nonneg.2 (hx hab)
        rw [abs_of_nonneg h0]
        exact key a b hab h
      · have h0 : 0 ≤ x b - x a := sub_nonneg.2 (hx hab)
        rw [abs_sub_comm, abs_of_nonneg h0]
        exact key b a hab h.symm

/- English proof (translation)
Introduce `hLK hRn hUI hCO hFN n C δ hδ`. Take `⟨K2, hK2⟩` from `hUI n`. Take `⟨K1, hK1⟩` from `hCO n`. Take `⟨N₀, hN⟩` from `hFN n C δ (max K1 K2) hδ`. Use `⟨N₀, ?_⟩` and prove the remaining obligations.

Introduce `ε V _ _ E hE χ N hV hUn hLF hInt hSC hN₀ hsep hbd`. Take `⟨γ, u, hu, hKH, hMin, hγint, hdom⟩` from `hLK n ε V E hE hV hUn hLF hInt`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin n), Antitone (xv ε γ ∘ s) := by`. Use `⟨Tuple.sort (fun a => - xv ε γ a), fun a b hab => ?_⟩` and prove the remaining obligations. Use `Tuple.monotone_sort (fun a => - xv ε γ a) hab` as an intermediate fact.

Simplify using `only [Function.comp_apply] at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hblk : ∀ a b, a < b → ε a = ε b → xv ε γ b < xv ε γ a`. Introduce `a b hab he`. Establish `h1` using `hdom a b hab he`.

Establish `h2` using `rhoC_lt ε hab he`. Simplify using `only [xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hord : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b`. Introduce `a b hab he`.

Assume the negation of the conclusion as `hc`. Establish `hne : s a ≠ s b` using `fun h => hab.ne (s.injective h)`. Establish `hlt : s b < s a` using `lt_of_le_of_ne (not_lt.1 hc) hne.symm`. Establish `h1` using `hblk (s b) (s a) hlt he.symm`. Establish `h2` using `hs hab.le`.

Simplify using `only [Function.comp_apply] at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hE', hUn', hLF', hSC', hKH', hMin', hrho⟩` from `hRn n ε V E hE s hord`. Establish `hUn2` using `hUn' hUn`. Establish `hLF2` using `hLF' hLF`.

Establish `hSC2` using `hSC' χ hSC`. Establish `hKH2` using `(hKH' γ u).1 hKH`. Establish `hMin2` using `(hMin' γ).1 hMin`. Establish `hx' : xv (ε ∘ s) (γ ∘ s) = xv ε γ ∘ s`. Use function extensionality and compare the values at `a`.

Simplify using `only [xv, hrho, Pi.add_apply, Pi.smul_apply, Function.comp_apply]`. Establish `hanti : Antitone (xv (ε ∘ s) (γ ∘ s))` using `by rw [hx']; exact hs`. Establish `hLc : (0 : ℝ) ≤ Lc n` using `by unfold Lc; positivity`. Take `⟨lev, hmono, hgap, hspread⟩` from `exists_lev _ hanti hLc`. Establish `hG : Gapped (ε ∘ s) (γ ∘ s) lev (Lc n)` using `⟨hanti, hmono, hgap⟩`.

Establish `hKU : CompanionTheory.D.DSIC.KUnit (ε ∘ s) (fun a b => E (s a) (s b))`. Introduce `a b he x y`. Establish `h1` using `hUn2 a b x y`. Establish `h2 : Formalism.REAL.sgn (ε ∘ s) a b = 1` using `if_pos he`. Rewrite `h1` using `[h2]`.

Simplify using `using h1`. Take `⟨σ, hσ⟩` from `hK1 (ε ∘ s) (γ ∘ s) lev V (fun a b => E (s a) (s b)) hE' χ hG hKU hLF2 hMin2 hSC2 ⟨u, hu, hKH2⟩`. Establish `hcas` using `hK2 (ε ∘ s) V (fun a b => E (s a) (s b)) hE' χ (γ ∘ s) u hUn2 hSC2 hu hKH2`. Establish `hinj : Function.Injective lev`. Use `hN χ (xv (ε ∘ s) (γ ∘ s)) (rhoC (ε ∘ s)) lev σ N hanti hmono (abs_rhoC_le _) hspread ?_ ?_ hsep hbd hN₀` and prove the remaining obligations.

Conclude with `fun c => (hσ c).trans (le_max_left _ _)`. Establish `e : nsq (γ ∘ s + rhoC (ε ∘ s)) = ∑ a, (xv (ε ∘ s) (γ ∘ s) a - rhoC (ε ∘ s) a) ^ 2`. Unfold `PI.UpqRep.nsq PI.UpqRep.dot`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `hcas.trans (by linarith [le_max_right K1 K2])`. Establish `hstep : ∀ a b : Fin n, a < b → Lc n ≤ xv (ε ∘ s) (γ ∘ s) a - xv (ε ∘ s) (γ ∘ s) b`. Introduce `a b hab`.

Conclude with `hgap a b (lt_of_le_of_ne (hmono hab.le) fun h => hab.ne (hinj h))`. Establish `hLbig : (n : ℝ) + 1 ≤ Lc n`. Unfold `Lc`. Establish `h0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg _`. Use polynomial arithmetic with `[mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]`.

Establish `hlow : lowK (ε ∘ s) (xv (ε ∘ s) (γ ∘ s) - Formalism.QuantumDeterminants.rhoStd n) = γ ∘ s`. Use function extensionality and compare the values at `a`. Establish `h1` using `rho_sum (ε ∘ s) a`. Simplify using `only [lowK, xv, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨s, xv (ε ∘ s) (γ ∘ s) - Formalism.QuantumDeterminants.rhoStd n, ⟨?_, ?_⟩, hord, ?_, u, hu, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `h1` using `hstep a b hab`. Establish `h2 : ((b : ℕ) : ℝ) < n` using `by exact_mod_cast b.isLt`. Establish `h3 : (0 : ℝ) ≤ ((a : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Simplify using `only [Formalism.QuantumDeterminants.rhoStd, Pi.sub_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a`. Take `⟨m, hm⟩` from `hγint (s a)`. Take `⟨k, hk⟩` from `two_rhoC_int (ε ∘ s) a`.

Use `⟨m + k - (n : ℤ) + 1 + (a : ℕ), ?_⟩` and prove the remaining obligations. Simplify using `only [xv, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]`. Use `push_cast`. Rewrite using `[hm, hk]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `μ x hx hμ show vNormSq (ε ∘ s) (lowK (ε ∘ s) _) ≤ _`. Rewrite using `[hlow]`. Conclude with `hMin2 μ x hx hμ`. Use `show KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (lowK (ε ∘ s) _) u`. Rewrite using `[hlow]`.

Conclude with `hKH2`.
-/
theorem farReg_of_lkt_unitIneq_farNum : LKTExists → Renumber → UnitIneq → COBlock → FarNum → FarReg := by
  intro hLK hRn hUI hCO hFN n C δ hδ
  obtain ⟨K2, hK2⟩ := hUI n
  obtain ⟨K1, hK1⟩ := hCO n
  obtain ⟨N₀, hN⟩ := hFN n C δ (max K1 K2) hδ
  refine ⟨N₀, ?_⟩
  intro ε V _ _ E hE χ N hV hUn hLF hInt hSC hN₀ hsep hbd
  obtain ⟨γ, u, hu, hKH, hMin, hγint, hdom⟩ := hLK n ε V E hE hV hUn hLF hInt

  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin n), Antitone (xv ε γ ∘ s) := by
    refine ⟨Tuple.sort (fun a => - xv ε γ a), fun a b hab => ?_⟩
    have := Tuple.monotone_sort (fun a => - xv ε γ a) hab
    simp only [Function.comp_apply] at this ⊢
    linarith
  have hblk : ∀ a b, a < b → ε a = ε b → xv ε γ b < xv ε γ a := by
    intro a b hab he
    have h1 := hdom a b hab he
    have h2 := rhoC_lt ε hab he
    simp only [xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hord : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b := by
    intro a b hab he
    by_contra hc
    have hne : s a ≠ s b := fun h => hab.ne (s.injective h)
    have hlt : s b < s a := lt_of_le_of_ne (not_lt.1 hc) hne.symm
    have h1 := hblk (s b) (s a) hlt he.symm
    have h2 := hs hab.le
    simp only [Function.comp_apply] at h2
    linarith
  obtain ⟨hE', hUn', hLF', hSC', hKH', hMin', hrho⟩ := hRn n ε V E hE s hord
  have hUn2 := hUn' hUn
  have hLF2 := hLF' hLF
  have hSC2 := hSC' χ hSC
  have hKH2 := (hKH' γ u).1 hKH
  have hMin2 := (hMin' γ).1 hMin
  have hx' : xv (ε ∘ s) (γ ∘ s) = xv ε γ ∘ s := by
    funext a
    simp only [xv, hrho, Pi.add_apply, Pi.smul_apply, Function.comp_apply]
  have hanti : Antitone (xv (ε ∘ s) (γ ∘ s)) := by rw [hx']; exact hs
  have hLc : (0 : ℝ) ≤ Lc n := by unfold Lc; positivity
  obtain ⟨lev, hmono, hgap, hspread⟩ := exists_lev _ hanti hLc
  have hG : Gapped (ε ∘ s) (γ ∘ s) lev (Lc n) := ⟨hanti, hmono, hgap⟩
  have hKU : CompanionTheory.D.DSIC.KUnit (ε ∘ s) (fun a b => E (s a) (s b)) := by
    intro a b he x y
    have h1 := hUn2 a b x y
    have h2 : Formalism.REAL.sgn (ε ∘ s) a b = 1 := if_pos he
    rw [h2] at h1
    simpa using h1
  obtain ⟨σ, hσ⟩ := hK1 (ε ∘ s) (γ ∘ s) lev V (fun a b => E (s a) (s b)) hE' χ hG hKU hLF2 hMin2 hSC2 ⟨u, hu, hKH2⟩
  have hcas := hK2 (ε ∘ s) V (fun a b => E (s a) (s b)) hE' χ (γ ∘ s) u hUn2 hSC2 hu hKH2
  have hinj : Function.Injective lev := by
    refine hN χ (xv (ε ∘ s) (γ ∘ s)) (rhoC (ε ∘ s)) lev σ N hanti hmono (abs_rhoC_le _) hspread ?_ ?_ hsep hbd hN₀
    · exact fun c => (hσ c).trans (le_max_left _ _)
    · have e : nsq (γ ∘ s + rhoC (ε ∘ s)) = ∑ a, (xv (ε ∘ s) (γ ∘ s) a - rhoC (ε ∘ s) a) ^ 2 := by
        unfold PI.UpqRep.nsq PI.UpqRep.dot
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [← e]
      exact hcas.trans (by linarith [le_max_right K1 K2])

  have hstep : ∀ a b : Fin n, a < b → Lc n ≤ xv (ε ∘ s) (γ ∘ s) a - xv (ε ∘ s) (γ ∘ s) b := by
    intro a b hab
    exact hgap a b (lt_of_le_of_ne (hmono hab.le) fun h => hab.ne (hinj h))
  have hLbig : (n : ℝ) + 1 ≤ Lc n := by
    unfold Lc
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
  have hlow : lowK (ε ∘ s) (xv (ε ∘ s) (γ ∘ s) - Formalism.QuantumDeterminants.rhoStd n) = γ ∘ s := by
    funext a
    have h1 := rho_sum (ε ∘ s) a
    simp only [lowK, xv, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  refine ⟨s, xv (ε ∘ s) (γ ∘ s) - Formalism.QuantumDeterminants.rhoStd n, ⟨?_, ?_⟩, hord, ?_, u, hu, ?_⟩
  · intro a b hab
    have h1 := hstep a b hab
    have h2 : ((b : ℕ) : ℝ) < n := by exact_mod_cast b.isLt
    have h3 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [Formalism.QuantumDeterminants.rhoStd, Pi.sub_apply]
    linarith
  · intro a
    obtain ⟨m, hm⟩ := hγint (s a)
    obtain ⟨k, hk⟩ := two_rhoC_int (ε ∘ s) a
    refine ⟨m + k - (n : ℤ) + 1 + (a : ℕ), ?_⟩
    simp only [xv, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    push_cast
    rw [hm, hk]
    ring
  · intro μ x hx hμ
    show vNormSq (ε ∘ s) (lowK (ε ∘ s) _) ≤ _
    rw [hlow]
    exact hMin2 μ x hx hμ
  · show KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (lowK (ε ∘ s) _) u
    rw [hlow]
    exact hKH2

end GlobalTheory.CompanionTheory.FarRegularityLevels
