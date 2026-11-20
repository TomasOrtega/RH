import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `A B hAB h`. Establish `hE : A = B` using `Submodule.eq_of_le_of_finrank_eq hAB (by omega)`.

Conclude with `⟨fun _ => A, fun _ _ _ => le_rfl, rfl, fun _ _ => hE, fun t ht => by`. Establish `: t = 0` using `by omega`. Substitute `this` using the available equality. Use the proof step `simp⟩`. Consider the case `succ k ih`.

Introduce `A B hAB h`. Establish `hne : A ≠ B`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Take `⟨v, hvB, hvA⟩` from `SetLike.exists_of_lt (lt_of_le_of_ne hAB hne)`.

Establish `hA' : Module.finrank K (A ⊔ Submodule.span K {v} : Submodule K V) = Module.finrank K A + 1` using `Submodule.finrank_sup_span_singleton hvA`. Establish `hle : (A ⊔ Submodule.span K {v} : Submodule K V) ≤ B` using `sup_le hAB ((Submodule.span_singleton_le_iff_mem v B).2 hvB)`. Take `⟨c, hc, hc0, hcB, hcr⟩` from `ih _ B hle (by omega)`. Use `⟨fun t => match t with | 0 => A | s + 1 => c s, ?_, rfl, ?_, ?_⟩` and prove the remaining obligations. Use `monotone_nat_of_le_succ fun t => ?_` and prove the remaining obligations.

Break down `t with _ | s` into its components or cases. Use `show A ≤ c 0`. Rewrite using `[hc0]`. Conclude with `le_sup_left`. Use `show c s ≤ c (s + 1)`.

Conclude with `hc (Nat.le_succ s)`. Introduce `t ht`. Take `⟨s, rfl⟩ : ∃ s, t = s + 1` from `⟨t - 1, by omega⟩`. Conclude with `hcB s (by omega)`. Introduce `t ht`.

Break down `t with _ | s` into its components or cases. Simplify using the standard rewrite rules. Use `show Module.finrank K (c s) = _`. Rewrite using `[hcr s (by omega), hA']`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_chain_between {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    ∀ (k : ℕ) (A B : Submodule K V), A ≤ B → Module.finrank K B = Module.finrank K A + k →
      ∃ c : ℕ → Submodule K V, Monotone c ∧ c 0 = A ∧ (∀ t, k ≤ t → c t = B) ∧
        ∀ t ≤ k, Module.finrank K (c t) = Module.finrank K A + t := by
  intro k
  induction k with
  | zero =>
    intro A B hAB h
    have hE : A = B := Submodule.eq_of_le_of_finrank_eq hAB (by omega)
    exact ⟨fun _ => A, fun _ _ _ => le_rfl, rfl, fun _ _ => hE, fun t ht => by
      have : t = 0 := by omega
      subst this; simp⟩
  | succ k ih =>
    intro A B hAB h
    have hne : A ≠ B := by
      rintro rfl; omega
    obtain ⟨v, hvB, hvA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hAB hne)
    have hA' : Module.finrank K (A ⊔ Submodule.span K {v} : Submodule K V) = Module.finrank K A + 1 :=
      Submodule.finrank_sup_span_singleton hvA
    have hle : (A ⊔ Submodule.span K {v} : Submodule K V) ≤ B :=
      sup_le hAB ((Submodule.span_singleton_le_iff_mem v B).2 hvB)
    obtain ⟨c, hc, hc0, hcB, hcr⟩ := ih _ B hle (by omega)
    refine ⟨fun t => match t with | 0 => A | s + 1 => c s, ?_, rfl, ?_, ?_⟩
    · refine monotone_nat_of_le_succ fun t => ?_
      rcases t with _ | s
      · show A ≤ c 0
        rw [hc0]; exact le_sup_left
      · show c s ≤ c (s + 1)
        exact hc (Nat.le_succ s)
    · intro t ht
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact hcB s (by omega)
    · intro t ht
      rcases t with _ | s
      · simp
      · show Module.finrank K (c s) = _
        rw [hcr s (by omega), hA']
        omega

/- English proof (translation)
Establish `hr : ∀ i, Module.finrank K (Wn i) = P i`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => rw [h0, hP0]`. Simplify using the standard rewrite rules.

Consider the case `succ i ih => rw [hs, ih, hPs]`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero`. Use `⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun l hl => ?_, fun i hi => ?_, fun l _ => h0.symm⟩` and prove the remaining obligations.

Rewrite `hl` using `[hP0]`. Establish `: l = 0` using `by omega`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `: i = 0` using `by omega`.

Substitute `this` using the available equality. Conclude with `h0.symm`. Consider the case `succ a ih`. Take `⟨W', hW'm, hW'r, hW'p, hW'l⟩` from `ih`. Take `⟨c, hc, hc0, hcB, hcr⟩` from `exists_chain_between (jn a) (Wn a) (Wn (a + 1)) (hm (Nat.le_succ a)) (hs a)`.

Take `⟨W'', hW''⟩ : ∃ W'' : ℕ → Submodule K V, ∀ l, W'' l = if l ≤ P a then W' l else c (l - P a)` from `⟨_, fun _ => rfl⟩`. Establish `hPa : W' (P a) = Wn a` using `hW'l _ le_rfl`. Use `⟨W'', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l m hlm`. Rewrite using `[hW'' l, hW'' m]`.

Distinguish the cases in `hl : l ≤ P a`. Distinguish the cases in `hm' : m ≤ P a`. Rewrite using `[if_pos hl, if_pos hm']`. Conclude with `hW'm hlm`. Rewrite using `[if_pos hl, if_neg hm']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[if_neg hl, if_neg (by omega)]`. Conclude with `hc (by omega)`. Introduce `l hl`. Rewrite using `[hW'' l]`.

Distinguish the cases in `hl' : l ≤ P a`. Rewrite using `[if_pos hl']`. Conclude with `hW'r l hl'`. Rewrite using `[if_neg hl', hcr _ (by rw [hPs] at hl; omega), hr]`. Use linear arithmetic over natural numbers and integers.

Introduce `i hi`. Rewrite using `[hW'' (P i)]`. Break down `Nat.lt_or_ge i (a + 1) with hia | hia` into its components or cases. Establish `hle : P i ≤ P a`. Establish `key : ∀ d, P i ≤ P (i + d)`.

Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => exact le_rfl`. Consider the case `succ d ihd => rw [← Nat.add_assoc, hPs]`. Use linear arithmetic over natural numbers and integers.

Use `key (a - i)` as an intermediate fact. Rewrite `this` using `[show i + (a - i) = a by omega]`. Then use the resulting hypothesis. Rewrite using `[if_pos hle]; exact hW'p i (by omega)`. Establish `hi' : i = a + 1` using `by omega`. Substitute `hi'` using the available equality.

Distinguish the cases in `hj : P (a + 1) ≤ P a`. Rewrite using `[if_pos hj]`. Establish `hj0 : jn a = 0` using `by rw [hPs] at hj; omega`. Rewrite using `[show P (a + 1) = P a by rw [hPs, hj0, Nat.add_zero], hPa]`. Conclude with `hc0.symm.trans (hcB 0 (by omega))`.

Rewrite using `[if_neg hj, hPs, Nat.add_sub_cancel_left]`. Conclude with `hcB _ le_rfl`. Introduce `l hl`. Rewrite `hl` using `[hPs]`. Rewrite using `[hW'' l]`.

Distinguish the cases in `hl' : l ≤ P a`. Rewrite using `[if_pos hl', hW'l l (by omega)]`. Conclude with `hc0.symm.trans (hcB 0 (by omega))`. Rewrite using `[if_neg hl']`. Conclude with `hcB _ (by omega)`.
-/
theorem exists_refine_nat {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Wn : ℕ → Submodule K V) (jn P : ℕ → ℕ) (h0 : Wn 0 = ⊥) (hm : Monotone Wn)
    (hs : ∀ k, Module.finrank K (Wn (k + 1)) = Module.finrank K (Wn k) + jn k)
    (hP0 : P 0 = 0) (hPs : ∀ i, P (i + 1) = P i + jn i) :
    ∀ a, ∃ W' : ℕ → Submodule K V, Monotone W' ∧ (∀ l ≤ P a, Module.finrank K (W' l) = l) ∧
      (∀ i ≤ a, W' (P i) = Wn i) ∧ ∀ l, P a ≤ l → W' l = Wn a := by
  have hr : ∀ i, Module.finrank K (Wn i) = P i := by
    intro i
    induction i with
    | zero => rw [h0, hP0]; simp
    | succ i ih => rw [hs, ih, hPs]
  intro a
  induction a with
  | zero =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun l hl => ?_, fun i hi => ?_, fun l _ => h0.symm⟩
    · rw [hP0] at hl
      have : l = 0 := by omega
      subst this; simp
    · have : i = 0 := by omega
      subst this; exact h0.symm
  | succ a ih =>
    obtain ⟨W', hW'm, hW'r, hW'p, hW'l⟩ := ih
    obtain ⟨c, hc, hc0, hcB, hcr⟩ := exists_chain_between (jn a) (Wn a) (Wn (a + 1))
      (hm (Nat.le_succ a)) (hs a)
    obtain ⟨W'', hW''⟩ : ∃ W'' : ℕ → Submodule K V, ∀ l, W'' l = if l ≤ P a then W' l else c (l - P a) :=
      ⟨_, fun _ => rfl⟩
    have hPa : W' (P a) = Wn a := hW'l _ le_rfl
    refine ⟨W'', ?_, ?_, ?_, ?_⟩
    · intro l m hlm
      rw [hW'' l, hW'' m]
      by_cases hl : l ≤ P a
      · by_cases hm' : m ≤ P a
        · rw [if_pos hl, if_pos hm']; exact hW'm hlm
        · rw [if_pos hl, if_neg hm']
          calc W' l ≤ W' (P a) := hW'm hl
            _ = c 0 := by rw [hPa, hc0]
            _ ≤ c (m - P a) := hc (Nat.zero_le _)
      · rw [if_neg hl, if_neg (by omega)]
        exact hc (by omega)
    · intro l hl
      rw [hW'' l]
      by_cases hl' : l ≤ P a
      · rw [if_pos hl']; exact hW'r l hl'
      · rw [if_neg hl', hcr _ (by rw [hPs] at hl; omega), hr]
        omega
    · intro i hi
      rw [hW'' (P i)]
      rcases Nat.lt_or_ge i (a + 1) with hia | hia
      · have hle : P i ≤ P a := by
          have key : ∀ d, P i ≤ P (i + d) := by
            intro d
            induction d with
            | zero => exact le_rfl
            | succ d ihd => rw [← Nat.add_assoc, hPs]; omega
          have := key (a - i)
          rwa [show i + (a - i) = a by omega] at this
        rw [if_pos hle]; exact hW'p i (by omega)
      · have hi' : i = a + 1 := by omega
        subst hi'
        by_cases hj : P (a + 1) ≤ P a
        · rw [if_pos hj]
          have hj0 : jn a = 0 := by rw [hPs] at hj; omega
          rw [show P (a + 1) = P a by rw [hPs, hj0, Nat.add_zero], hPa]
          exact hc0.symm.trans (hcB 0 (by omega))
        · rw [if_neg hj, hPs, Nat.add_sub_cancel_left]
          exact hcB _ le_rfl
    · intro l hl
      rw [hPs] at hl
      rw [hW'' l]
      by_cases hl' : l ≤ P a
      · rw [if_pos hl', hW'l l (by omega)]
        exact hc0.symm.trans (hcB 0 (by omega))
      · rw [if_neg hl']
        exact hcB _ (by omega)

/- English proof (translation)
Introduce `n a ε j W hW`. Take `⟨h0, hmono, hstep, hiso⟩` from `hW`. Take `⟨jn, hjn⟩ : ∃ jn : ℕ → ℕ, ∀ k, jn k = if h : k < a then j ⟨k, h⟩ else 0` from `⟨_, fun _ => rfl⟩`. Take `⟨Wn, hWn⟩ : ∃ Wn : ℕ → Submodule ℂ (Fin n → ℂ), ∀ k, Wn k = W ⟨min k a, by omega⟩` from `⟨_, fun _ => rfl⟩`. Take `⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ i, P i = ∑ k ∈ range i, jn k` from `⟨_, fun _ => rfl⟩`.

Establish `hP0 : P 0 = 0` using `by rw [hP]; simp`. Establish `hPs : ∀ i, P (i + 1) = P i + jn i` using `fun i => by rw [hP, hP, Finset.sum_range_succ]`. Establish `hPm : Monotone P` using `fun x y h => by`. Rewrite using `[hP, hP]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.range_mono h)`.

Establish `hWi : ∀ i : Fin (a + 1), Wn i = W i` using `fun i => by`. Rewrite using `[hWn]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish `hWn0 : Wn 0 = ⊥`. Rewrite using `[hWn, ← h0]`. Use `congr 1`. Establish `hWnm : Monotone Wn` using `fun x y hxy => by`.

Rewrite using `[hWn, hWn]; exact hmono (Fin.mk_le_mk.2 (by omega))`. Establish `hWns : ∀ k, Module.finrank ℂ (Wn (k + 1)) = Module.finrank ℂ (Wn k) + jn k`. Introduce `k`. Distinguish the cases in `hk : k < a`. Establish `e1 : Wn (k + 1) = W (⟨k, hk⟩ : Fin a).succ`.

Rewrite using `[hWn]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish `e2 : Wn k = W (⟨k, hk⟩ : Fin a).castSucc`. Rewrite using `[hWn]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2, hstep ⟨k, hk⟩, hjn, dif_pos hk]`. Establish `e : Wn (k + 1) = Wn k`. Rewrite using `[hWn, hWn]`. Use `congr 1`.

Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[e, hjn, dif_neg hk, Nat.add_zero]`. Take `⟨W', hW'm, hW'r, hW'p, hW'l⟩` from `exists_refine_nat Wn jn P hWn0 hWnm hWns hP0 hPs a`.

Establish `hlast : W' (P a) = W (Fin.last a)`. Rewrite using `[hW'l _ le_rfl, ← hWi (Fin.last a), Fin.val_last]`. Establish `hβ : ∀ l : Fin (P a), ∃! i : Fin a, P i ≤ l ∧ (l : ℕ) < P (i + 1)`. Introduce `l`. Establish `ha : 0 < a`.

Break down `Nat.eq_zero_or_pos a with ha | ha` into its components or cases. Substitute `ha` using the available equality. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `ha`.

Establish `hla : (l : ℕ) < P (a - 1 + 1)` using `by rw [show a - 1 + 1 = a by omega]; exact l.isLt`. Establish `hex : ∃ m, (l : ℕ) < P (m + 1)` using `⟨a - 1, hla⟩`. Establish `hma : Nat.find hex < a`. Establish `hle : Nat.find hex ≤ a - 1` using `Nat.find_min' hex hla`. Use linear arithmetic over natural numbers and integers.

Use `⟨⟨Nat.find hex, hma⟩, ⟨?_, Nat.find_spec hex⟩, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (Nat.find hex) with h | h` into its components or cases. Simplify using `only [h, hP0]`. Conclude with `Nat.zero_le _`. Use `Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)` as an intermediate fact.

Rewrite `this` using `[show Nat.find hex - 1 + 1 = Nat.find hex by omega]`. Simplify using `using this`. Introduce and unpack `i ⟨hi1, hi2⟩`. Apply `Fin.ext` to reduce the goal to its premises. Use `show (i : ℕ) = Nat.find hex`.

Break down `lt_trichotomy (i : ℕ) (Nat.find hex) with h | h | h` into its components or cases. Conclude with `absurd hi2 (not_lt.2 ((hPm (by omega : (i : ℕ) + 1 ≤ Nat.find hex)).trans (by`. Break down `Nat.eq_zero_or_pos (Nat.find hex) with h' | h'` into its components or cases. Use linear arithmetic over natural numbers and integers. Use `Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)` as an intermediate fact.

Rewrite `this` using `[show Nat.find hex - 1 + 1 = Nat.find hex by omega]`. Use the proof step `omega)))`. Conclude with `h`. Conclude with `absurd (Nat.find_spec hex) (not_lt.2 ((hPm (by omega : Nat.find hex + 1 ≤ (i : ℕ))).trans hi1))`. Establish `hPle : ∀ i : Fin (a + 1), P i < P a + 1` using `fun i => Nat.lt_succ_of_le (hPm (Nat.le_of_lt_succ i.isLt))`.

Use `⟨P a, fun l => W' l, fun l => Classical.choose (hβ l), fun i => ⟨P i, hPle i⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show W' ((0 : Fin (P a + 1)) : ℕ) = ⊥`. Rewrite using `[Fin.val_zero]`. Conclude with `Submodule.finrank_eq_zero.1 (hW'r 0 (Nat.zero_le _))`. Introduce `x y hxy`.

Conclude with `hW'm (Fin.le_iff_val_le_val.1 hxy)`. Introduce `i show Module.finrank ℂ (W' ((i.succ : Fin (P a + 1)) : ℕ)) = Module.finrank ℂ (W' ((i.castSucc : Fin (P a + 1)) : ℕ)) + 1`. Rewrite using `[Fin.val_succ, Fin.coe_castSucc, hW'r _ (by omega), hW'r _ (by omega)]`. Introduce `x hx y hy`. Establish `e : W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a)` using `by rw [Fin.val_last, hlast]`.

Conclude with `hiso x (e ▸ hx) y (e ▸ hy)`. Introduce `i show W' (P i) = W i`. Rewrite using `[hW'p i (Nat.le_of_lt_succ i.isLt), hWi]`. Use `show W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a)`. Rewrite using `[Fin.val_last, hlast]`.

Introduce `l i`. Establish `hs` using `Classical.choose_spec (hβ l)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Use `⟨Fin.le_iff_val_le_val.2 ?_, Fin.lt_iff_val_lt_val.2 ?_⟩` and prove the remaining obligations.

Simplify using `using hs.1.1`. Simplify using `using hs.1.2`. Introduce and unpack `⟨h1, h2⟩`. Use `(hs.2 i ⟨?_, ?_⟩).symm` and prove the remaining obligations. Simplify using `using Fin.le_iff_val_le_val.1 h1`.

Simplify using `using Fin.lt_iff_val_lt_val.1 h2`. Introduce `i show P i = _`. Rewrite using `[hP, Finset.sum_filter]`. Establish `e1 : ∀ l : Fin a, (if (l : ℕ) < (i : ℕ) then j l else 0) = (fun k => if k < (i : ℕ) then jn k else 0) (l : ℕ)`. Introduce `l`.

Simplify using `[hjn, l.isLt]`. Rewrite using `[Finset.sum_congr rfl (fun l _ => e1 l), Fin.sum_univ_eq_sum_range (fun k => if k < (i : ℕ) then jn k else 0) a, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `k`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_refine_isIsoFlag : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W → ∃ (b : ℕ) (W' : Flag n b) (β : Fin b → Fin a) (p : Fin (a + 1) → Fin (b + 1)), IsIsoFlag ε (fun _ => 1) W' ∧ (∀ i, W' (p i) = W i) ∧ W' (Fin.last b) = W (Fin.last a) ∧ (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) ∧ ∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l := by
  intro n a ε j W hW
  obtain ⟨h0, hmono, hstep, hiso⟩ := hW
  obtain ⟨jn, hjn⟩ : ∃ jn : ℕ → ℕ, ∀ k, jn k = if h : k < a then j ⟨k, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Wn, hWn⟩ : ∃ Wn : ℕ → Submodule ℂ (Fin n → ℂ), ∀ k, Wn k = W ⟨min k a, by omega⟩ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ i, P i = ∑ k ∈ range i, jn k := ⟨_, fun _ => rfl⟩
  have hP0 : P 0 = 0 := by rw [hP]; simp
  have hPs : ∀ i, P (i + 1) = P i + jn i := fun i => by rw [hP, hP, Finset.sum_range_succ]
  have hPm : Monotone P := fun x y h => by
    rw [hP, hP]; exact Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hWi : ∀ i : Fin (a + 1), Wn i = W i := fun i => by
    rw [hWn]; congr 1; ext; simp; omega
  have hWn0 : Wn 0 = ⊥ := by
    rw [hWn, ← h0]; congr 1
  have hWnm : Monotone Wn := fun x y hxy => by
    rw [hWn, hWn]; exact hmono (Fin.mk_le_mk.2 (by omega))
  have hWns : ∀ k, Module.finrank ℂ (Wn (k + 1)) = Module.finrank ℂ (Wn k) + jn k := by
    intro k
    by_cases hk : k < a
    · have e1 : Wn (k + 1) = W (⟨k, hk⟩ : Fin a).succ := by
        rw [hWn]; congr 1; ext; simp; omega
      have e2 : Wn k = W (⟨k, hk⟩ : Fin a).castSucc := by
        rw [hWn]; congr 1; ext; simp; omega
      rw [e1, e2, hstep ⟨k, hk⟩, hjn, dif_pos hk]
    · have e : Wn (k + 1) = Wn k := by
        rw [hWn, hWn]; congr 1; ext; simp; omega
      rw [e, hjn, dif_neg hk, Nat.add_zero]
  obtain ⟨W', hW'm, hW'r, hW'p, hW'l⟩ := exists_refine_nat Wn jn P hWn0 hWnm hWns hP0 hPs a
  have hlast : W' (P a) = W (Fin.last a) := by
    rw [hW'l _ le_rfl, ← hWi (Fin.last a), Fin.val_last]
  have hβ : ∀ l : Fin (P a), ∃! i : Fin a, P i ≤ l ∧ (l : ℕ) < P (i + 1) := by
    intro l
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; have := l.isLt; omega
      · exact ha
    have hla : (l : ℕ) < P (a - 1 + 1) := by rw [show a - 1 + 1 = a by omega]; exact l.isLt
    have hex : ∃ m, (l : ℕ) < P (m + 1) := ⟨a - 1, hla⟩
    have hma : Nat.find hex < a := by
      have hle : Nat.find hex ≤ a - 1 := Nat.find_min' hex hla
      omega
    refine ⟨⟨Nat.find hex, hma⟩, ⟨?_, Nat.find_spec hex⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · simp only [h, hP0]; exact Nat.zero_le _
      · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
        simpa using this
    · rintro i ⟨hi1, hi2⟩
      apply Fin.ext
      show (i : ℕ) = Nat.find hex
      rcases lt_trichotomy (i : ℕ) (Nat.find hex) with h | h | h
      · exact absurd hi2 (not_lt.2 ((hPm (by omega : (i : ℕ) + 1 ≤ Nat.find hex)).trans
          (by
            rcases Nat.eq_zero_or_pos (Nat.find hex) with h' | h'
            · omega
            · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
              rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
              omega)))
      · exact h
      · exact absurd (Nat.find_spec hex) (not_lt.2 ((hPm (by omega : Nat.find hex + 1 ≤ (i : ℕ))).trans hi1))
  have hPle : ∀ i : Fin (a + 1), P i < P a + 1 := fun i => Nat.lt_succ_of_le (hPm (Nat.le_of_lt_succ i.isLt))
  refine ⟨P a, fun l => W' l, fun l => Classical.choose (hβ l), fun i => ⟨P i, hPle i⟩, ⟨?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · show W' ((0 : Fin (P a + 1)) : ℕ) = ⊥
    rw [Fin.val_zero]
    exact Submodule.finrank_eq_zero.1 (hW'r 0 (Nat.zero_le _))
  · intro x y hxy
    exact hW'm (Fin.le_iff_val_le_val.1 hxy)
  · intro i
    show Module.finrank ℂ (W' ((i.succ : Fin (P a + 1)) : ℕ)) = Module.finrank ℂ (W' ((i.castSucc : Fin (P a + 1)) : ℕ)) + 1
    rw [Fin.val_succ, Fin.coe_castSucc, hW'r _ (by omega), hW'r _ (by omega)]
  · intro x hx y hy
    have e : W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a) := by rw [Fin.val_last, hlast]
    exact hiso x (e ▸ hx) y (e ▸ hy)
  · intro i
    show W' (P i) = W i
    rw [hW'p i (Nat.le_of_lt_succ i.isLt), hWi]
  · show W' ((Fin.last (P a) : Fin (P a + 1)) : ℕ) = W (Fin.last a)
    rw [Fin.val_last, hlast]
  · intro l i
    have hs := Classical.choose_spec (hβ l)
    constructor
    · rintro rfl
      refine ⟨Fin.le_iff_val_le_val.2 ?_, Fin.lt_iff_val_lt_val.2 ?_⟩
      · simpa using hs.1.1
      · simpa using hs.1.2
    · rintro ⟨h1, h2⟩
      refine (hs.2 i ⟨?_, ?_⟩).symm
      · simpa using Fin.le_iff_val_le_val.1 h1
      · simpa using Fin.lt_iff_val_lt_val.1 h2
  · intro i
    show P i = _
    rw [hP, Finset.sum_filter]
    have e1 : ∀ l : Fin a, (if (l : ℕ) < (i : ℕ) then j l else 0) =
        (fun k => if k < (i : ℕ) then jn k else 0) (l : ℕ) := by
      intro l; simp [hjn, l.isLt]
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Fin.sum_univ_eq_sum_range (fun k => if k < (i : ℕ) then jn k else 0) a,
      ← Finset.sum_filter]
    congr 1
    ext k; simp; omega

end GlobalTheory.RealInd.Stages
