import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastStepParam

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a` using `by ext; simp`. Establish `h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a` using `by ext; simp`. Establish `h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ)`. Use `a.2` as an intermediate fact. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp`.

Simplify using `only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, allPos, Pi.add_apply, Pi.sub_apply, ne_eq, not_true_eq_false, and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio, h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma lowK_allPos {n : ℕ} (lam : Fin n → ℝ) (a : Fin n) :
    Formalism.QuantumDeterminants.lowK (allPos n) lam a = lam a - ((n : ℝ) - 1) / 2 + ((a : ℕ) : ℝ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have := a.2
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  simp only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, allPos, Pi.add_apply, Pi.sub_apply, ne_eq,
    not_true_eq_false, and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2,
    Fin.card_Ioi, Fin.card_Iio, h3]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Establish `h1` using `ih (by omega)`. Establish `h2 : z ⟨a + d, by omega⟩ < z ⟨a + (d + 1), h⟩` using `hz (by simp [Fin.lt_def])`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
lemma sub_mono {n : ℕ} {z : Fin n → ℤ} (hz : StrictMono z) (a d : ℕ) (h : a + d < n) :
    z ⟨a, by omega⟩ + d ≤ z ⟨a + d, h⟩ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 : z ⟨a + d, by omega⟩ < z ⟨a + (d + 1), h⟩ := hz (by simp [Fin.lt_def])
    push_cast
    omega

/- English proof (translation)
Take `⟨a, ha⟩` from `a`. Take `⟨b, hb⟩` from `b`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le (show a ≤ b from h)`. Use `sub_mono hz a d hb` as an intermediate fact. Use `push_cast`.

Use linear arithmetic over natural numbers and integers.
-/
lemma sub_mono' {n : ℕ} {z : Fin n → ℤ} (hz : StrictMono z) {a b : Fin n} (h : (a : ℕ) ≤ b) :
    z a - (a : ℕ) ≤ z b - (b : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ b from h)
  have := sub_mono hz a d hb
  push_cast
  omega

/- English proof (translation)
Set `L : Fin (n + t) → ℤ` to `fun b => if h : (b : ℕ) < t then e + s - (b : ℕ) else -z ⟨b - t, by omega⟩`. Establish `hL : StrictAnti L`. Introduce `a b hab`. Establish `hab' : (a : ℕ) < b` using `hab`. Simplify using `only [L]`.

Use `split_ifs with h1 h2 h2`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use `hb ⟨b - t, by omega⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `: z ⟨a - t, by omega⟩ < z ⟨b - t, by omega⟩` using `hz (by simp only [Fin.lt_def]; omega)`. Use linear arithmetic over natural numbers and integers. Establish `hL' : StrictAnti fun b => (L b : ℝ)` using `fun a b hab => by`. Use `hL hab` as an intermediate fact. Simplify using `only`.

Conclude with `this` after adjusting the coercions. Establish `key : lam' = fun b => (L b : ℝ)`. Rewrite using `[← StrictAnti.range_inj h' hL']`. Use extensionality with `x`. Rewrite using `[hr]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨a, rfl⟩ | ⟨c, hc, rfl⟩)`. Use `⟨⟨a + t, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `[L]`. Use `⟨⟨c, by omega⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[L, hc]`. Introduce and unpack `⟨c, rfl⟩`. Distinguish the cases in `hc : (c : ℕ) < t`. Conclude with `.inr ⟨c, hc, by simp [L, hc]⟩`. Conclude with `.inl ⟨⟨c - t, by omega⟩, by simp [L, hc]⟩`.

Rewrite using `[key]`.
-/
lemma shape {n t : ℕ} (e s : ℤ) (ht : (t : ℤ) = 2 * s + 1) (z : Fin n → ℤ) (hz : StrictMono z)
    (hb : ∀ a, -e + s + 2 ≤ z a) (lam' : Fin (n + t) → ℝ) (h' : StrictAnti lam')
    (hr : ∀ x : ℝ, x ∈ Set.range lam' ↔
      (∃ a, x = -(z a : ℝ)) ∨ ∃ c : ℕ, c < t ∧ x = ((e + s - c : ℤ) : ℝ)) (b : Fin (n + t)) :
    lam' b = ((if h : (b : ℕ) < t then e + s - (b : ℕ) else -z ⟨b - t, by omega⟩ : ℤ) : ℝ) := by
  let L : Fin (n + t) → ℤ := fun b => if h : (b : ℕ) < t then e + s - (b : ℕ) else -z ⟨b - t, by omega⟩
  have hL : StrictAnti L := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    simp only [L]
    split_ifs with h1 h2 h2
    · omega
    · omega
    · have := hb ⟨b - t, by omega⟩
      omega
    · have : z ⟨a - t, by omega⟩ < z ⟨b - t, by omega⟩ := hz (by simp only [Fin.lt_def]; omega)
      omega
  have hL' : StrictAnti fun b => (L b : ℝ) := fun a b hab => by
    have := hL hab
    simp only
    exact_mod_cast this
  have key : lam' = fun b => (L b : ℝ) := by
    rw [← StrictAnti.range_inj h' hL']
    ext x
    rw [hr]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
      · refine ⟨⟨a + t, by omega⟩, ?_⟩
        simp [L]
      · refine ⟨⟨c, by omega⟩, ?_⟩
        simp [L, hc]
    · rintro ⟨c, rfl⟩
      by_cases hc : (c : ℕ) < t
      · exact .inr ⟨c, hc, by simp [L, hc]⟩
      · exact .inl ⟨⟨c - t, by omega⟩, by simp [L, hc]⟩
  rw [key]

/- English proof (translation)
Establish `hz : StrictMono z` using `fun a b hab => by`. Use `hl hab` as an intermediate fact. Rewrite `this` using `[hlz, hlz]`. Establish `h2 : (z a : ℝ) < z b` using `by linarith`. Conclude with `h2` after adjusting the coercions.

Establish `hpos : ∀ a : Fin n, 0 ≤ e + z a - (s + 1) - (a : ℕ)` using `fun a => by`. Establish `h1` using `sub_mono' hz (a := ⟨0, by have := a.2; omega⟩) (b := a) (Nat.zero_le _)`. Establish `h2` using `hb ⟨0, by have := a.2; omega⟩`. Simplify using `only [Nat.cast_zero] at h1`. Use linear arithmetic over natural numbers and integers.

Establish `htR : (t : ℝ) = 2 * s + 1` using `by exact_mod_cast ht`. Establish `hnR : (n : ℝ) = 2 * p` using `by exact_mod_cast hn`. Set `ν : Fin (n + t) → ℕ` to `fun c => if h : (c : ℕ) < n then (e + z ⟨n - 1 - c, by omega⟩ - (s + 1) - ((n - 1 - c : ℕ) : ℤ)).toNat else 0`. Establish `hν : ∀ (c : Fin (n + t)) (a : Fin n), (c : ℕ) + a + 1 = n → (ν c : ℝ) = e + z a - (s + 1) - (a : ℕ)`. Introduce `c a h`.

Establish `hc : (c : ℕ) < n` using `by omega`. Establish `ha : (⟨n - 1 - c, by omega⟩ : Fin n) = a` using `Fin.ext (by simp only; omega)`. Establish `ha' : n - 1 - c = a` using `by omega`. Establish `: (ν c : ℤ) = e + z a - (s + 1) - (a : ℕ)`. Simplify using `only [ν, dif_pos hc, ha]`.

Rewrite using `[ha']`. Conclude with `Int.toNat_of_nonneg (hpos a)`. Conclude with `this` after adjusting the coercions. Use `⟨by omega, ν, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c d hcd`.

Establish `hcd' : (c : ℕ) ≤ d` using `hcd`. Simplify using `only [ν]`. Use `split_ifs with h1 h2 h2`. Apply `Int.toNat_le_toNat` to reduce the goal to its premises. Use `sub_mono' hz (a := ⟨n - 1 - d, by omega⟩) (b := ⟨n - 1 - c, by omega⟩) (by simp only; omega)` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Introduce `b hb`. Simplify using `only [ν]`. Rewrite using `[dif_neg (by omega)]`. Introduce `a`. Use `a.2` as an intermediate fact.

Rewrite using `[lowK_allPos, hν _ a (by simp [Fin.val_rev]; omega), hlz, hnR]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `b`. Use `b.2` as an intermediate fact.

Rewrite using `[lowK_allPos, shape e s ht z hz hb lam' h' hr b]`. Distinguish the cases in `hc : (b : ℕ) < t`. Establish `h0 : ν (Fin.rev b) = 0`. Simplify using `only [ν]`. Rewrite using `[dif_neg (by simp only [Fin.val_rev]; omega)]`.

Rewrite using `[dif_pos hc, h0]`. Use `push_cast`. Rewrite using `[htR, hnR]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dif_neg hc, hν _ ⟨b - t, by omega⟩ (by simp only [Fin.val_rev]; omega)]`.

Simplify using `only`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Rewrite using `[htR, hnR]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma partition {n t : ℕ} (e s p : ℤ) (ht : (t : ℤ) = 2 * s + 1) (hn : (n : ℤ) = 2 * p)
    (z : Fin n → ℤ) (lam : Fin n → ℝ) (hl : StrictAnti lam) (hlz : ∀ a, lam a = -(z a : ℝ) + 1 / 2)
    (hb : ∀ a, -e + s + 2 ≤ z a) (lam' : Fin (n + t) → ℝ) (h' : StrictAnti lam')
    (hr : ∀ x : ℝ, x ∈ Set.range lam' ↔
      (∃ a, x = -(z a : ℝ)) ∨ ∃ c : ℕ, c < t ∧ x = ((e + s - c : ℤ) : ℝ)) :
    ∃ (hn : n ≤ n + t) (ν : Fin (n + t) → ℕ), Antitone ν ∧ (∀ b : Fin (n + t), n ≤ (b : ℕ) → ν b = 0) ∧
      (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = ((e - p - s : ℤ) : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧
      ∀ b, Formalism.QuantumDeterminants.lowK (allPos (n + t)) lam' b = -((-e + p : ℤ) : ℝ) - ν (Fin.rev b) := by
  have hz : StrictMono z := fun a b hab => by
    have := hl hab
    rw [hlz, hlz] at this
    have h2 : (z a : ℝ) < z b := by linarith
    exact_mod_cast h2
  have hpos : ∀ a : Fin n, 0 ≤ e + z a - (s + 1) - (a : ℕ) := fun a => by
    have h1 := sub_mono' hz (a := ⟨0, by have := a.2; omega⟩) (b := a) (Nat.zero_le _)
    have h2 := hb ⟨0, by have := a.2; omega⟩
    simp only [Nat.cast_zero] at h1
    omega
  have htR : (t : ℝ) = 2 * s + 1 := by exact_mod_cast ht
  have hnR : (n : ℝ) = 2 * p := by exact_mod_cast hn
  let ν : Fin (n + t) → ℕ := fun c => if h : (c : ℕ) < n then
    (e + z ⟨n - 1 - c, by omega⟩ - (s + 1) - ((n - 1 - c : ℕ) : ℤ)).toNat else 0
  have hν : ∀ (c : Fin (n + t)) (a : Fin n), (c : ℕ) + a + 1 = n →
      (ν c : ℝ) = e + z a - (s + 1) - (a : ℕ) := by
    intro c a h
    have hc : (c : ℕ) < n := by omega
    have ha : (⟨n - 1 - c, by omega⟩ : Fin n) = a := Fin.ext (by simp only; omega)
    have ha' : n - 1 - c = a := by omega
    have : (ν c : ℤ) = e + z a - (s + 1) - (a : ℕ) := by
      simp only [ν, dif_pos hc, ha]
      rw [ha']
      exact Int.toNat_of_nonneg (hpos a)
    exact_mod_cast this
  refine ⟨by omega, ν, ?_, ?_, ?_, ?_⟩
  · intro c d hcd
    have hcd' : (c : ℕ) ≤ d := hcd
    simp only [ν]
    split_ifs with h1 h2 h2
    · apply Int.toNat_le_toNat
      have := sub_mono' hz (a := ⟨n - 1 - d, by omega⟩) (b := ⟨n - 1 - c, by omega⟩) (by simp only; omega)
      simp only at this
      omega
    · omega
    · omega
    · omega
  · intro b hb
    simp only [ν]
    rw [dif_neg (by omega)]
  · intro a
    have := a.2
    rw [lowK_allPos, hν _ a (by simp [Fin.val_rev]; omega), hlz, hnR]
    push_cast
    ring
  · intro b
    have := b.2
    rw [lowK_allPos, shape e s ht z hz hb lam' h' hr b]
    by_cases hc : (b : ℕ) < t
    · have h0 : ν (Fin.rev b) = 0 := by
        simp only [ν]
        rw [dif_neg (by simp only [Fin.val_rev]; omega)]
      rw [dif_pos hc, h0]
      push_cast
      rw [htR, hnR]
      ring
    · rw [dif_neg hc, hν _ ⟨b - t, by omega⟩ (by simp only [Fin.val_rev]; omega)]
      simp only
      rw [Nat.cast_sub (by omega)]
      push_cast
      rw [htR, hnR]
      ring

def IsEntry {R : Ranks} (P : HCParam R) (j : ℕ) (y : ℚ) : Prop :=
  (∃ i, y = P.v i) ∨ (∃ i, y = -P.b i) ∨
    ∃ i : Fin R.m, (i : ℕ) < j ∧ ∃ a : ℕ, a < R.t ∧ y = -P.e i + ((R.t : ℚ) - 1) / 2 - a

/- English proof (translation)
Establish `hi : ∀ i : Fin D.R.m, (i : ℕ) ≤ j` using `fun i => by have := i.2; omega`. Simplify using `only [parB, dualPar, TPar.Dpar, TPar.block, Ptw, tparRec, tparHC, Finset.mem_image, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range, hi, true_or, decide_true, IsEntry]`. Generalize the expression as in `(if Odd j then -(1 / 2) else 0 : ℚ) = c`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨_, ⟨_, (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, hij, _, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩, h⟩ <;>`.

Apply the tactic sequence `obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> refine ⟨rfl, ?_⟩`. Conclude with `.inl ⟨i, by simp⟩`. Conclude with `.inr (.inl ⟨i, by simp⟩)`. Conclude with `.inr (.inr ⟨i, hij, a, ha, by simp⟩)`. Introduce and unpack `⟨rfl, ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, hij, a, ha, h⟩⟩`.

Conclude with `⟨_, ⟨_, .inl (.inl ⟨i, rfl⟩), rfl⟩, Prod.ext (by simp only; linarith) rfl⟩`. Conclude with `⟨_, ⟨_, .inl (.inr ⟨i, rfl⟩), rfl⟩, Prod.ext (by simp only; linarith) rfl⟩`. Conclude with `⟨_, ⟨_, .inr ⟨i, hij, _, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩, Prod.ext (by simp only; linarith) rfl⟩`.
-/
lemma mem_parB (D : D7) (j : ℕ) (hj : D.R.m ≤ j + 1) (τ : D.what₂.Tau) (q : ℚ) (s : Bool) :
    (q, s) ∈ parB (Ptw D) j τ ↔
      s = true ∧ IsEntry (D.hc τ) j (-q - if Odd j then -(1 / 2) else 0) := by
  have hi : ∀ i : Fin D.R.m, (i : ℕ) ≤ j := fun i => by have := i.2; omega
  simp only [parB, dualPar, TPar.Dpar, TPar.block, Ptw, tparRec, tparHC, Finset.mem_image,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, hi, true_or, decide_true, IsEntry]
  generalize (if Odd j then -(1 / 2) else 0 : ℚ) = c
  constructor
  · rintro ⟨_, ⟨_, (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, hij, _, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩, h⟩ <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;> refine ⟨rfl, ?_⟩
    · exact .inl ⟨i, by simp⟩
    · exact .inr (.inl ⟨i, by simp⟩)
    · exact .inr (.inr ⟨i, hij, a, ha, by simp⟩)
  · rintro ⟨rfl, ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, hij, a, ha, h⟩⟩
    · exact ⟨_, ⟨_, .inl (.inl ⟨i, rfl⟩), rfl⟩, Prod.ext (by simp only; linarith) rfl⟩
    · exact ⟨_, ⟨_, .inl (.inr ⟨i, rfl⟩), rfl⟩, Prod.ext (by simp only; linarith) rfl⟩
    · exact ⟨_, ⟨_, .inr ⟨i, hij, _, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩, Prod.ext (by simp only; linarith) rfl⟩

/- English proof (translation)
Break down `h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, -, a, ha, rfl⟩` into its components or cases. Conclude with `P.v_int i`. Conclude with `GlobalTheory.ForcedWeights.entry_int P (.inr (.inl i))`. Conclude with `GlobalTheory.ForcedWeights.entry_int P (.inr (.inr (i, ⟨a, ha⟩)))`.
-/
lemma entry_int {R : Ranks} (P : HCParam R) (j : ℕ) (y : ℚ) (h : IsEntry P j y) : ∃ z : ℤ, y = z := by
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, -, a, ha, rfl⟩
  · exact P.v_int i
  · exact GlobalTheory.ForcedWeights.entry_int P (.inr (.inl i))
  · exact GlobalTheory.ForcedWeights.entry_int P (.inr (.inr (i, ⟨a, ha⟩)))

/- English proof (translation)
Establish `h0` using `P.gap_be k`. Break down `h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, hi, a, ha, rfl⟩` into its components or cases. Use `GlobalTheory.ForcedWeights.negb_lt_v P i k` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `GlobalTheory.ForcedWeights.be P (i := i) (j := k) (by have := i.2; rw [Fin.le_def]; omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `GlobalTheory.ForcedWeights.eb P (i := i) (j := k) hi` as an intermediate fact. Establish `ha' : (a : ℚ) + 1 ≤ R.t` using `by exact_mod_cast ha`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma entry_ge {R : Ranks} (P : HCParam R) (k : Fin R.m) (hk : (k : ℕ) + 1 = R.m) (y : ℚ)
    (h : IsEntry P k y) : -P.e k + ((R.t : ℚ) + 3) / 2 ≤ y := by
  have h0 := P.gap_be k
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, hi, a, ha, rfl⟩
  · have := GlobalTheory.ForcedWeights.negb_lt_v P i k
    linarith
  · have := GlobalTheory.ForcedWeights.be P (i := i) (j := k) (by have := i.2; rw [Fin.le_def]; omega)
    linarith
  · have := GlobalTheory.ForcedWeights.eb P (i := i) (j := k) hi
    have ha' : (a : ℚ) + 1 ≤ R.t := by exact_mod_cast ha
    linarith

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h | ⟨i, -, h⟩)`. Conclude with `.inl (.inl h)`. Conclude with `.inl (.inr (.inl h))`. Distinguish the cases in `hi : (i : ℕ) < k`.

Conclude with `.inl (.inr (.inr ⟨i, hi, h⟩))`. Establish `: i = k` using `Fin.ext (by have := i.2; omega)`. Substitute `this` using the available equality. Conclude with `.inr h`. Introduce and unpack `((h | h | ⟨i, -, h⟩) | h)`.

Conclude with `.inl h`. Conclude with `.inr (.inl h)`. Conclude with `.inr (.inr ⟨i, i.2, h⟩)`. Conclude with `.inr (.inr ⟨k, k.2, h⟩)`.
-/
lemma entry_succ {R : Ranks} (P : HCParam R) (k : Fin R.m) (hk : (k : ℕ) + 1 = R.m) (y : ℚ) :
    IsEntry P R.m y ↔ IsEntry P k y ∨ ∃ a : ℕ, a < R.t ∧ y = -P.e k + ((R.t : ℚ) - 1) / 2 - a := by
  constructor
  · rintro (h | h | ⟨i, -, h⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · by_cases hi : (i : ℕ) < k
      · exact .inl (.inr (.inr ⟨i, hi, h⟩))
      · have : i = k := Fin.ext (by have := i.2; omega)
        subst this
        exact .inr h
  · rintro ((h | h | ⟨i, -, h⟩) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨i, i.2, h⟩)
    · exact .inr (.inr ⟨k, k.2, h⟩)

/- English proof (translation)
Introduce `D k τ n N lam ε lam' ε' hk hn hN ⟨hl, q, hq, hS⟩ ⟨hl', q', hq', hS'⟩`. Substitute `hN` using the available equality. Take `⟨s, hs⟩` from `D.R.t_odd`. Take `⟨m', hm'⟩` from `D.R.m_even`. Take `⟨k', hk'⟩` from `D.R.k_even`.

Take `⟨e, he⟩` from `(D.hc τ).e_int k`. Establish `hm2` using `D.R.two_le_m`. Establish `hkodd : Odd (k : ℕ)` using `⟨m' - 1, by omega⟩`. Establish `hkne : ¬ Even (k : ℕ)` using `Nat.not_even_iff_odd.mpr hkodd`. Establish `hmno : ¬ Odd D.R.m` using `Nat.not_odd_iff_even.mpr D.R.m_even`.

Establish `hnev : Even n`. Rewrite using `[hn]`. Use `Odd.add_odd ⟨k' + m' - 1, ?_⟩ (hkodd.mul D.R.t_odd)` and prove the remaining obligations. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.

Take `⟨p, hp⟩` from `hnev`. Establish `hsQ : (D.R.t : ℚ) = 2 * s + 1` using `by exact_mod_cast hs`. Establish `hpQ : (n : ℚ) = 2 * p` using `by rw [hp]; push_cast; ring`. Apply the tactic sequence `have A : ∀ x b, (∃ a, (q a, ε a) = (x, b)) ↔ b = true ∧ IsEntry (D.hc τ) k (-x + 1 / 2) := by`. Introduce `x b`.

Use `mem_parB D k (by omega) τ x b` as an intermediate fact. Rewrite `this` using `[hS, if_pos hkodd, sub_neg_eq_add]`. Simplify using `using this`. Apply the tactic sequence `have B : ∀ x b, (∃ a, (q' a, ε' a) = (x, b)) ↔ b = true ∧ IsEntry (D.hc τ) D.R.m (-x) := by`. Introduce `x b`.

Use `mem_parB D D.R.m (by omega) τ x b` as an intermediate fact. Rewrite `this` using `[hS', if_neg hmno, sub_zero]`. Simplify using `using this`. Establish `hε : ∀ a, ε a = true` using `fun a => ((A _ _).mp ⟨a, rfl⟩).1`. Establish `hε' : ∀ a, ε' a = true` using `fun a => ((B _ _).mp ⟨a, rfl⟩).1`.

Apply the tactic sequence `have hE : ∀ a, IsEntry (D.hc τ) k (-q a + 1 / 2) := fun a => ((A _ _).mp ⟨a, rfl⟩).2`. Use `choose z hz using fun a => entry_int _ _ _ (hE a)`. Use `⟨funext hε, funext hε', -e + p, e - p - s, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [expS, if_neg hkne, he, hpQ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [expT, if_neg hkne, he]`. Use `push_cast`. Rewrite using `[hpQ, hsQ]`. Expand and normalize the polynomial expressions, which then agree.

Use `partition e s p (by exact_mod_cast hs) (by omega) z lam hl ?_ ?_ lam' hl' ?_` and prove the remaining obligations. Introduce `a`. Establish `: q a = -(z a : ℚ) + 1 / 2` using `by linarith [hz a]`. Rewrite using `[hq, this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `a`. Establish `h1` using `entry_ge _ k hk _ (hE a)`. Rewrite `h1` using `[hz, he, hsQ]`. Establish `h2 : -(e : ℚ) + s + 2 ≤ z a` using `by linarith`.

Conclude with `h2` after adjusting the coercions. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`. Break down `(entry_succ _ k hk _).mp ((B _ _).mp ⟨b, rfl⟩).2 with h | ⟨a, ha, h⟩` into its components or cases.

Take `⟨a, ha⟩` from `(A (q' b + 1 / 2) true).mpr ⟨rfl, by convert h using 1; ring⟩`. Use `.inl ⟨a, ?_⟩` and prove the remaining obligations. Establish `h1 : q a = q' b + 1 / 2` using `(Prod.mk.inj ha).1`. Establish `h2 : q' b = -(z a : ℚ)` using `by linarith [hz a]`. Rewrite using `[hq', h2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `.inr ⟨D.R.t - 1 - a, by omega, ?_⟩` and prove the remaining obligations. Establish `h2 : q' b = e - s + a` using `by rw [he, hsQ] at h; linarith`. Establish `h3 : ((D.R.t - 1 - a : ℕ) : ℤ) = 2 * s - a` using `by omega`.

Rewrite using `[hq', h2, h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `(⟨a, rfl⟩ | ⟨c, hc, rfl⟩)`. Take `⟨b, hb⟩` from `(B (-(z a : ℚ)) true).mpr ⟨rfl, (entry_succ _ k hk _).mpr (.inl (by rw [neg_neg, ← hz]; exact hE a))⟩`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hq', (Prod.mk.inj hb).1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ((D.R.t - 1 - c : ℕ) : ℚ) = 2 * s - c`.

Establish `: ((D.R.t - 1 - c : ℕ) : ℤ) = 2 * s - c` using `by omega`. Conclude with `this` after adjusting the coercions. Take `⟨b, hb⟩` from `(B ((e : ℚ) + s - c) true).mpr ⟨rfl, (entry_succ _ k hk _).mpr (.inr ⟨D.R.t - 1 - c, by omega, by`. Rewrite using `[h3, he, hsQ]`. Use the proof step `ring⟩)⟩`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hq', (Prod.mk.inj hb).1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lastStep_param : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), (k : ℕ) + 1 = D.R.m → n = D.R.r + k * D.R.t → N = n + D.R.t → IsEnum (parB (Ptw D) k τ) lam ε → IsEnum (parB (Ptw D) D.R.m τ) lam' ε' → ε = allPos n ∧ ε' = allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = expS D k τ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + expT D k τ) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (allPos n) lam a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (allPos N) lam' b = -(x₁ : ℝ) - ν (Fin.rev b) := by
  intro D k τ n N lam ε lam' ε' hk hn hN ⟨hl, q, hq, hS⟩ ⟨hl', q', hq', hS'⟩
  subst hN
  obtain ⟨s, hs⟩ := D.R.t_odd
  obtain ⟨m', hm'⟩ := D.R.m_even
  obtain ⟨k', hk'⟩ := D.R.k_even
  obtain ⟨e, he⟩ := (D.hc τ).e_int k
  have hm2 := D.R.two_le_m
  have hkodd : Odd (k : ℕ) := ⟨m' - 1, by omega⟩
  have hkne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hkodd
  have hmno : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
  have hnev : Even n := by
    rw [hn]
    refine Odd.add_odd ⟨k' + m' - 1, ?_⟩ (hkodd.mul D.R.t_odd)
    unfold Ranks.r; omega
  obtain ⟨p, hp⟩ := hnev
  have hsQ : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hpQ : (n : ℚ) = 2 * p := by rw [hp]; push_cast; ring
  have A : ∀ x b, (∃ a, (q a, ε a) = (x, b)) ↔ b = true ∧ IsEntry (D.hc τ) k (-x + 1 / 2) := by
    intro x b
    have := mem_parB D k (by omega) τ x b
    rw [hS, if_pos hkodd, sub_neg_eq_add] at this
    simpa using this
  have B : ∀ x b, (∃ a, (q' a, ε' a) = (x, b)) ↔ b = true ∧ IsEntry (D.hc τ) D.R.m (-x) := by
    intro x b
    have := mem_parB D D.R.m (by omega) τ x b
    rw [hS', if_neg hmno, sub_zero] at this
    simpa using this
  have hε : ∀ a, ε a = true := fun a => ((A _ _).mp ⟨a, rfl⟩).1
  have hε' : ∀ a, ε' a = true := fun a => ((B _ _).mp ⟨a, rfl⟩).1
  have hE : ∀ a, IsEntry (D.hc τ) k (-q a + 1 / 2) := fun a => ((A _ _).mp ⟨a, rfl⟩).2
  choose z hz using fun a => entry_int _ _ _ (hE a)
  refine ⟨funext hε, funext hε', -e + p, e - p - s, ?_, ?_, ?_⟩
  · simp only [expS, if_neg hkne, he, hpQ]
    push_cast
    ring
  · simp only [expT, if_neg hkne, he]
    push_cast
    rw [hpQ, hsQ]
    ring
  refine partition e s p (by exact_mod_cast hs) (by omega) z lam hl ?_ ?_ lam' hl' ?_
  · intro a
    have : q a = -(z a : ℚ) + 1 / 2 := by linarith [hz a]
    rw [hq, this]
    push_cast
    ring
  · intro a
    have h1 := entry_ge _ k hk _ (hE a)
    rw [hz, he, hsQ] at h1
    have h2 : -(e : ℚ) + s + 2 ≤ z a := by linarith
    exact_mod_cast h2
  · intro x
    constructor
    · rintro ⟨b, rfl⟩
      rcases (entry_succ _ k hk _).mp ((B _ _).mp ⟨b, rfl⟩).2 with h | ⟨a, ha, h⟩
      · obtain ⟨a, ha⟩ := (A (q' b + 1 / 2) true).mpr ⟨rfl, by convert h using 1; ring⟩
        refine .inl ⟨a, ?_⟩
        have h1 : q a = q' b + 1 / 2 := (Prod.mk.inj ha).1
        have h2 : q' b = -(z a : ℚ) := by linarith [hz a]
        rw [hq', h2]
        push_cast
        ring
      · refine .inr ⟨D.R.t - 1 - a, by omega, ?_⟩
        have h2 : q' b = e - s + a := by rw [he, hsQ] at h; linarith
        have h3 : ((D.R.t - 1 - a : ℕ) : ℤ) = 2 * s - a := by omega
        rw [hq', h2, h3]
        push_cast
        ring
    · rintro (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
      · obtain ⟨b, hb⟩ := (B (-(z a : ℚ)) true).mpr
          ⟨rfl, (entry_succ _ k hk _).mpr (.inl (by rw [neg_neg, ← hz]; exact hE a))⟩
        refine ⟨b, ?_⟩
        rw [hq', (Prod.mk.inj hb).1]
        push_cast
        ring
      · have h3 : ((D.R.t - 1 - c : ℕ) : ℚ) = 2 * s - c := by
          have : ((D.R.t - 1 - c : ℕ) : ℤ) = 2 * s - c := by omega
          exact_mod_cast this
        obtain ⟨b, hb⟩ := (B ((e : ℚ) + s - c) true).mpr
          ⟨rfl, (entry_succ _ k hk _).mpr (.inr ⟨D.R.t - 1 - c, by omega, by
            rw [h3, he, hsQ]; ring⟩)⟩
        refine ⟨b, ?_⟩
        rw [hq', (Prod.mk.inj hb).1]
        push_cast
        ring

end GlobalTheory.LastStepParam
