import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine

noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights

variable {n : ℕ}

def t0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def tB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ :=
  t0 a b - 2 * (if (a, b) ∈ B then 1 else 0) + 2 * (if (b, a) ∈ B then 1 else 0)

structure IsT (t : Fin n → Fin n → ℝ) : Prop where
  diag : ∀ a, t a a = 0
  anti : ∀ a b, t b a = - t a b
  pm : ∀ a b, a ≠ b → t a b = 1 ∨ t a b = -1

/- English proof (translation)
Simplify using `[t0] anti a b := by`. Unfold `t0`. Apply the tactic sequence `split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num`. Use `pm a b h := by`. Unfold `t0`.

Establish `: (a : ℕ) ≠ b` using `fun e => h (Fin.ext e)`. Apply the tactic sequence `split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num`.
-/
theorem isTournament_standard : IsT (t0 (n := n)) where
  diag a := by simp [t0]
  anti a b := by
    unfold t0
    split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num
  pm a b h := by
    unfold t0
    have : (a : ℕ) ≠ b := fun e => h (Fin.ext e)
    split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num

/- English proof (translation)
Simplify using `[tB, t0] anti a b := by`. Use `isTournament_standard.anti a b` as an intermediate fact. Simplify using `only [tB, this]`. Expand and normalize the polynomial expressions, which then agree. Use `pm a b h := by`.

Establish `h1 : (a, b) ∈ B → (b, a) ∉ B` using `fun x y => by`. Use `hB _ x` as an intermediate fact. Use `hB _ y` as an intermediate fact. Simplify using `only [Fin.lt_def] at *`. Use linear arithmetic over natural numbers and integers.

Establish `h2 : (a, b) ∈ B → t0 a b = 1` using `fun x => by`. Use `hB _ x` as an intermediate fact. Simplify using `only at this`. Simplify using `[t0, this]`. Establish `h3 : (b, a) ∈ B → t0 a b = -1` using `fun x => by`.

Use `hB _ x` as an intermediate fact. Simplify using `only at this`. Establish `h' : ¬ a < b` using `not_lt.2 this.le`. Simplify using `[t0, this, h']`. Establish `h4` using `isTournament_standard.pm a b h`.

Simplify using `only [tB]`. Distinguish the cases in `x : (a, b) ∈ B`. Simplify using `[x, h1 x, h2 x]`. Evaluate the numerical expressions. Distinguish the cases in `y : (b, a) ∈ B`.

Simplify using `[x, y, h3 y]`. Evaluate the numerical expressions. Simplify `h4` using `[x, y]`.
-/
theorem isT_tB {B : Finset (Fin n × Fin n)} (hB : ∀ p ∈ B, p.1 < p.2) : IsT (tB B) where
  diag a := by simp [tB, t0]
  anti a b := by
    have := isTournament_standard.anti a b
    simp only [tB, this]
    ring
  pm a b h := by
    have h1 : (a, b) ∈ B → (b, a) ∉ B := fun x y => by
      have := hB _ x; have := hB _ y; simp only [Fin.lt_def] at *; omega
    have h2 : (a, b) ∈ B → t0 a b = 1 := fun x => by
      have := hB _ x; simp only at this; simp [t0, this]
    have h3 : (b, a) ∈ B → t0 a b = -1 := fun x => by
      have := hB _ x; simp only at this
      have h' : ¬ a < b := not_lt.2 this.le
      simp [t0, this, h']
    have h4 := isTournament_standard.pm a b h
    simp only [tB]
    by_cases x : (a, b) ∈ B
    · simp [x, h1 x, h2 x]; norm_num
    · by_cases y : (b, a) ∈ B
      · simp [x, y, h3 y]; norm_num
      · simpa [x, y] using h4

def cyc (t : Fin n → Fin n → ℝ) (a b c : Fin n) : ℝ := t a b * t a c + t b c * t b a + t c a * t c b

/- English proof (translation)
Unfold `cyc`. Use `split_ifs with e`. Substitute `e` using the available equality. Simplify using `[h.diag]`. Rewrite using `[h.diag]`.

Apply the tactic sequence `rcases h.pm c a e with x | x <;> simp [x, h.anti c a, h.diag]`.
-/
theorem cyc_eq {t : Fin n → Fin n → ℝ} (h : IsT t) (a c : Fin n) : cyc t a a c = if c = a then 0 else 1 := by
  unfold cyc
  split_ifs with e
  · subst e; simp [h.diag]
  · rw [h.diag]
    rcases h.pm c a e with x | x <;> simp [x, h.anti c a, h.diag]

/- English proof (translation)
Unfold `cyc`. Rewrite using `[h.anti a b, h.anti b c, h.anti c a]`. Apply the tactic sequence `rcases h.pm a b hab with x | x <;> rcases h.pm b c hbc with y | y <;> rcases h.pm c a hca with z | z <;>`. Apply the tactic sequence `rw [x, y, z] <;> norm_num`.
-/
theorem cyc_le {t : Fin n → Fin n → ℝ} (h : IsT t) {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    cyc t a b c ≤ 1 := by
  unfold cyc
  rw [h.anti a b, h.anti b c, h.anti c a]
  rcases h.pm a b hab with x | x <;> rcases h.pm b c hbc with y | y <;> rcases h.pm c a hca with z | z <;>
    rw [x, y, z] <;> norm_num

/- English proof (translation)
Establish `h1 : (a : ℕ) ≠ b` using `fun e => hab (Fin.ext e)`. Establish `h2 : (b : ℕ) ≠ c` using `fun e => hbc (Fin.ext e)`. Establish `h3 : (c : ℕ) ≠ a` using `fun e => hca (Fin.ext e)`. Unfold `cyc t0`. Apply the tactic sequence `split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num`.
-/
theorem cyclic_standard_tournament {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : cyc t0 a b c = 1 := by
  have h1 : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  have h2 : (b : ℕ) ≠ c := fun e => hbc (Fin.ext e)
  have h3 : (c : ℕ) ≠ a := fun e => hca (Fin.ext e)
  unfold cyc t0
  split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[cyc_eq h, cyc_eq isTournament_standard]`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality.

Establish `e : ∀ t : Fin n → Fin n → ℝ, cyc t a b b = cyc t b b a` using `fun t => by unfold cyc; ring`. Rewrite using `[e, e, cyc_eq h, cyc_eq isTournament_standard]`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Establish `e : ∀ t : Fin n → Fin n → ℝ, cyc t c b c = cyc t c c b` using `fun t => by unfold cyc; ring`.

Rewrite using `[e, e, cyc_eq h, cyc_eq isTournament_standard]`. Rewrite using `[cyclic_standard_tournament hab hbc hca]`. Conclude with `cyc_le h hab hbc hca`.
-/
theorem cyc_compare {t : Fin n → Fin n → ℝ} (h : IsT t) (a b c : Fin n) : cyc t a b c ≤ cyc t0 a b c := by
  by_cases hab : a = b
  · subst hab; rw [cyc_eq h, cyc_eq isTournament_standard]
  by_cases hbc : b = c
  · subst hbc
    have e : ∀ t : Fin n → Fin n → ℝ, cyc t a b b = cyc t b b a := fun t => by unfold cyc; ring
    rw [e, e, cyc_eq h, cyc_eq isTournament_standard]
  by_cases hca : c = a
  · subst hca
    have e : ∀ t : Fin n → Fin n → ℝ, cyc t c b c = cyc t c c b := fun t => by unfold cyc; ring
    rw [e, e, cyc_eq h, cyc_eq isTournament_standard]
  rw [cyclic_standard_tournament hab hbc hca]
  exact cyc_le h hab hbc hca

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem rot (F : Fin n → Fin n → Fin n → ℝ) : ∑ a, ∑ b, ∑ c, F b c a = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `h0 : ∑ c, (∑ b, t c b) ^ 2 = ∑ a, ∑ b, ∑ c, t a b * t a c`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[sq, Finset.sum_mul_sum]`. Establish `h1` using `rot (fun a b c => t a b * t a c)`. Establish `h2` using `rot (fun a b c => t c a * t c b)`.

Simplify using `only [cyc, Finset.sum_add_distrib]`. Rewrite using `[h0, h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem three_mul (t : Fin n → Fin n → ℝ) :
    3 * ∑ c, (∑ b, t c b) ^ 2 = ∑ a, ∑ b, ∑ c, cyc t a b c := by
  have h0 : ∑ c, (∑ b, t c b) ^ 2 = ∑ a, ∑ b, ∑ c, t a b * t a c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sq, Finset.sum_mul_sum]
  have h1 := rot (fun a b c => t a b * t a c)
  have h2 := rot (fun a b c => t c a * t c b)
  simp only [cyc, Finset.sum_add_distrib]
  rw [h0, h1, ← h2]
  ring

/- English proof (translation)
Establish `: 3 * ∑ c, (∑ b, t c b) ^ 2 ≤ 3 * ∑ c : Fin n, (∑ b : Fin n, t0 c b) ^ 2`. Rewrite using `[three_mul, three_mul]`. Conclude with `Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => cyc_compare h a b c`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem score_sq_le {t : Fin n → Fin n → ℝ} (h : IsT t) :
    ∑ c, (∑ b, t c b) ^ 2 ≤ ∑ c : Fin n, (∑ b : Fin n, t0 c b) ^ 2 := by
  have : 3 * ∑ c, (∑ b, t c b) ^ 2 ≤ 3 * ∑ c : Fin n, (∑ b : Fin n, t0 c b) ^ 2 := by
    rw [three_mul, three_mul]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => cyc_compare h a b c
  linarith

/- English proof (translation)
Establish `e : ∀ b : Fin n, t0 c b = (if b ∈ Finset.Ioi c then 1 else 0) - (if b ∈ Finset.Iio c then 1 else 0)`. Introduce `b`. Simplify using `only [t0, Finset.mem_Ioi, Finset.mem_Iio]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num`. Simplify using `only [e, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_Ioi, Fin.card_Iio, rhoV]`.

Use `c.2` as an intermediate fact. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_standard_tournament (c : Fin n) : ∑ b, t0 c b = 2 * rhoV n c := by
  have e : ∀ b : Fin n, t0 c b = (if b ∈ Finset.Ioi c then 1 else 0) - (if b ∈ Finset.Iio c then 1 else 0) := by
    intro b
    simp only [t0, Finset.mem_Ioi, Finset.mem_Iio]
    split_ifs <;> first | (exfalso; simp only [Fin.lt_def] at *; omega) | norm_num
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Fin.card_Ioi, Fin.card_Iio, rhoV]
  have := c.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/- English proof (translation)
Use `Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hp`. Substitute `h2` using the available equality. Simplify using `using h1`.

Introduce `p hp q hq e`. Take `⟨_, h2⟩` from `Finset.mem_filter.1 hp`. Take `⟨_, h4⟩` from `Finset.mem_filter.1 hq`. Conclude with `Prod.ext (h2.trans h4.symm) e`. Introduce `b hb`.

Conclude with `⟨(c, b), by simpa using hb, rfl⟩`.
-/
theorem card_fst (B : Finset (Fin n × Fin n)) (c : Fin n) :
    (B.filter fun p => p.1 = c).card = (univ.filter fun b => (c, b) ∈ B).card := by
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    subst h2
    simpa using h1
  · intro p hp q hq e
    obtain ⟨_, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨_, h4⟩ := Finset.mem_filter.1 hq
    exact Prod.ext (h2.trans h4.symm) e
  · intro b hb
    exact ⟨(c, b), by simpa using hb, rfl⟩

/- English proof (translation)
Use `Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Take `⟨h1, h2⟩` from `Finset.mem_filter.1 hp`. Substitute `h2` using the available equality. Simplify using `using h1`.

Introduce `p hp q hq e`. Take `⟨_, h2⟩` from `Finset.mem_filter.1 hp`. Take `⟨_, h4⟩` from `Finset.mem_filter.1 hq`. Conclude with `Prod.ext e (h2.trans h4.symm)`. Introduce `b hb`.

Conclude with `⟨(b, c), by simpa using hb, rfl⟩`.
-/
theorem card_snd (B : Finset (Fin n × Fin n)) (c : Fin n) :
    (B.filter fun p => p.2 = c).card = (univ.filter fun b => (b, c) ∈ B).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    subst h2
    simpa using h1
  · intro p hp q hq e
    obtain ⟨_, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨_, h4⟩ := Finset.mem_filter.1 hq
    exact Prod.ext e (h2.trans h4.symm)
  · intro b hb
    exact ⟨(b, c), by simpa using hb, rfl⟩

/- English proof (translation)
Simplify using `only [wtB, card_fst, card_snd]`. Simplify using `only [tB, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_standard_tournament, Finset.card_filter]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_tB (B : Finset (Fin n × Fin n)) (c : Fin n) : ∑ b, tB B c b = 2 * rhoV n c - 2 * wtB B c := by
  simp only [wtB, card_fst, card_snd]
  simp only [tB, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_standard_tournament, Finset.card_filter]
  push_cast
  ring

/- English proof (translation)
Establish `e : ∀ c, f c * wtB B c = ∑ p ∈ B, ((if p.1 = c then f c else 0) - (if p.2 = c then f c else 0))`. Introduce `c`. Simplify using `only [wtB, Finset.card_filter, Finset.sum_sub_distrib]`. Use `push_cast`. Rewrite using `[mul_sub, Finset.mul_sum, Finset.mul_sum]`.

Simplify using the standard rewrite rules. Simplify using `only [e]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `[Finset.sum_sub_distrib]`.
-/
theorem sum_wtB (B : Finset (Fin n × Fin n)) (f : Fin n → ℝ) :
    ∑ c, f c * wtB B c = ∑ p ∈ B, (f p.1 - f p.2) := by
  have e : ∀ c, f c * wtB B c = ∑ p ∈ B, ((if p.1 = c then f c else 0) - (if p.2 = c then f c else 0)) := by
    intro c
    simp only [wtB, Finset.card_filter, Finset.sum_sub_distrib]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Finset.sum_sub_distrib]

/- English proof (translation)
Establish `h` using `score_sq_le (isT_tB hB)`. Simplify using `only [sum_tB, sum_standard_tournament] at h`. Establish `e : ∑ c, (2 * rhoV n c - 2 * wtB B c) ^ 2 = ∑ c, (2 * rhoV n c) ^ 2 - 8 * ∑ c, rhoV n c * wtB B c + 4 * ∑ c, wtB B c ^ 2`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`.

Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wt_sq_le {B : Finset (Fin n × Fin n)} (hB : ∀ p ∈ B, p.1 < p.2) :
    ∑ c, wtB B c ^ 2 ≤ 2 * ∑ c, rhoV n c * wtB B c := by
  have h := score_sq_le (isT_tB hB)
  simp only [sum_tB, sum_standard_tournament] at h
  have e : ∑ c, (2 * rhoV n c - 2 * wtB B c) ^ 2 =
      ∑ c, (2 * rhoV n c) ^ 2 - 8 * ∑ c, rhoV n c * wtB B c + 4 * ∑ c, wtB B c ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e] at h
  linarith

/- English proof (translation)
Establish `hab : a ≤ b`. Assume the negation of the conclusion as `x`. Conclude with `absurd (hm (not_le.1 x).le) (not_le.2 h)`. Establish `h1 : (lam b : ℝ) ≤ lam a` using `by exact_mod_cast hl hab`. Establish `h2 : (univ.filter fun x => lev b < lev x).card + 1 ≤ (univ.filter fun x => lev a < lev x).card`.

Rewrite using `[← Finset.card_insert_of_notMem (a := b) (s := univ.filter fun x => lev b < lev x) (by simp)]`. Use `Finset.card_le_card fun x hx => ?_` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Simplify using `using h`. Use `(Finset.mem_filter.1 hx).2` as an intermediate fact.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : (univ.filter fun x => lev x < lev a).card + 1 ≤ (univ.filter fun x => lev x < lev b).card`. Rewrite using `[← Finset.card_insert_of_notMem (a := a) (s := univ.filter fun x => lev x < lev a) (by simp)]`. Use `Finset.card_le_card fun x hx => ?_` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Simplify using `using h`. Use `(Finset.mem_filter.1 hx).2` as an intermediate fact. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers.

Establish `h2' : ((univ.filter fun x => lev b < lev x).card : ℝ) + 1 ≤ (univ.filter fun x => lev a < lev x).card`. Conclude with `h2` after adjusting the coercions. Establish `h3' : ((univ.filter fun x => lev x < lev a).card : ℝ) + 1 ≤ (univ.filter fun x => lev x < lev b).card`. Conclude with `h3` after adjusting the coercions. Simplify using `only [muQ, rhoU]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem muQ_lt {lam : Fin n → ℤ} (hl : Antitone lam) {lev : Fin n → ℕ} (hm : Monotone lev) {a b : Fin n}
    (h : lev a < lev b) : muQ lam lev b < muQ lam lev a := by
  have hab : a ≤ b := by
    by_contra x
    exact absurd (hm (not_le.1 x).le) (not_le.2 h)
  have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hl hab
  have h2 : (univ.filter fun x => lev b < lev x).card + 1 ≤ (univ.filter fun x => lev a < lev x).card := by
    rw [← Finset.card_insert_of_notMem (a := b) (s := univ.filter fun x => lev b < lev x) (by simp)]
    refine Finset.card_le_card fun x hx => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using h
    · have := (Finset.mem_filter.1 hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  have h3 : (univ.filter fun x => lev x < lev a).card + 1 ≤ (univ.filter fun x => lev x < lev b).card := by
    rw [← Finset.card_insert_of_notMem (a := a) (s := univ.filter fun x => lev x < lev a) (by simp)]
    refine Finset.card_le_card fun x hx => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using h
    · have := (Finset.mem_filter.1 hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  have h2' : ((univ.filter fun x => lev b < lev x).card : ℝ) + 1 ≤ (univ.filter fun x => lev a < lev x).card := by
    exact_mod_cast h2
  have h3' : ((univ.filter fun x => lev x < lev a).card : ℝ) + 1 ≤ (univ.filter fun x => lev x < lev b).card := by
    exact_mod_cast h3
  simp only [muQ, rhoU]
  linarith

/- English proof (translation)
Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, Function.comp]`. Conclude with `Equiv.sum_comp w fun a => x a * x a`.
-/
theorem nsq_comp (x : Fin n → ℝ) (w : Equiv.Perm (Fin n)) : Formalism.REAL.nsq (x ∘ w) = Formalism.REAL.nsq x := by
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Function.comp]
  exact Equiv.sum_comp w fun a => x a * x a

/- English proof (translation)
Take `⟨B, hne, hB, -, w, hw⟩` from `hν`. Establish `hpos : ∀ p ∈ B, p.1 < p.2` using `fun p hp => by`. Assume the negation of the conclusion as `x`. Conclude with `absurd (hlev.1 (not_lt.1 x)) (not_le.2 (hB p hp))`. Establish `h1` using `wt_sq_le hpos`.

Establish `h2 : 0 < ∑ c, muQ lam lev c * wtB B c`. Rewrite using `[sum_wtB]`. Conclude with `Finset.sum_pos (fun p hp => sub_pos.2 (muQ_lt hl hlev.1 (hB p hp))) hne`. Rewrite using `[hw, nsq_comp]`. Establish `e : Formalism.REAL.nsq (muQ lam lev + rhoV n - wtB B) = Formalism.REAL.nsq (muQ lam lev + rhoV n) - 2 * ∑ c, muQ lam lev c * wtB B c - 2 * ∑ c, rhoV n c * wtB B c + ∑ c, wtB B c ^ 2`.

Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nsq_lt (n : ℕ) (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hlev : IsLev lam lev)
    (ν : Fin n → ℝ) (hν : IsSecondTypeWeight lam lev ν) : Formalism.REAL.nsq (ν + rhoV n) < Formalism.REAL.nsq (muQ lam lev + rhoV n) := by
  obtain ⟨B, hne, hB, -, w, hw⟩ := hν
  have hpos : ∀ p ∈ B, p.1 < p.2 := fun p hp => by
    by_contra x
    exact absurd (hlev.1 (not_lt.1 x)) (not_le.2 (hB p hp))
  have h1 := wt_sq_le hpos
  have h2 : 0 < ∑ c, muQ lam lev c * wtB B c := by
    rw [sum_wtB]
    exact Finset.sum_pos (fun p hp => sub_pos.2 (muQ_lt hl hlev.1 (hB p hp))) hne
  rw [hw, nsq_comp]
  have e : Formalism.REAL.nsq (muQ lam lev + rhoV n - wtB B) = Formalism.REAL.nsq (muQ lam lev + rhoV n)
      - 2 * ∑ c, muQ lam lev c * wtB B c - 2 * ∑ c, rhoV n c * wtB B c + ∑ c, wtB B c ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights
