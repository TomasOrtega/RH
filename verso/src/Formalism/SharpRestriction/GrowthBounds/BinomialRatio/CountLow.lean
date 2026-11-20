import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountUp

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

def IsPair {s r : ℕ} (A : ℕ) (Ai Ci : Fin s → ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) : Prop :=
  IsChain (kLetters A Ai Ci) mu ∧ Inter (mu (Fin.last _)) lam

section Data

variable {s r : ℕ} (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ)

def pairC (l : ℕ) : ℤ := mu (finPos (2 * s + 1) (2 * l + 1)) 0

def pairTail (n : ℕ) : ℤ := ∑ t : Fin r, mu (finPos (2 * s + 1) n) t.succ

def pairRho [NeZero r] (i : ℕ) : ℤ := mu (finPos (2 * s + 1) (2 * i + 2)) (0 : Fin r).succ

def pairO (Ai : Fin s → ℕ) (i : Fin s) : ℤ := pairC mu i + Ai i - pairC mu (i + 1)

def pairW (i : ℕ) : ℤ := pairTail mu (2 * i + 2) - pairTail mu (2 * i + 1)

def pairSg (Ai : Fin s → ℕ) (i : Fin s) : ℤ := pairO mu Ai i - pairW mu i

def pairN (i : ℕ) : ℤ := -(if h : r - s + i < r then lam ⟨r - s + i, h⟩ else 0)

def pairD : ℤ := ∑ t, lam t - pairTail mu (2 * s + 1)

end Data

def KeptPair (p : ℕ) (La : ℝ) {s r : ℕ} [NeZero r] (Ai Ci : Fin s → ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ)
    (lam : Fin r → ℤ) : Prop :=
  ∀ i : Fin s,
    ((pairO mu Ai i - pairRho mu i : ℤ) : ℝ) + 4 * ((Ai i : ℝ) + r) / (p : ℝ) ^ 2 ≤
        La * max ((pairC mu i : ℤ) : ℝ) (Ai i : ℝ) / ((r : ℝ) + 1) ∧
      (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ((pairN (s := s) lam i : ℤ) : ℝ)

open Classical in

def keptPairSum (p : ℕ) (La : ℝ) {s r : ℕ} [NeZero r] (A : ℕ) (Ai Ci : Fin s → ℕ) : ℚ :=
  ∑ᶠ x : (Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ),
    if IsPair A Ai Ci x.1 x.2 ∧ KeptPair p La Ai Ci x.1 x.2 then wdim x.2 else 0

abbrev clA (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) :
    Fin (segS X.TT j) → ℕ := fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i

abbrev clC (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) :
    Fin (segS X.TT j) → ℕ := fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i

def TailAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        (1 - Real.exp (-(X.La C0) / 8)) *
            (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ) ≤
          ((keptPairSum X.p (X.La C0) (r := X.m) A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℚ) : ℝ)

def MatchAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      keptPairSum X.p (X.La C0) (r := X.m) ((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat
          (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) *
        (∑ jp ∈ range (⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k⌋₊ + 1),
          (sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℚ)) ≤
      chainCount C0 CE1 CE2 X j m rz ry

def RestTail : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => TailAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestMatch : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => MatchAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

/- English proof (translation)
Establish `h : (y + (n + 1)) * sd n y = sd (n + 1) y * (n + 1)`. Simplify using `only [sd]`. Rewrite using `[show y + (n + 1) = (y + n) + 1 by omega]`. Conclude with `Nat.add_one_mul_choose_eq (y + n) n`. Conclude with `h` after adjusting the coercions.
-/
theorem cl_sd_step (y n : ℕ) : ((y : ℝ) + ((n : ℝ) + 1)) * (sd n y : ℝ) = (sd (n + 1) y : ℝ) * ((n : ℝ) + 1) := by
  have h : (y + (n + 1)) * sd n y = sd (n + 1) y * (n + 1) := by
    simp only [sd]
    rw [show y + (n + 1) = (y + n) + 1 by omega]
    exact Nat.add_one_mul_choose_eq (y + n) n
  exact_mod_cast h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [sd]`. Consider the case `succ n ih`. Establish `ih'` using `ih (fun t h1 h2 => h t h1 (by omega))`. Establish `hs` using `cl_sd_step a n`.

Establish `hs'` using `cl_sd_step b n`. Establish `hn : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Establish `ht` using `h (n + 1) (by omega) le_rfl`. Move the coercions through the operations in `at ht`. Establish `ha0 : (0 : ℝ) ≤ (sd n a : ℝ)` using `Nat.cast_nonneg _`.

Establish `hb0 : (0 : ℝ) ≤ (sd n b : ℝ)` using `Nat.cast_nonneg _`. Use `le_of_mul_le_mul_right ?_ hn` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cl_sd_ratio_le (a b : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ n → (a : ℝ) + t ≤ θ * ((b : ℝ) + t)) : (sd n a : ℝ) ≤ θ ^ n * (sd n b : ℝ) := by
  induction n with
  | zero => simp [sd]
  | succ n ih =>
    have ih' := ih (fun t h1 h2 => h t h1 (by omega))
    have hs := cl_sd_step a n
    have hs' := cl_sd_step b n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht := h (n + 1) (by omega) le_rfl
    push_cast at ht
    have ha0 : (0 : ℝ) ≤ (sd n a : ℝ) := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ (sd n b : ℝ) := Nat.cast_nonneg _
    refine le_of_mul_le_mul_right ?_ hn
    calc (sd (n + 1) a : ℝ) * ((n : ℝ) + 1) = ((a : ℝ) + ((n : ℝ) + 1)) * (sd n a : ℝ) := hs.symm
      _ ≤ (θ * ((b : ℝ) + ((n : ℝ) + 1))) * (θ ^ n * (sd n b : ℝ)) :=
          mul_le_mul ht ih' ha0 (mul_nonneg hθ (by positivity))
      _ = θ ^ (n + 1) * (((b : ℝ) + ((n : ℝ) + 1)) * (sd n b : ℝ)) := by ring
      _ = θ ^ (n + 1) * (sd (n + 1) b : ℝ) * ((n : ℝ) + 1) := by rw [hs']; ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ l ih`. Rewrite using `[Finset.sum_range_succ, ← ih (by omega)]`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`.

Take `⟨g, hg⟩ : ∃ g, B - l = g + 1` from `⟨B - l - 1, by omega⟩`. Establish `hg' : B - (l + 1) = g` using `by omega`. Rewrite using `[hg', hg]`. Simplify using `only [sd, sdXi]`. Establish `e1 : g + 1 + (k + 1) - 1 = g + (k + 1)` using `by omega`.

Establish `e2 : k + 1 - 1 = k` using `by omega`. Establish `e3 : g + 1 + (k + 1) = g + (k + 1) + 1` using `by omega`. Rewrite using `[e1, e2, e3, Nat.choose_succ_succ']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cl_hockey (m B l : ℕ) (hm : 1 ≤ m) (hl : l ≤ B) :
    ∑ jp ∈ range l, sdXi m (B - jp) + sd m (B - l) = sd m B := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ, ← ih (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, B - l = g + 1 := ⟨B - l - 1, by omega⟩
    have hg' : B - (l + 1) = g := by omega
    rw [hg', hg]
    simp only [sd, sdXi]
    have e1 : g + 1 + (k + 1) - 1 = g + (k + 1) := by omega
    have e2 : k + 1 - 1 = k := by omega
    have e3 : g + 1 + (k + 1) = g + (k + 1) + 1 := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ']
    ring

/- English proof (translation)
Use `set J := ⌊La * (B : ℝ) / ((m : ℝ) + 1)⌋₊ with hJ`. Establish `hm1 : (0 : ℝ) < (m : ℝ) + 1` using `by positivity`. Establish `hBr : (m : ℝ) + 1 ≤ (B : ℝ)` using `by exact_mod_cast hB`. Establish `hm4 : (4 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hB0 : (0 : ℝ) ≤ (B : ℝ)` using `Nat.cast_nonneg _`.

Establish `hx0 : 0 ≤ La * (B : ℝ) / ((m : ℝ) + 1)` using `div_nonneg (mul_nonneg hLa0 hB0) hm1.le`. Establish `hxB : La * (B : ℝ) / ((m : ℝ) + 1) ≤ (B : ℝ) / 4`. Rewrite using `[div_le_iff₀ hm1]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hJle : (J : ℝ) ≤ La * (B : ℝ) / ((m : ℝ) + 1)` using `Nat.floor_le hx0`.

Establish `hJlt : La * (B : ℝ) / ((m : ℝ) + 1) < (J : ℝ) + 1` using `Nat.lt_floor_add_one _`. Establish `hJB : J + 1 ≤ B`. Establish `: (J : ℝ) + 1 ≤ B` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hhock` using `cl_hockey m B (J + 1) (by omega) hJB`.

Establish `hBm : (0 : ℝ) < (B : ℝ) + m` using `by positivity`. Establish `hcastBL : ((B - (J + 1) : ℕ) : ℝ) = (B : ℝ) - ((J : ℝ) + 1)`. Rewrite using `[Nat.cast_sub hJB]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `set θ : ℝ := 1 - ((J : ℝ) + 1) / ((B : ℝ) + m) with hθ`. Establish `hLB : (J : ℝ) + 1 ≤ (B : ℝ) + m`. Establish `: ((J + 1 : ℕ) : ℝ) ≤ (B : ℝ)` using `by exact_mod_cast hJB`. Move the coercions through the operations in `at this`. Establish `: (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hθ0 : 0 ≤ θ`. Rewrite using `[hθ, sub_nonneg, div_le_iff₀ hBm]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hratio : (sd m (B - (J + 1)) : ℝ) ≤ θ ^ m * (sd m B : ℝ)`.

Apply `cl_sd_ratio_le _ _ θ hθ0 m` to reduce the goal to its premises. Introduce `t _ htm`. Rewrite using `[hcastBL]`. Establish `htm' : (t : ℝ) ≤ m` using `by exact_mod_cast htm`. Establish `ht0 : (0 : ℝ) ≤ t` using `Nat.cast_nonneg _`.

Establish `e : θ * ((B : ℝ) + t) = ((B : ℝ) + t) - ((J : ℝ) + 1) * ((B : ℝ) + t) / ((B : ℝ) + m)`. Rewrite using `[hθ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hJ0 : (0 : ℝ) ≤ (J : ℝ) + 1` using `by positivity`. Establish `: ((J : ℝ) + 1) * ((B : ℝ) + t) / ((B : ℝ) + m) ≤ (J : ℝ) + 1`.

Rewrite using `[div_le_iff₀ hBm]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hθexp : θ ^ m ≤ Real.exp (-La / 3)`.

Establish `h1 : θ ≤ Real.exp (-(((J : ℝ) + 1) / ((B : ℝ) + m)))`. Use `Real.add_one_le_exp (-(((J : ℝ) + 1) / ((B : ℝ) + m)))` as an intermediate fact. Rewrite using `[hθ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : θ ^ m ≤ Real.exp (-(((J : ℝ) + 1) / ((B : ℝ) + m))) ^ m` using `pow_le_pow_left₀ hθ0 h1 m`.

Rewrite `h2` using `[← Real.exp_nat_mul]`. Use `h2.trans (Real.exp_le_exp.mpr ?_)` and prove the remaining obligations. Establish `hLa' : La * (B : ℝ) < ((J : ℝ) + 1) * ((m : ℝ) + 1)` using `(div_lt_iff₀ hm1).mp hJlt`. Establish `hq : ((m : ℝ) + 1) * ((B : ℝ) + m) ≤ 3 * m * B`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hBr) (by linarith : (0 : ℝ) ≤ 2 * m - 1), mul_nonneg (by linarith : (0 : ℝ) ≤ m + 1) (by linarith : (0 : ℝ) ≤ m - 1)]`.

Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `key : La * ((B : ℝ) + m) * ((m : ℝ) + 1) ≤ 3 * m * ((J : ℝ) + 1) * ((m : ℝ) + 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `key2 : La * ((B : ℝ) + m) ≤ 3 * m * ((J : ℝ) + 1)` using `le_of_mul_le_mul_right key hm1`. Establish `e : (m : ℝ) * -(((J : ℝ) + 1) / ((B : ℝ) + m)) = -((m * ((J : ℝ) + 1)) / ((B : ℝ) + m))` using `by ring`.

Rewrite using `[e]`. Establish `: La / 3 ≤ (m * ((J : ℝ) + 1)) / ((B : ℝ) + m)`. Rewrite using `[le_div_iff₀ hBm]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsd0 : (0 : ℝ) ≤ (sd m B : ℝ)` using `Nat.cast_nonneg _`. Establish `hc` using `congrArg (Nat.cast (R := ℝ)) hhock`. Move the coercions through the operations in `at hc ⊢`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hθexp hsd0, hratio, hc]`.
-/
theorem cl_hockey_low (m B : ℕ) (La : ℝ) (hm : 4 ≤ m) (hB : m + 1 ≤ B) (hLa0 : 0 ≤ La) (hLa : 4 * La ≤ (m : ℝ) + 1) :
    (1 - Real.exp (-La / 3)) * (sd m B : ℝ) ≤
      ((∑ jp ∈ range (⌊La * (B : ℝ) / ((m : ℝ) + 1)⌋₊ + 1), sdXi m (B - jp) : ℕ) : ℝ) := by
  set J := ⌊La * (B : ℝ) / ((m : ℝ) + 1)⌋₊ with hJ
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hBr : (m : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast hB
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ La * (B : ℝ) / ((m : ℝ) + 1) := div_nonneg (mul_nonneg hLa0 hB0) hm1.le
  have hxB : La * (B : ℝ) / ((m : ℝ) + 1) ≤ (B : ℝ) / 4 := by
    rw [div_le_iff₀ hm1]
    nlinarith
  have hJle : (J : ℝ) ≤ La * (B : ℝ) / ((m : ℝ) + 1) := Nat.floor_le hx0
  have hJlt : La * (B : ℝ) / ((m : ℝ) + 1) < (J : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJB : J + 1 ≤ B := by
    have : (J : ℝ) + 1 ≤ B := by linarith
    exact_mod_cast this
  have hhock := cl_hockey m B (J + 1) (by omega) hJB
  have hBm : (0 : ℝ) < (B : ℝ) + m := by positivity
  have hcastBL : ((B - (J + 1) : ℕ) : ℝ) = (B : ℝ) - ((J : ℝ) + 1) := by
    rw [Nat.cast_sub hJB]; push_cast; ring
  set θ : ℝ := 1 - ((J : ℝ) + 1) / ((B : ℝ) + m) with hθ
  have hLB : (J : ℝ) + 1 ≤ (B : ℝ) + m := by
    have : ((J + 1 : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hJB
    push_cast at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_iff₀ hBm]; linarith
  have hratio : (sd m (B - (J + 1)) : ℝ) ≤ θ ^ m * (sd m B : ℝ) := by
    apply cl_sd_ratio_le _ _ θ hθ0 m
    intro t _ htm
    rw [hcastBL]
    have htm' : (t : ℝ) ≤ m := by exact_mod_cast htm
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have e : θ * ((B : ℝ) + t) = ((B : ℝ) + t) - ((J : ℝ) + 1) * ((B : ℝ) + t) / ((B : ℝ) + m) := by
      rw [hθ]; ring
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
    have : ((J : ℝ) + 1) * ((B : ℝ) + t) / ((B : ℝ) + m) ≤ (J : ℝ) + 1 := by
      rw [div_le_iff₀ hBm]; nlinarith
    rw [e]; linarith
  have hθexp : θ ^ m ≤ Real.exp (-La / 3) := by
    have h1 : θ ≤ Real.exp (-(((J : ℝ) + 1) / ((B : ℝ) + m))) := by
      have := Real.add_one_le_exp (-(((J : ℝ) + 1) / ((B : ℝ) + m)))
      rw [hθ]; linarith
    have h2 : θ ^ m ≤ Real.exp (-(((J : ℝ) + 1) / ((B : ℝ) + m))) ^ m := pow_le_pow_left₀ hθ0 h1 m
    rw [← Real.exp_nat_mul] at h2
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    have hLa' : La * (B : ℝ) < ((J : ℝ) + 1) * ((m : ℝ) + 1) := (div_lt_iff₀ hm1).mp hJlt
    have hq : ((m : ℝ) + 1) * ((B : ℝ) + m) ≤ 3 * m * B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hBr) (by linarith : (0 : ℝ) ≤ 2 * m - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ m + 1) (by linarith : (0 : ℝ) ≤ m - 1)]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have key : La * ((B : ℝ) + m) * ((m : ℝ) + 1) ≤ 3 * m * ((J : ℝ) + 1) * ((m : ℝ) + 1) := by
      calc La * ((B : ℝ) + m) * ((m : ℝ) + 1) = La * (((m : ℝ) + 1) * ((B : ℝ) + m)) := by ring
        _ ≤ La * (3 * m * B) := mul_le_mul_of_nonneg_left hq hLa0
        _ = 3 * m * (La * B) := by ring
        _ ≤ 3 * m * (((J : ℝ) + 1) * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hLa'.le (by positivity)
        _ = 3 * m * ((J : ℝ) + 1) * ((m : ℝ) + 1) := by ring
    have key2 : La * ((B : ℝ) + m) ≤ 3 * m * ((J : ℝ) + 1) := le_of_mul_le_mul_right key hm1
    have e : (m : ℝ) * -(((J : ℝ) + 1) / ((B : ℝ) + m)) = -((m * ((J : ℝ) + 1)) / ((B : ℝ) + m)) := by ring
    rw [e]
    have : La / 3 ≤ (m * ((J : ℝ) + 1)) / ((B : ℝ) + m) := by
      rw [le_div_iff₀ hBm]; linarith
    linarith
  have hsd0 : (0 : ℝ) ≤ (sd m B : ℝ) := Nat.cast_nonneg _
  have hc := congrArg (Nat.cast (R := ℝ)) hhock
  push_cast at hc ⊢
  nlinarith [mul_le_mul_of_nonneg_right hθexp hsd0, hratio, hc]

/- English proof (translation)
Establish `hA' : (0 : ℝ) < A0` using `by exact_mod_cast hA`. Establish `hq1 : (M : ℝ) / (A0 : ℝ) ≤ 1`. Rewrite using `[div_le_iff₀ hA']; simpa using (show (M : ℝ) ≤ A0 by exact_mod_cast hM)`. Establish `hq0 : (0 : ℝ) ≤ 1 - (M : ℝ) / (A0 : ℝ)` using `by linarith`. Establish `hcast : ((A0 - M : ℕ) : ℝ) = (A0 : ℝ) - M` using `by rw [Nat.cast_sub hM]`.

Establish `hqA : (M : ℝ) / A0 * A0 = M` using `div_mul_cancel₀ _ hA'.ne'`. Proceed by induction on `m with`. Consider the case `zero => simp [sd]`. Consider the case `succ n ih`. Establish `hs` using `cl_sd_step A0 n`.

Establish `hs'` using `cl_sd_step (A0 - M) n`. Establish `hn : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Use `le_of_mul_le_mul_right ?_ hn` and prove the remaining obligations. Establish `key : (1 - (M : ℝ) / A0) * ((A0 : ℝ) + ((n : ℝ) + 1)) ≤ ((A0 - M : ℕ) : ℝ) + ((n : ℝ) + 1)`. Rewrite using `[hcast]`.

Establish `e : (1 - (M : ℝ) / A0) * ((A0 : ℝ) + ((n : ℝ) + 1)) = (A0 : ℝ) + ((n : ℝ) + 1) - (M : ℝ) / A0 * A0 - (M : ℝ) / A0 * ((n : ℝ) + 1)` using `by ring`. Establish `h0 : 0 ≤ (M : ℝ) / A0 * ((n : ℝ) + 1)` using `by positivity`. Rewrite using `[e, hqA]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, ← hs]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (((A0 - M : ℕ) : ℝ) + ((n : ℝ) + 1)) * (sd n (A0 - M) : ℝ) := mul_le_mul key ih (mul_nonneg (pow_nonneg hq0 _) (Nat.cast_nonneg _)) (by positivity)`. Use `_ = (sd (n + 1) (A0 - M) : ℝ) * ((n : ℝ) + 1) := hs'`.
-/
private theorem one_sub_div_pow_mul_sd_le_sd_sub (A0 M : ℕ) (hA : 0 < A0) (hM : M ≤ A0) (m : ℕ) :
    (1 - (M : ℝ) / (A0 : ℝ)) ^ m * (sd m A0 : ℝ) ≤ (sd m (A0 - M) : ℝ) := by
  have hA' : (0 : ℝ) < A0 := by exact_mod_cast hA
  have hq1 : (M : ℝ) / (A0 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hA']; simpa using (show (M : ℝ) ≤ A0 by exact_mod_cast hM)
  have hq0 : (0 : ℝ) ≤ 1 - (M : ℝ) / (A0 : ℝ) := by linarith
  have hcast : ((A0 - M : ℕ) : ℝ) = (A0 : ℝ) - M := by rw [Nat.cast_sub hM]
  have hqA : (M : ℝ) / A0 * A0 = M := div_mul_cancel₀ _ hA'.ne'
  induction m with
  | zero => simp [sd]
  | succ n ih =>
    have hs := cl_sd_step A0 n
    have hs' := cl_sd_step (A0 - M) n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine le_of_mul_le_mul_right ?_ hn
    have key : (1 - (M : ℝ) / A0) * ((A0 : ℝ) + ((n : ℝ) + 1)) ≤ ((A0 - M : ℕ) : ℝ) + ((n : ℝ) + 1) := by
      rw [hcast]
      have e : (1 - (M : ℝ) / A0) * ((A0 : ℝ) + ((n : ℝ) + 1)) =
          (A0 : ℝ) + ((n : ℝ) + 1) - (M : ℝ) / A0 * A0 - (M : ℝ) / A0 * ((n : ℝ) + 1) := by ring
      have h0 : 0 ≤ (M : ℝ) / A0 * ((n : ℝ) + 1) := by positivity
      rw [e, hqA]; linarith
    calc (1 - (M : ℝ) / A0) ^ (n + 1) * (sd (n + 1) A0 : ℝ) * ((n : ℝ) + 1)
        = ((1 - (M : ℝ) / A0) * ((A0 : ℝ) + ((n : ℝ) + 1))) * ((1 - (M : ℝ) / A0) ^ n * (sd n A0 : ℝ)) := by
          rw [mul_assoc, ← hs]; ring
      _ ≤ (((A0 - M : ℕ) : ℝ) + ((n : ℝ) + 1)) * (sd n (A0 - M) : ℝ) :=
          mul_le_mul key ih (mul_nonneg (pow_nonneg hq0 _) (Nat.cast_nonneg _)) (by positivity)
      _ = (sd (n + 1) (A0 - M) : ℝ) * ((n : ℝ) + 1) := hs'

/- English proof (translation)
Establish `hA' : (0 : ℝ) < A0` using `by exact_mod_cast hA`. Establish `h1` using `one_sub_div_pow_mul_sd_le_sd_sub A0 M hA hM m`. Establish `hb : 1 - (m : ℝ) * ((M : ℝ) / A0) ≤ (1 - (M : ℝ) / A0) ^ m`. Establish `hq1 : (M : ℝ) / (A0 : ℝ) ≤ 1`. Rewrite using `[div_le_iff₀ hA']; simpa using (show (M : ℝ) ≤ A0 by exact_mod_cast hM)`.

Establish `h2 : (-2 : ℝ) ≤ -((M : ℝ) / A0)` using `by linarith`. Establish `h3` using `one_add_mul_le_pow h2 m`. Establish `e1 : (1 : ℝ) + (m : ℝ) * -((M : ℝ) / A0) = 1 - (m : ℝ) * ((M : ℝ) / A0)` using `by ring`. Establish `e2 : (1 : ℝ) + -((M : ℝ) / A0) = 1 - (M : ℝ) / A0` using `by ring`. Rewrite `h3` using `[e1, e2]`.

Conclude with `h3`. Establish `hs0 : (0 : ℝ) ≤ (sd m A0 : ℝ)` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (1 - (M : ℝ) / A0) ^ m * (sd m A0 : ℝ) := mul_le_mul_of_nonneg_right hb hs0`.

Use `_ ≤ _ := h1`.
-/
theorem cl_sd_margin (m A0 M : ℕ) (hA : 0 < A0) (hM : M ≤ A0) :
    (1 - (m : ℝ) * (M : ℝ) / (A0 : ℝ)) * (sd m A0 : ℝ) ≤ (sd m (A0 - M) : ℝ) := by
  have hA' : (0 : ℝ) < A0 := by exact_mod_cast hA
  have h1 := one_sub_div_pow_mul_sd_le_sd_sub A0 M hA hM m
  have hb : 1 - (m : ℝ) * ((M : ℝ) / A0) ≤ (1 - (M : ℝ) / A0) ^ m := by
    have hq1 : (M : ℝ) / (A0 : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hA']; simpa using (show (M : ℝ) ≤ A0 by exact_mod_cast hM)
    have h2 : (-2 : ℝ) ≤ -((M : ℝ) / A0) := by linarith
    have h3 := one_add_mul_le_pow h2 m
    have e1 : (1 : ℝ) + (m : ℝ) * -((M : ℝ) / A0) = 1 - (m : ℝ) * ((M : ℝ) / A0) := by ring
    have e2 : (1 : ℝ) + -((M : ℝ) / A0) = 1 - (M : ℝ) / A0 := by ring
    rw [e1, e2] at h3; exact h3
  have hs0 : (0 : ℝ) ≤ (sd m A0 : ℝ) := Nat.cast_nonneg _
  calc (1 - (m : ℝ) * (M : ℝ) / (A0 : ℝ)) * (sd m A0 : ℝ) = (1 - (m : ℝ) * ((M : ℝ) / A0)) * (sd m A0 : ℝ) := by
        ring
    _ ≤ (1 - (M : ℝ) / A0) ^ m * (sd m A0 : ℝ) := mul_le_mul_of_nonneg_right hb hs0
    _ ≤ _ := h1

/- English proof (translation)
Introduce `X _ hD hH hc j m hm hmA rz ry hd`. Establish `hs` using `hstd X hD hH hc`. Establish `hkdef : X.k = (X.m : ℝ) + 1` using `rfl`. Establish `hk5` using `hs.k5`. Establish `hk0 : 0 < X.k` using `by linarith`.

Establish `hLa1` using `hs.La1`. Establish `hLa0 : 0 ≤ X.La C0` using `by linarith`. Establish `hm4 : 4 ≤ X.m`. Establish `: (4 : ℝ) ≤ (X.m : ℝ)` using `by rw [hkdef] at hk5; linarith`. Conclude with `this` after adjusting the coercions.

Choose the witnesses or unpack the hypotheses as in `⟨A0n, hA0n⟩ : ∃ n : ℕ, (X.seg C0 CE1 CE2 j).A0 X.p = (n : ℤ) := by`. Establish `h1` using `hs.half_ratio_le_segment_base_of_std j`. Establish `h2 : (0 : ℝ) < (X.a : ℝ) / (2 * X.Q)` using `div_pos hs.apos (by have := hs.Q1; linarith)`. Establish `h3 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)` using `lt_of_lt_of_le h2 h1`. Establish `h4 : 0 < (X.seg C0 CE1 CE2 j).A0 X.p` using `by exact_mod_cast h3`.

Conclude with `⟨((X.seg C0 CE1 CE2 j).A0 X.p).toNat, (Int.toNat_of_nonneg h4.le).symm⟩`. Establish `hA0r : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) = (A0n : ℝ)` using `by rw [hA0n]; simp`. Establish `hA0pos : (0 : ℝ) < (A0n : ℝ)`. Establish `h1` using `hs.half_ratio_le_segment_base_of_std j`. Establish `h2 : (0 : ℝ) < (X.a : ℝ) / (2 * X.Q)` using `div_pos hs.apos (by have := hs.Q1; linarith)`.

Rewrite `h1` using `[hA0r]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA0pos' : 0 < A0n` using `by exact_mod_cast hA0pos`. Establish `heps : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1`. Establish `h1` using `hs.LaK`.

Establish `h2` using `hs.de6`. Establish `h3 : 0 ≤ (X.N1 : ℝ) * X.La C0 / X.k` using `by positivity`. Establish `e : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k)` using `by ring`. Rewrite `h1` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmA' : (⌈m⌉₊ : ℝ) ≤ (A0n : ℝ) * ((X.N1 : ℝ) * X.La C0 / X.k)`. Rewrite `hmA` using `[hA0r]`. Combine the equalities or inequalities in the displayed calculation. Establish `hMle : ⌈m⌉₊ ≤ A0n`. Establish `: (⌈m⌉₊ : ℝ) ≤ (A0n : ℝ)` using `hmA'.trans (by nlinarith)`.

Conclude with `this` after adjusting the coercions. Establish `hAn : ((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat = A0n - ⌈m⌉₊`. Rewrite using `[hA0n]`. Use linear arithmetic over natural numbers and integers. Establish `hAnr : ((A0n - ⌈m⌉₊ : ℕ) : ℝ) = (A0n : ℝ) - (⌈m⌉₊ : ℝ)` using `Nat.cast_sub hMle`.

Establish `hBdef : (X.seg C0 CE1 CE2 j).bPlus = X.bT (segNext X.TT j)` using `rfl`. Establish `hB : X.m + 1 ≤ (X.seg C0 CE1 CE2 j).bPlus`. Establish `h1` using `(hs.winB _ (next_mem X.TT j).1).1`. Establish `h2` using `hs.beLe`. Establish `h3` using `hs.de6`.

Establish `h4 : 0 ≤ 18 * (X.N1 : ℝ) * X.La C0 / X.k` using `by positivity`. Establish `h5` using `hs.kQ le_rfl`. Establish `h6` using `hs.Q1`. Establish `h7 : X.k ^ 3 ≤ X.b'`. Establish `: X.k ^ 3 * 1 ≤ X.k ^ 3 * X.Q` using `mul_le_mul_of_nonneg_left h6 (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h8 : 2 * X.k ≤ X.k ^ 3`. Establish `hkk : 25 ≤ X.k * X.k` using `by nlinarith`. Establish `e3 : X.k ^ 3 = X.k * (X.k * X.k)` using `by ring`. Rewrite using `[e3]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h9 : X.b' * (1 / 2) ≤ X.b' * (1 - be X C0)` using `mul_le_mul_of_nonneg_left (by linarith) hs.bpos.le`. Establish `: (X.m : ℝ) + 1 ≤ (X.bT (segNext X.TT j) : ℝ)` using `by rw [← hkdef]; linarith`. Rewrite using `[hBdef]`. Conclude with `this` after adjusting the coercions.

Establish `h4La : 4 * X.La C0 ≤ (X.m : ℝ) + 1`. Establish `h1` using `hs.LaN`. Establish `h2` using `hs.N2`. Rewrite using `[← hkdef]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `t2` using `cl_hockey_low X.m (X.seg C0 CE1 CE2 j).bPlus (X.La C0) hm4 hB hLa0 h4La`. Establish `t3` using `cl_sd_margin X.m A0n ⌈m⌉₊ hA0pos' hMle`. Establish `t1` using `hT X hD hH hc j rz ry hd (A0n - ⌈m⌉₊) (by rw [hA0r, hAnr]; nlinarith) (by rw [hA0r, hAnr]; have : (0 : ℝ) ≤ (⌈m⌉₊ : ℝ) := Nat.cast_nonneg _; linarith)`. Establish `t0` using `hM X hD hH hc j m hm hmA rz ry hd`. Rewrite `t0` using `[hAn]`.

Establish `t0' : ((keptPairSum X.p (X.La C0) (r` using `X.m) (A0n - ⌈m⌉₊) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℚ) : ℝ) * ((∑ jp ∈ range (⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / ((X.m : ℝ) + 1)⌋₊ + 1), sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℕ) : ℝ) ≤ ((chainCount C0 CE1 CE2 X j m rz ry : ℚ) : ℝ) := by`. Use `(Rat.cast_le (K := ℝ)).mpr t0` as an intermediate fact. Move the coercions through the operations in `at this`. Use `push_cast`. Conclude with `this`.

Use `set Pi : ℕ := ∏ i, symDim (X.m + 1) (clA C0 CE1 CE2 X j rz ry i) * symDim (X.m + 1) (clC C0 CE1 CE2 X j rz ry i) with hPi`. Establish `eMM : ∀ z : ℤ, dimMM (X.m + 1) z (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) = symDim (X.m + 1) z * Pi` using `fun _ => rfl`. Establish `eB : mmB C0 CE1 CE2 X j rz ry = sd X.m A0n * Pi * sd X.m (X.seg C0 CE1 CE2 j).bPlus`. Establish `e1 : mmB C0 CE1 CE2 X j rz ry = dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) * symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ)` using `rfl`. Rewrite using `[e1, eMM, hA0n, symDim_toNat _ _ (Int.natCast_nonneg _), symDim_toNat _ _ (Int.natCast_nonneg _), Int.toNat_natCast, Int.toNat_natCast]`.

Rewrite `t1` using `[eMM, symDim_toNat _ _ (Int.natCast_nonneg _), Int.toNat_natCast]`. Move the coercions through the operations in `at t1`. Rewrite using `[eB]`. Unfold `lowFac`. Rewrite using `[hA0r]`.

Use `push_cast`. Use `set a1 : ℝ := 1 - Real.exp (-(X.La C0) / 8) with ha1`. Use `set a2 : ℝ := 1 - Real.exp (-(X.La C0) / 3) with ha2`. Establish `ha1' : 0 ≤ a1`. Establish `: Real.exp (-(X.La C0) / 8) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith)`.

Rewrite using `[ha1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha2' : 0 ≤ a2`. Establish `: Real.exp (-(X.La C0) / 3) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith)`. Rewrite using `[ha2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set KS : ℝ := ((keptPairSum X.p (X.La C0) (r := X.m) (A0n - ⌈m⌉₊) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℚ) : ℝ) with hKS`. Use `set Hr : ℝ := ((∑ jp ∈ range (⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / ((X.m : ℝ) + 1)⌋₊ + 1), sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℕ) : ℝ) with hHr`. Establish `hP0 : (0 : ℝ) ≤ (Pi : ℝ)` using `Nat.cast_nonneg _`. Establish `hy0 : (0 : ℝ) ≤ (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ)` using `Nat.cast_nonneg _`.

Establish `hx1 : (0 : ℝ) ≤ (sd X.m (A0n - ⌈m⌉₊) : ℝ)` using `Nat.cast_nonneg _`. Establish `hKS0 : 0 ≤ KS` using `le_trans (by positivity) t1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem countLow_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hT : TailAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : MatchAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    CountLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hH hc j m hm hmA rz ry hd
  have hs := hstd X hD hH hc
  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  have hk5 := hs.k5
  have hk0 : 0 < X.k := by linarith
  have hLa1 := hs.La1
  have hLa0 : 0 ≤ X.La C0 := by linarith
  have hm4 : 4 ≤ X.m := by
    have : (4 : ℝ) ≤ (X.m : ℝ) := by rw [hkdef] at hk5; linarith
    exact_mod_cast this

  obtain ⟨A0n, hA0n⟩ : ∃ n : ℕ, (X.seg C0 CE1 CE2 j).A0 X.p = (n : ℤ) := by
    have h1 := hs.half_ratio_le_segment_base_of_std j
    have h2 : (0 : ℝ) < (X.a : ℝ) / (2 * X.Q) := div_pos hs.apos (by have := hs.Q1; linarith)
    have h3 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := lt_of_lt_of_le h2 h1
    have h4 : 0 < (X.seg C0 CE1 CE2 j).A0 X.p := by exact_mod_cast h3
    exact ⟨((X.seg C0 CE1 CE2 j).A0 X.p).toNat, (Int.toNat_of_nonneg h4.le).symm⟩
  have hA0r : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) = (A0n : ℝ) := by rw [hA0n]; simp
  have hA0pos : (0 : ℝ) < (A0n : ℝ) := by
    have h1 := hs.half_ratio_le_segment_base_of_std j
    have h2 : (0 : ℝ) < (X.a : ℝ) / (2 * X.Q) := div_pos hs.apos (by have := hs.Q1; linarith)
    rw [hA0r] at h1
    linarith
  have hA0pos' : 0 < A0n := by exact_mod_cast hA0pos

  have heps : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1 := by
    have h1 := hs.LaK
    have h2 := hs.de6
    have h3 : 0 ≤ (X.N1 : ℝ) * X.La C0 / X.k := by positivity
    have e : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
    rw [e] at h1
    linarith
  have hmA' : (⌈m⌉₊ : ℝ) ≤ (A0n : ℝ) * ((X.N1 : ℝ) * X.La C0 / X.k) := by
    rw [hA0r] at hmA
    calc (⌈m⌉₊ : ℝ) ≤ (A0n : ℝ) * X.N1 * X.La C0 / X.k := hmA
      _ = (A0n : ℝ) * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
  have hMle : ⌈m⌉₊ ≤ A0n := by
    have : (⌈m⌉₊ : ℝ) ≤ (A0n : ℝ) := hmA'.trans (by nlinarith)
    exact_mod_cast this
  have hAn : ((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat = A0n - ⌈m⌉₊ := by
    rw [hA0n]; omega
  have hAnr : ((A0n - ⌈m⌉₊ : ℕ) : ℝ) = (A0n : ℝ) - (⌈m⌉₊ : ℝ) := Nat.cast_sub hMle

  have hBdef : (X.seg C0 CE1 CE2 j).bPlus = X.bT (segNext X.TT j) := rfl
  have hB : X.m + 1 ≤ (X.seg C0 CE1 CE2 j).bPlus := by
    have h1 := (hs.winB _ (next_mem X.TT j).1).1
    have h2 := hs.beLe
    have h3 := hs.de6
    have h4 : 0 ≤ 18 * (X.N1 : ℝ) * X.La C0 / X.k := by positivity
    have h5 := hs.kQ le_rfl
    have h6 := hs.Q1
    have h7 : X.k ^ 3 ≤ X.b' := by
      have : X.k ^ 3 * 1 ≤ X.k ^ 3 * X.Q := mul_le_mul_of_nonneg_left h6 (by positivity)
      linarith
    have h8 : 2 * X.k ≤ X.k ^ 3 := by
      have hkk : 25 ≤ X.k * X.k := by nlinarith
      have e3 : X.k ^ 3 = X.k * (X.k * X.k) := by ring
      rw [e3]
      nlinarith
    have h9 : X.b' * (1 / 2) ≤ X.b' * (1 - be X C0) := mul_le_mul_of_nonneg_left (by linarith) hs.bpos.le
    have : (X.m : ℝ) + 1 ≤ (X.bT (segNext X.TT j) : ℝ) := by rw [← hkdef]; linarith
    rw [hBdef]
    exact_mod_cast this
  have h4La : 4 * X.La C0 ≤ (X.m : ℝ) + 1 := by
    have h1 := hs.LaN
    have h2 := hs.N2
    rw [← hkdef]
    nlinarith

  have t2 := cl_hockey_low X.m (X.seg C0 CE1 CE2 j).bPlus (X.La C0) hm4 hB hLa0 h4La
  have t3 := cl_sd_margin X.m A0n ⌈m⌉₊ hA0pos' hMle
  have t1 := hT X hD hH hc j rz ry hd (A0n - ⌈m⌉₊)
    (by rw [hA0r, hAnr]; nlinarith) (by rw [hA0r, hAnr]; have : (0 : ℝ) ≤ (⌈m⌉₊ : ℝ) := Nat.cast_nonneg _; linarith)
  have t0 := hM X hD hH hc j m hm hmA rz ry hd
  rw [hAn] at t0
  have t0' : ((keptPairSum X.p (X.La C0) (r := X.m) (A0n - ⌈m⌉₊) (clA C0 CE1 CE2 X j rz ry)
      (clC C0 CE1 CE2 X j rz ry) : ℚ) : ℝ) *
      ((∑ jp ∈ range (⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / ((X.m : ℝ) + 1)⌋₊ + 1),
        sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℕ) : ℝ) ≤ ((chainCount C0 CE1 CE2 X j m rz ry : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr t0
    push_cast at this
    push_cast
    exact this

  set Pi : ℕ := ∏ i, symDim (X.m + 1) (clA C0 CE1 CE2 X j rz ry i) * symDim (X.m + 1) (clC C0 CE1 CE2 X j rz ry i) with hPi
  have eMM : ∀ z : ℤ, dimMM (X.m + 1) z (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) = symDim (X.m + 1) z * Pi :=
    fun _ => rfl
  have eB : mmB C0 CE1 CE2 X j rz ry = sd X.m A0n * Pi * sd X.m (X.seg C0 CE1 CE2 j).bPlus := by
    have e1 : mmB C0 CE1 CE2 X j rz ry =
        dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) *
          symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ) := rfl
    rw [e1, eMM, hA0n, symDim_toNat _ _ (Int.natCast_nonneg _), symDim_toNat _ _ (Int.natCast_nonneg _),
      Int.toNat_natCast, Int.toNat_natCast]
  rw [eMM, symDim_toNat _ _ (Int.natCast_nonneg _), Int.toNat_natCast] at t1
  push_cast at t1
  rw [eB]
  unfold lowFac
  rw [hA0r]
  push_cast
  set a1 : ℝ := 1 - Real.exp (-(X.La C0) / 8) with ha1
  set a2 : ℝ := 1 - Real.exp (-(X.La C0) / 3) with ha2
  have ha1' : 0 ≤ a1 := by
    have : Real.exp (-(X.La C0) / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [ha1]; linarith
  have ha2' : 0 ≤ a2 := by
    have : Real.exp (-(X.La C0) / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [ha2]; linarith
  set KS : ℝ := ((keptPairSum X.p (X.La C0) (r := X.m) (A0n - ⌈m⌉₊) (clA C0 CE1 CE2 X j rz ry)
      (clC C0 CE1 CE2 X j rz ry) : ℚ) : ℝ) with hKS
  set Hr : ℝ := ((∑ jp ∈ range (⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / ((X.m : ℝ) + 1)⌋₊ + 1),
        sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℕ) : ℝ) with hHr
  have hP0 : (0 : ℝ) ≤ (Pi : ℝ) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ) := Nat.cast_nonneg _
  have hx1 : (0 : ℝ) ≤ (sd X.m (A0n - ⌈m⌉₊) : ℝ) := Nat.cast_nonneg _
  have hKS0 : 0 ≤ KS := le_trans (by positivity) t1
  calc a1 * a2 * (1 - (X.m : ℝ) * (⌈m⌉₊ : ℝ) / (A0n : ℝ)) *
        ((sd X.m A0n : ℝ) * (Pi : ℝ) * (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ))
      = (a1 * (Pi : ℝ) * (a2 * (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ))) *
          ((1 - (X.m : ℝ) * (⌈m⌉₊ : ℝ) / (A0n : ℝ)) * (sd X.m A0n : ℝ)) := by ring
    _ ≤ (a1 * (Pi : ℝ) * (a2 * (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ))) * (sd X.m (A0n - ⌈m⌉₊) : ℝ) :=
        mul_le_mul_of_nonneg_left t3 (by positivity)
    _ = (a1 * ((sd X.m (A0n - ⌈m⌉₊) : ℝ) * (Pi : ℝ))) * (a2 * (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ)) := by ring
    _ ≤ KS * (a2 * (sd X.m (X.seg C0 CE1 CE2 j).bPlus : ℝ)) := mul_le_mul_of_nonneg_right t1 (by positivity)
    _ ≤ KS * Hr := mul_le_mul_of_nonneg_left t2 hKS0
    _ ≤ _ := t0'

/- English proof (translation)
Unfold `TransportedAlt at hP hQ ⊢`. Introduce `Cc hCc`. Take `⟨T0, hT0, hP1⟩` from `hP Cc hCc`. Take `⟨U0, _, hQ1⟩` from `hQ Cc hCc`. Use `⟨max T0 U0, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩` and prove the remaining obligations.

Take `⟨T1, hT1, hP2⟩` from `hP1 C0 (le_trans (le_max_left _ _) hC0)`. Take `⟨U1, _, hQ2⟩` from `hQ1 C0 (le_trans (le_max_right _ _) hC0)`. Use `⟨max T1 U1, lt_max_of_lt_left hT1, fun CE1 CE2 Cm e1 e2 e3 => ?_⟩` and prove the remaining obligations. Take `⟨T2, hT2, hP3⟩` from `hP2 CE1 CE2 Cm (le_trans (le_max_left _ _) e1) (le_trans (le_max_left _ _) e2) (le_trans (le_max_left _ _) e3)`. Take `⟨U2, _, hQ3⟩` from `hQ2 CE1 CE2 Cm (le_trans (le_max_right _ _) e1) (le_trans (le_max_right _ _) e2) (le_trans (le_max_right _ _) e3)`.

Use `⟨max T2 U2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb f1 f2 f3 f4 f5 => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `hP3 CYb Cde Ck CD Cb (le_trans (le_max_left _ _) f1) (le_trans (le_max_left _ _) f2) (le_trans (le_max_left _ _) f3) (le_trans (le_max_left _ _) f4) (le_trans (le_max_left _ _) f5)`. Conclude with `hQ3 CYb Cde Ck CD Cb (le_trans (le_max_right _ _) f1) (le_trans (le_max_right _ _) f2) (le_trans (le_max_right _ _) f3) (le_trans (le_max_right _ _) f4) (le_trans (le_max_right _ _) f5)`.
-/
private theorem transported_and {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hP : TransportedAlt P) (hQ : TransportedAlt Q) :
    TransportedAlt fun a b c d e f g i j l => P a b c d e f g i j l ∧ Q a b c d e f g i j l := by
  unfold TransportedAlt at hP hQ ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, hP1⟩ := hP Cc hCc
  obtain ⟨U0, _, hQ1⟩ := hQ Cc hCc
  refine ⟨max T0 U0, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, hP2⟩ := hP1 C0 (le_trans (le_max_left _ _) hC0)
  obtain ⟨U1, _, hQ2⟩ := hQ1 C0 (le_trans (le_max_right _ _) hC0)
  refine ⟨max T1 U1, lt_max_of_lt_left hT1, fun CE1 CE2 Cm e1 e2 e3 => ?_⟩
  obtain ⟨T2, hT2, hP3⟩ := hP2 CE1 CE2 Cm (le_trans (le_max_left _ _) e1)
    (le_trans (le_max_left _ _) e2) (le_trans (le_max_left _ _) e3)
  obtain ⟨U2, _, hQ3⟩ := hQ2 CE1 CE2 Cm (le_trans (le_max_right _ _) e1)
    (le_trans (le_max_right _ _) e2) (le_trans (le_max_right _ _) e3)
  refine ⟨max T2 U2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb f1 f2 f3 f4 f5 => ⟨?_, ?_⟩⟩
  · exact hP3 CYb Cde Ck CD Cb (le_trans (le_max_left _ _) f1) (le_trans (le_max_left _ _) f2)
      (le_trans (le_max_left _ _) f3) (le_trans (le_max_left _ _) f4) (le_trans (le_max_left _ _) f5)
  · exact hQ3 CYb Cde Ck CD Cb (le_trans (le_max_right _ _) f1) (le_trans (le_max_right _ _) f2)
      (le_trans (le_max_right _ _) f3) (le_trans (le_max_right _ _) f4) (le_trans (le_max_right _ _) f5)

/- English proof (translation)
Unfold `TransportedAlt at hP ⊢`. Introduce `Cc hCc`. Take `⟨T0, hT0, h1⟩` from `hP Cc hCc`. Use `⟨T0, hT0, fun C0 hC0 => ?_⟩` and prove the remaining obligations. Take `⟨T1, hT1, h2⟩` from `h1 C0 hC0`.

Use `⟨T1, hT1, fun CE1 CE2 Cm e1 e2 e3 => ?_⟩` and prove the remaining obligations. Take `⟨T2, hT2, h3⟩` from `h2 CE1 CE2 Cm e1 e2 e3`. Conclude with `⟨T2, hT2, fun CYb Cde Ck CD Cb f1 f2 f3 f4 f5 => h _ _ _ _ _ _ _ _ _ _ (h3 CYb Cde Ck CD Cb f1 f2 f3 f4 f5)⟩`.
-/
private theorem transported_of_imp {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ a b c d e f g i j l, P a b c d e f g i j l → Q a b c d e f g i j l) (hP : TransportedAlt P) : TransportedAlt Q := by
  unfold TransportedAlt at hP ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h1⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h2⟩ := h1 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm e1 e2 e3 => ?_⟩
  obtain ⟨T2, hT2, h3⟩ := h2 CE1 CE2 Cm e1 e2 e3
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb f1 f2 f3 f4 f5 => h _ _ _ _ _ _ _ _ _ _ (h3 CYb Cde Ck CD Cb f1 f2 f3 f4 f5)⟩

/- English proof (translation)
Unfold `RestCountLow`. Unfold `RestTail at hT`. Unfold `RestMatch at hM`. Use `transported_of_imp ?_ (transported_and (transported_and threshold_standard_one hT) hM)` and prove the remaining obligations. Introduce `_ _ _ _ _ _ _ _ _ _ h`.

Conclude with `countLow_of h.1.1 h.1.2 h.2`.
-/
theorem restCountLow_of (hT : RestTail) (hM : RestMatch) : RestCountLow := by
  unfold RestCountLow
  unfold RestTail at hT
  unfold RestMatch at hM
  refine transported_of_imp ?_ (transported_and (transported_and threshold_standard_one hT) hM)
  intro _ _ _ _ _ _ _ _ _ _ h
  exact countLow_of h.1.1 h.1.2 h.2

def TgtOK (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (t : Tgt (segS X.TT j) X.m) : Prop :=
  (IsPair ((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) t.1 t.2.1 ∧
    KeptPair X.p (X.La C0) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) t.1 t.2.1) ∧
    t.2.2 ≤ ⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k⌋₊

def MatchLowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∃ Ψ : Tgt (segS X.TT j) X.m → FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t,
        Set.InjOn Ψ {t | TgtOK C0 CE1 CE2 X j m rz ry t} ∧
        ∀ t, TgtOK C0 CE1 CE2 X j m rz ry t →
          SrcOK C0 CE1 CE2 X j m rz ry (Ψ t) ∧ (Ψ t).2.2 (Fin.last _) = t.2.1 ∧ (Ψ t).2.1.2 = t.2.2

def RestMatchLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => MatchLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

/- English proof (translation)
Distinguish the cases in `hS : (Function.support fun a => if P a then w a else 0).Finite`. Take `⟨S, hSe⟩ : ∃ S : Finset α, (S : Set α) = Function.support fun a => if P a then w a else 0` from `⟨hS.toFinset, hS.coe_toFinset⟩`. Take `⟨T, hTe⟩ : ∃ T : Finset τ, (T : Set τ) = Function.support G` from `⟨hGfin.toFinset, hGfin.coe_toFinset⟩`. Establish `hmemS : ∀ a, a ∈ S ↔ P a`. Introduce `a`.

Rewrite using `[← Finset.mem_coe, hSe, Function.mem_support]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hp`. Conclude with `h (if_neg hp)`.

Introduce `hp`. Rewrite using `[if_pos hp]`. Conclude with `(hw a hp).ne'`. Establish `mem : ∀ x : α × ℕ, x ∈ S ×ˢ range (J + 1) → P x.1 ∧ x.2 ≤ J`. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_product, Finset.mem_range]`. Conclude with `⟨(hmemS _).mp hx.1, by omega⟩`. Rewrite using `[finsum_eq_sum_of_support_subset _ hSe.symm.subset, finsum_eq_sum_of_support_subset _ hTe.symm.subset, Finset.sum_mul_sum]`. Establish `himg : ∑ t ∈ (S ×ˢ range (J + 1)).image Ψ, G t = ∑ a ∈ S, ∑ jj ∈ range (J + 1), (if P a then w a else 0) * c jj`. Rewrite using `[Finset.sum_image (by`.

Introduce `x hx y hy hxy`. Conclude with `hinj (mem x (by simpa using hx)) (mem y (by simpa using hy)) hxy),`. Use the proof step `Finset.sum_product]`. Use `Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun jj hj => ?_))` and prove the remaining obligations. Establish `hp` using `(hmemS a).mp ha`.

Establish `hjj : jj ≤ J` using `by have := Finset.mem_range.mp hj; omega`. Rewrite using `[if_pos hp, hval (a, jj) hp hjj]`. Rewrite using `[← himg]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `t ht`.

Rewrite `ht` using `[Finset.mem_image]`. Take `⟨x, hx, rfl⟩` from `ht`. Rewrite using `[← Finset.mem_coe, hTe, Function.mem_support]`. Take `⟨hp, hj⟩` from `mem x hx`. Rewrite using `[hval x hp hj]`.

Conclude with `(mul_pos (hw _ hp) (hc _)).ne'`. Introduce `t _ _`. Conclude with `hG0 t`. Rewrite using `[finsum_of_infinite_support hS, zero_mul]`. Conclude with `finsum_nonneg hG0`.
-/
theorem cl_prod_le {α τ : Type*} (P : α → Prop) [DecidablePred P] (w : α → ℚ) (hw : ∀ a, P a → 0 < w a) (J : ℕ) (c : ℕ → ℚ)
    (hc : ∀ n, 0 < c n) (G : τ → ℚ) (hG0 : ∀ t, 0 ≤ G t) (hGfin : (Function.support G).Finite) (Ψ : α × ℕ → τ)
    (hinj : Set.InjOn Ψ {t | P t.1 ∧ t.2 ≤ J}) (hval : ∀ t : α × ℕ, P t.1 → t.2 ≤ J → G (Ψ t) = w t.1 * c t.2) :
    (∑ᶠ a, if P a then w a else 0) * ∑ jp ∈ range (J + 1), c jp ≤ ∑ᶠ t, G t := by
  classical
  by_cases hS : (Function.support fun a => if P a then w a else 0).Finite
  · obtain ⟨S, hSe⟩ : ∃ S : Finset α, (S : Set α) = Function.support fun a => if P a then w a else 0 :=
      ⟨hS.toFinset, hS.coe_toFinset⟩
    obtain ⟨T, hTe⟩ : ∃ T : Finset τ, (T : Set τ) = Function.support G := ⟨hGfin.toFinset, hGfin.coe_toFinset⟩
    have hmemS : ∀ a, a ∈ S ↔ P a := by
      intro a
      rw [← Finset.mem_coe, hSe, Function.mem_support]
      constructor
      · intro h; by_contra hp; exact h (if_neg hp)
      · intro hp; rw [if_pos hp]; exact (hw a hp).ne'
    have mem : ∀ x : α × ℕ, x ∈ S ×ˢ range (J + 1) → P x.1 ∧ x.2 ≤ J := by
      intro x hx
      rw [Finset.mem_product, Finset.mem_range] at hx
      exact ⟨(hmemS _).mp hx.1, by omega⟩
    rw [finsum_eq_sum_of_support_subset _ hSe.symm.subset, finsum_eq_sum_of_support_subset _ hTe.symm.subset,
      Finset.sum_mul_sum]
    have himg : ∑ t ∈ (S ×ˢ range (J + 1)).image Ψ, G t =
        ∑ a ∈ S, ∑ jj ∈ range (J + 1), (if P a then w a else 0) * c jj := by
      rw [Finset.sum_image (by
          intro x hx y hy hxy
          exact hinj (mem x (by simpa using hx)) (mem y (by simpa using hy)) hxy),
        Finset.sum_product]
      refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun jj hj => ?_))
      have hp := (hmemS a).mp ha
      have hjj : jj ≤ J := by have := Finset.mem_range.mp hj; omega
      rw [if_pos hp, hval (a, jj) hp hjj]
    rw [← himg]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      rw [← Finset.mem_coe, hTe, Function.mem_support]
      obtain ⟨hp, hj⟩ := mem x hx
      rw [hval x hp hj]
      exact (mul_pos (hw _ hp) (hc _)).ne'
    · intro t _ _; exact hG0 t
  · rw [finsum_of_infinite_support hS, zero_mul]
    exact finsum_nonneg hG0

/- English proof (translation)
Introduce `⟨i, hi⟩ ⟨j, hj⟩ hij`. Simplify using `only [Fin.mk_le_mk] at hij`. Proceed by induction on `j with`. Consider the case `zero`. Establish `: i = 0` using `by omega`.

Substitute `this` using the available equality. Conclude with `le_rfl`. Consider the case `succ j ih`. Break down `Nat.lt_or_ge i (j + 1) with hlt | hge` into its components or cases. Conclude with `le_trans (h ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl) (ih (by omega) (by omega))`.

Establish `: i = j + 1` using `by omega`. Substitute `this` using the available equality. Conclude with `le_rfl`.
-/
private theorem antitone_of_succ_le' {r : ℕ} (f : Fin r → ℤ) (h : ∀ i j : Fin r, i.val + 1 = j.val → f j ≤ f i) :
    ∀ i j : Fin r, i ≤ j → f j ≤ f i := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Fin.mk_le_mk] at hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact le_trans (h ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl) (ih (by omega) (by omega))
    · have : i = j + 1 := by omega
      subst this; exact le_rfl

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `h`. Conclude with `⟨antitone_of_succ_le' nu (fun i j hij => le_trans (h2 i j hij) (h1 i)), antitone_of_succ_le' mu (fun i j hij => le_trans (h1 j) (h2 i j hij))⟩`.
-/
private theorem antitone_pair_of_strip {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) :
    (∀ i j : Fin r, i ≤ j → nu j ≤ nu i) ∧ (∀ i j : Fin r, i ≤ j → mu j ≤ mu i) := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨antitone_of_succ_le' nu (fun i j hij => le_trans (h2 i j hij) (h1 i)),
    antitone_of_succ_le' mu (fun i j hij => le_trans (h1 j) (h2 i j hij))⟩

/- English proof (translation)
Take `⟨h0, hs⟩` from `h`. Consider the cases of `N with`. Consider the case `zero`. Introduce `i j _`. Establish `e : Fin.last 0 = 0` using `by ext; simp`.

Rewrite using `[e, h0]`. Simplify using the standard rewrite rules. Consider the case `succ N`. Introduce `i j hij`. Use `hs (Fin.last N)` as an intermediate fact.

Rewrite `this` using `[Fin.succ_last]`. Use `split_ifs at this`. Conclude with `(antitone_pair_of_strip this).1 i j hij`. Conclude with `(antitone_pair_of_strip this).2 i j hij`.
-/
private theorem antitone_last_of_isChain {N r : ℕ} {LL : ChainLetters N} {ka : Fin (N + 1) → Fin r → ℤ}
    (h : IsChain LL ka) : ∀ i j : Fin r, i ≤ j → ka (Fin.last N) j ≤ ka (Fin.last N) i := by
  obtain ⟨h0, hs⟩ := h
  cases N with
  | zero =>
    intro i j _
    have e : Fin.last 0 = 0 := by ext; simp
    rw [e, h0]; simp
  | succ N =>
    intro i j hij
    have := hs (Fin.last N)
    rw [Fin.succ_last] at this
    split_ifs at this
    · exact (antitone_pair_of_strip this).1 i j hij
    · exact (antitone_pair_of_strip this).2 i j hij

/- English proof (translation)
Unfold `wdim`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j _`.

Use `split_ifs with hij`. Establish `hl : (lam j : ℚ) ≤ (lam i : ℚ)` using `by exact_mod_cast h i j hij.le`. Establish `hij' : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ)` using `by exact_mod_cast (show (i : ℕ) < (j : ℕ) from hij)`. Apply the tactic sequence `apply div_pos <;> linarith`. Conclude with `one_pos`.
-/
private theorem wdim_pos_of_antitone {r : ℕ} (lam : Fin r → ℤ) (h : ∀ i j : Fin r, i ≤ j → lam j ≤ lam i) :
    0 < wdim lam := by
  unfold wdim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with hij
  · have hl : (lam j : ℚ) ≤ (lam i : ℚ) := by exact_mod_cast h i j hij.le
    have hij' : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from hij)
    apply div_pos <;> linarith
  · exact one_pos

/- English proof (translation)
Unfold `Fs`. Use `split_ifs with hok`. Use `mul_nonneg (wdim_pos_of_antitone _ ?_).le (Nat.cast_nonneg _)` and prove the remaining obligations. Take `⟨-, -, hch, -⟩` from `hok`. Conclude with `antitone_last_of_isChain hch`.

Conclude with `le_refl 0`.
-/
theorem cl_Fs_nonneg (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (z : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t) :
    0 ≤ Fs C0 CE1 CE2 X j m rz ry z := by
  unfold Fs
  split_ifs with hok
  · refine mul_nonneg (wdim_pos_of_antitone _ ?_).le (Nat.cast_nonneg _)
    obtain ⟨-, -, hch, -⟩ := hok
    exact antitone_last_of_isChain hch
  · exact le_refl 0

/- English proof (translation)
Take `⟨Φ, hinj, hΦ⟩` from `hMU X hD hI hc j m hm rz ry hd`. Establish `hsupp : ∀ z, z ∈ Function.support (Fs C0 CE1 CE2 X j m rz ry) → SrcOK C0 CE1 CE2 X j m rz ry z`. Introduce `z hz`. Assume the negation of the conclusion as `hn`. Apply `hz` to reduce the goal to its premises.

Unfold `Fs`. Rewrite using `[if_neg hn]`. Conclude with `(finsum_le_of_inj (Fs C0 CE1 CE2 X j m rz ry) (Gt (r := X.m) (mmLetters C0 CE1 CE2 X j rz ry) (X.seg C0 CE1 CE2 j).bPlus) Φ (Gt_nonneg _ _) (Gt_support_finite hCD _ _) (hinj.mono hsupp) (by`. Introduce `z hz`. Establish `hz'` using `hsupp z hz`.

Take `⟨h1, h2, h3, h4⟩` from `hΦ z hz'`. Establish `hjp : z.2.1.2 ≤ (X.seg C0 CE1 CE2 j).bPlus` using `le_trans hz'.2.1.2 (min_le_right _ _)`. Unfold `Fs Gt`. Rewrite using `[if_pos hz', if_pos ⟨h1, h2, by rw [h4]; exact hjp⟩, h3, h4])).1`.
-/
theorem cl_Fs_finite {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hCD : ChainDimAt)
    (hMU : MatchUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (X : Loc) [NeZero X.m] (hD : D1num X)
    (hI : HIext C0 CYb Cde Ck CD Cb X) (hc : CBound Cc X) (j : Fin (numSeg X.TT)) (m : ℝ) (hm : 0 ≤ m)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry)) :
    (Function.support (Fs C0 CE1 CE2 X j m rz ry)).Finite := by
  classical
  obtain ⟨Φ, hinj, hΦ⟩ := hMU X hD hI hc j m hm rz ry hd
  have hsupp : ∀ z, z ∈ Function.support (Fs C0 CE1 CE2 X j m rz ry) → SrcOK C0 CE1 CE2 X j m rz ry z := by
    intro z hz
    by_contra hn
    apply hz
    unfold Fs
    rw [if_neg hn]
  exact (finsum_le_of_inj (Fs C0 CE1 CE2 X j m rz ry)
    (Gt (r := X.m) (mmLetters C0 CE1 CE2 X j rz ry) (X.seg C0 CE1 CE2 j).bPlus) Φ
    (Gt_nonneg _ _) (Gt_support_finite hCD _ _) (hinj.mono hsupp) (by
      intro z hz
      have hz' := hsupp z hz
      obtain ⟨h1, h2, h3, h4⟩ := hΦ z hz'
      have hjp : z.2.1.2 ≤ (X.seg C0 CE1 CE2 j).bPlus := le_trans hz'.2.1.2 (min_le_right _ _)
      unfold Fs Gt
      rw [if_pos hz', if_pos ⟨h1, h2, by rw [h4]; exact hjp⟩, h3, h4])).1

/- English proof (translation)
The claim follows from `antitone_of_succ_le' lam (fun i j hij => by have e : j.castSucc = i.succ := Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega) have h1 := (h j).2 rw [e] at h1 exact le_trans h1 (h i).1)`.
-/
private theorem antitone_lam_of_inter {r : ℕ} {mu : Fin (r + 1) → ℤ} {lam : Fin r → ℤ} (h : Inter mu lam) :
    ∀ i j : Fin r, i ≤ j → lam j ≤ lam i :=
  antitone_of_succ_le' lam (fun i j hij => by
    have e : j.castSucc = i.succ := Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega)
    have h1 := (h j).2
    rw [e] at h1
    exact le_trans h1 (h i).1)

/- English proof (translation)
Introduce `X _ hD hI hc j m hm hmA rz ry hdig`. Take `⟨Ψ, hinj, hΨ⟩` from `hML X hD hI hc j m hm hmA rz ry hdig`. Establish `hfin` using `cl_Fs_finite hCD hMU X hD hI hc j m hm rz ry hdig`. Establish `e : (∑ᶠ z, Fs C0 CE1 CE2 X j m rz ry z) = ∑ᶠ b, ∑ᶠ x, ∑ᶠ ka, Fs C0 CE1 CE2 X j m rz ry (b, x, ka)`. Rewrite using `[finsum_curry _ hfin]`.

Use `finsum_congr (fun b => ?_)` and prove the remaining obligations. Conclude with `finsum_curry _ (hfin.preimage (fun y1 _ y2 _ h => (Prod.mk.inj h).2))`. Rewrite using `[chainCount_eq, ← e]`. Establish `key` using `cl_prod_le (fun x : (Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) × (Fin X.m → ℤ) => IsPair (((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) x.1 x.2 ∧ KeptPair X.p (X.La C0) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X …`. Introduce `a ha`.

Take `⟨⟨-, hint⟩, -⟩` from `ha`. Conclude with `wdim_pos_of_antitone _ (antitone_lam_of_inter hint))`. Use the proof step `⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k⌋₊`. Use the proof step `(fun jp => (sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℚ))`. Use the proof step `(by intro n; unfold sdXi; exact_mod_cast Nat.choose_pos (by omega))`.

Use the proof step `(Fs C0 CE1 CE2 X j m rz ry) (cl_Fs_nonneg C0 CE1 CE2 X j m rz ry) hfin`. Use the proof step `(fun t => Ψ (t.1.1, t.1.2, t.2))`. Use the proof step `(by`. Introduce `t ht t' ht' he`. Establish `h1` using `@hinj (t.1.1, t.1.2, t.2) ht (t'.1.1, t'.1.2, t'.2) ht' he`.

Establish `e1` using `congrArg (fun z => z.1) h1`. Establish `e2` using `congrArg (fun z => z.2.1) h1`. Establish `e3` using `congrArg (fun z => z.2.2) h1`. Simplify using `only at e1 e2 e3`. Conclude with `Prod.ext (Prod.ext e1 e2) e3)`.

Use the proof step `(by`. Introduce `t hp hj`. Establish `hok : TgtOK C0 CE1 CE2 X j m rz ry (t.1.1, t.1.2, t.2)`. Unfold `TgtOK`. Conclude with `⟨hp, hj⟩`.

Take `⟨hs, hl, hjp⟩` from `hΨ (t.1.1, t.1.2, t.2) hok`. Unfold `Fs`. Rewrite using `[if_pos hs, hl, hjp])`. Unfold `keptPairSum`. Use `key` and compare the differences between its conclusion and the goal.
-/
theorem match_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hCD : ChainDimAt)
    (hMU : MatchUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hML : MatchLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    MatchAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD hI hc j m hm hmA rz ry hdig
  obtain ⟨Ψ, hinj, hΨ⟩ := hML X hD hI hc j m hm hmA rz ry hdig
  have hfin := cl_Fs_finite hCD hMU X hD hI hc j m hm rz ry hdig
  have e : (∑ᶠ z, Fs C0 CE1 CE2 X j m rz ry z) =
      ∑ᶠ b, ∑ᶠ x, ∑ᶠ ka, Fs C0 CE1 CE2 X j m rz ry (b, x, ka) := by
    rw [finsum_curry _ hfin]
    refine finsum_congr (fun b => ?_)
    exact finsum_curry _ (hfin.preimage (fun y1 _ y2 _ h => (Prod.mk.inj h).2))
  rw [chainCount_eq, ← e]
  have key := cl_prod_le (fun x : (Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) × (Fin X.m → ℤ) =>
      IsPair (((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat) (clA C0 CE1 CE2 X j rz ry)
          (clC C0 CE1 CE2 X j rz ry) x.1 x.2 ∧
        KeptPair X.p (X.La C0) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) x.1 x.2)
    (fun x => wdim x.2)
    (by
      intro a ha
      obtain ⟨⟨-, hint⟩, -⟩ := ha
      exact wdim_pos_of_antitone _ (antitone_lam_of_inter hint))
    ⌊X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k⌋₊
    (fun jp => (sdXi X.m ((X.seg C0 CE1 CE2 j).bPlus - jp) : ℚ))
    (by intro n; unfold sdXi; exact_mod_cast Nat.choose_pos (by omega))
    (Fs C0 CE1 CE2 X j m rz ry) (cl_Fs_nonneg C0 CE1 CE2 X j m rz ry) hfin
    (fun t => Ψ (t.1.1, t.1.2, t.2))
    (by
      intro t ht t' ht' he
      have h1 := @hinj (t.1.1, t.1.2, t.2) ht (t'.1.1, t'.1.2, t'.2) ht' he
      have e1 := congrArg (fun z => z.1) h1
      have e2 := congrArg (fun z => z.2.1) h1
      have e3 := congrArg (fun z => z.2.2) h1
      simp only at e1 e2 e3
      exact Prod.ext (Prod.ext e1 e2) e3)
    (by
      intro t hp hj
      have hok : TgtOK C0 CE1 CE2 X j m rz ry (t.1.1, t.1.2, t.2) := by
        unfold TgtOK; exact ⟨hp, hj⟩
      obtain ⟨hs, hl, hjp⟩ := hΨ (t.1.1, t.1.2, t.2) hok
      unfold Fs
      rw [if_pos hs, hl, hjp])
  unfold keptPairSum
  convert key

/- English proof (translation)
Unfold `RestMatch`. Unfold `RestMatchUp at hMU`. Unfold `RestMatchLow at hML`. Use `transported_of_imp ?_ (transported_and hMU hML)` and prove the remaining obligations. Introduce `_ _ _ _ _ _ _ _ _ _ h`.

Conclude with `match_of hCD h.1 h.2`.
-/
theorem restMatch_of (hCD : ChainDimAt) (hMU : RestMatchUp) (hML : RestMatchLow) : RestMatch := by
  unfold RestMatch
  unfold RestMatchUp at hMU
  unfold RestMatchLow at hML
  refine transported_of_imp ?_ (transported_and hMU hML)
  intro _ _ _ _ _ _ _ _ _ _ h
  exact match_of hCD h.1 h.2

/- English proof (translation)
Conclude with `restCountLow_of hT (restMatch_of hCD hMU hML)`.
-/
theorem restCountLow_of' (hCD : ChainDimAt) (hT : RestTail) (hMU : RestMatchUp) (hML : RestMatchLow) : RestCountLow := by
  exact restCountLow_of hT (restMatch_of hCD hMU hML)

def pairChain {s r : ℕ} (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) :
    Fin (2 * s + 1 + 1) → Fin r → ℤ :=
  fun n => if h : (n : ℕ) < 2 * s + 1 then (fun t => mu ⟨(n : ℕ) + 1, by omega⟩ t.succ) else lam

def pairBlock {s r : ℕ} (S : SegData s) (rz ry : Fin s → Fin (r + 1) → ℕ) (Ai : Fin s → ℕ)
    (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) (jp : ℕ) : SegBlock s r where
  rz := rz
  ry := ry
  o := fun i => if (i : ℕ) < S.sigma then 0 else (pairO mu Ai i).toNat
  w := fun i => if (i : ℕ) < S.sigma then (pairW mu i).toNat else 0
  sg := fun i => if (i : ℕ) < S.sigma then (pairSg mu Ai i).toNat else 0
  oPlus := (pairD mu lam).toNat + jp

def pairLevel {s r : ℕ} (S : SegData s) (Ai : Fin s → ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) : Fin S.t → ℕ :=
  fun l => (pairSg mu Ai (uTop S l)).toNat

def pairMap (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (t : Tgt (segS X.TT j) X.m) : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t :=
  (pairBlock (X.seg C0 CE1 CE2 j) rz ry (clA C0 CE1 CE2 X j rz ry) t.1 t.2.1 t.2.2,
    (pairLevel (X.seg C0 CE1 CE2 j) (clA C0 CE1 CE2 X j rz ry) t.1, t.2.2), pairChain t.1 t.2.1)

def KeptBlockAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ t, TgtOK C0 CE1 CE2 X j m rz ry t → SrcOK C0 CE1 CE2 X j m rz ry (pairMap C0 CE1 CE2 X j rz ry t)

def KeptBlocksBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptBlockAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

/- English proof (translation)
Take `⟨h0, hs⟩` from `h`. Take `⟨h0', hs'⟩` from `h'`. It suffices to establish `H : ∀ k (hk : k < N + 1), ∑ i, mu ⟨k, hk⟩ i = ∑ i, mu' ⟨k, hk⟩ i from H n.val n.isLt`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `hk`. Establish `e : (⟨0, hk⟩ : Fin (N + 1)) = 0` using `by ext; simp`. Rewrite using `[e, h0, h0']`. Consider the case `succ k ih`.

Introduce `hk`. Establish `ih'` using `ih (by omega)`. Establish `a` using `hs ⟨k, by omega⟩`. Establish `b` using `hs' ⟨k, by omega⟩`. Simplify using `only [Fin.succ_mk, Fin.castSucc_mk] at a b`.

Unfold `Strip at a b`. Use `split_ifs at a b`. Use `a.2.2` as an intermediate fact. Use `b.2.2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `a.2.2` as an intermediate fact. Use `b.2.2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cl_chain_total {N r : ℕ} {LL : ChainLetters N} {mu mu' : Fin (N + 1) → Fin r → ℤ} (h : IsChain LL mu)
    (h' : IsChain LL mu') (n : Fin (N + 1)) : ∑ i, mu n i = ∑ i, mu' n i := by
  obtain ⟨h0, hs⟩ := h
  obtain ⟨h0', hs'⟩ := h'
  suffices H : ∀ k (hk : k < N + 1), ∑ i, mu ⟨k, hk⟩ i = ∑ i, mu' ⟨k, hk⟩ i from H n.val n.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have e : (⟨0, hk⟩ : Fin (N + 1)) = 0 := by ext; simp
    rw [e, h0, h0']
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have a := hs ⟨k, by omega⟩
    have b := hs' ⟨k, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at a b
    unfold Strip at a b
    split_ifs at a b
    · have := a.2.2; have := b.2.2; linarith
    · have := a.2.2; have := b.2.2; linarith

/- English proof (translation)
Establish `hl : lam = lam'`. Use `congrFun he (Fin.last _)` as an intermediate fact. Simplify `this` using `[pairChain]`. Take `⟨h0, -⟩` from `id h`. Take `⟨h0', -⟩` from `id h'`.

Use `⟨funext fun n => ?_, hl⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) n` and prove the remaining obligations. Rewrite using `[h0, h0']`. Establish `hsucc : ∀ t : Fin r, mu i.succ t.succ = mu' i.succ t.succ`. Introduce `t`.

Use `congrFun (congrFun he i.castSucc) t` as an intermediate fact. Simplify using `[pairChain, i.isLt] at this`. Conclude with `this`. Use function extensionality and compare the values at `t`. Use `Fin.cases ?_ (fun t' => hsucc t') t` and prove the remaining obligations.

Establish `htot` using `cl_chain_total h h' i.succ`. Rewrite `htot` using `[Fin.sum_univ_succ, Fin.sum_univ_succ]`. Establish `: ∑ t : Fin r, mu i.succ t.succ = ∑ t : Fin r, mu' i.succ t.succ` using `Finset.sum_congr rfl (fun t _ => hsucc t)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cl_chain_ext {s r : ℕ} {LL : ChainLetters (2 * s + 1)} {mu mu' : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ}
    {lam lam' : Fin r → ℤ} (h : IsChain LL mu) (h' : IsChain LL mu') (he : pairChain mu lam = pairChain mu' lam') :
    mu = mu' ∧ lam = lam' := by
  have hl : lam = lam' := by
    have := congrFun he (Fin.last _)
    simpa [pairChain] using this
  obtain ⟨h0, -⟩ := id h
  obtain ⟨h0', -⟩ := id h'
  refine ⟨funext fun n => ?_, hl⟩
  refine Fin.cases ?_ (fun i => ?_) n
  · rw [h0, h0']
  · have hsucc : ∀ t : Fin r, mu i.succ t.succ = mu' i.succ t.succ := by
      intro t
      have := congrFun (congrFun he i.castSucc) t
      simp [pairChain, i.isLt] at this
      exact this
    funext t
    refine Fin.cases ?_ (fun t' => hsucc t') t
    have htot := cl_chain_total h h' i.succ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at htot
    have : ∑ t : Fin r, mu i.succ t.succ = ∑ t : Fin r, mu' i.succ t.succ :=
      Finset.sum_congr rfl (fun t _ => hsucc t)
    linarith

/- English proof (translation)
Introduce `X _ hD hI hc j m hm hmA rz ry hdig`. Use `⟨pairMap C0 CE1 CE2 X j rz ry, ?_, fun t ht => ⟨h X hD hI hc j m hm hmA rz ry hdig t ht, ?_, rfl⟩⟩` and prove the remaining obligations. Introduce `t ht t' ht' he`. Establish `h3` using `congrArg (fun z => z.2.2) he`. Establish `h2` using `congrArg (fun z => z.2.1.2) he`.

Simplify using `only [pairMap] at h3 h2`. Take `⟨⟨⟨hch, -⟩, -⟩, -⟩` from `id ht`. Take `⟨⟨⟨hch', -⟩, -⟩, -⟩` from `id ht'`. Take `⟨e1, e2⟩` from `cl_chain_ext hch hch' h3`. Take `⟨a, b, c⟩` from `t`.

Take `⟨a', b', c'⟩` from `t'`. Simplify using `only at e1 e2 h2`. Substitute `e1` using the available equality. Substitute `e2` using the available equality. Substitute `h2` using the available equality.

Both sides reduce to the same expression. Simplify using `[pairMap, pairChain]`.
-/
theorem matchLow_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : KeptBlockAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    MatchLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j m hm hmA rz ry hdig
  refine ⟨pairMap C0 CE1 CE2 X j rz ry, ?_, fun t ht => ⟨h X hD hI hc j m hm hmA rz ry hdig t ht, ?_, rfl⟩⟩
  · intro t ht t' ht' he
    have h3 := congrArg (fun z => z.2.2) he
    have h2 := congrArg (fun z => z.2.1.2) he
    simp only [pairMap] at h3 h2
    obtain ⟨⟨⟨hch, -⟩, -⟩, -⟩ := id ht
    obtain ⟨⟨⟨hch', -⟩, -⟩, -⟩ := id ht'
    obtain ⟨e1, e2⟩ := cl_chain_ext hch hch' h3
    obtain ⟨a, b, c⟩ := t
    obtain ⟨a', b', c'⟩ := t'
    simp only at e1 e2 h2
    subst e1; subst e2; subst h2; rfl
  · simp [pairMap, pairChain]

/- English proof (translation)
Unfold `RestMatchLow`. Unfold `KeptBlocksBeyondThreshold at h`. Use `transported_of_imp ?_ h` and prove the remaining obligations. Introduce `_ _ _ _ _ _ _ _ _ _ h`. Conclude with `matchLow_of h`.
-/
theorem restMatchLow_of (h : KeptBlocksBeyondThreshold) : RestMatchLow := by
  unfold RestMatchLow
  unfold KeptBlocksBeyondThreshold at h
  refine transported_of_imp ?_ h
  intro _ _ _ _ _ _ _ _ _ _ h
  exact matchLow_of h

/- English proof (translation)
The claim follows from `restCountLow_of' hCD hT hMU (restMatchLow_of hK)`.
-/
theorem restCountLow_of'' (hCD : ChainDimAt) (hT : RestTail) (hMU : RestMatchUp) (hK : KeptBlocksBeyondThreshold) : RestCountLow :=
  restCountLow_of' hCD hT hMU (restMatchLow_of hK)

end Formalism.MainNotions.ColumnSystems.Pf
