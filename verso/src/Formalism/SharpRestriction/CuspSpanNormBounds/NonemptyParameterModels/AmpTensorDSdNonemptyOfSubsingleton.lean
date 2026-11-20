import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Inh

section

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB

/- English proof (translation)
Conclude with `⟨{ Wp := ℂ, Wq := ℂ, π := (fun _ => 0), π' := (fun _ => 0), z := 0, z' := 0, μG := 0, μW := 0, μW' := 0, μN := 0, νS := 0, νS' := 0 }⟩`.
-/
theorem amp_locW_nonempty (k r : ℕ) : Nonempty (LocW k r) := by
  exact ⟨{ Wp := ℂ, Wq := ℂ, π := (fun _ => 0), π' := (fun _ => 0), z := 0, z' := 0, μG := 0, μW := 0, μW' := 0, μN := 0, νS := 0, νS' := 0 }⟩

/- English proof (translation)
Use `letI : NormedAddCommGroup W.Wp := W.p1`. Use `letI : NormedAddCommGroup W.Wq := W.q1`. Conclude with `⟨{ H := ℂ, σ := fun _ => 0, B := fun _ => 0, B' := fun _ => 0, v0 := 0, cN := 0, deg := 0 }⟩`.
-/
theorem amp_locS_nonempty {k r : ℕ} (W : LocW k r) : Nonempty (LocS W) := by
  letI : NormedAddCommGroup W.Wp := W.p1
  letI : NormedAddCommGroup W.Wq := W.q1
  exact ⟨{ H := ℂ, σ := fun _ => 0, B := fun _ => 0, B' := fun _ => 0, v0 := 0, cN := 0, deg := 0 }⟩

/- English proof (translation)
Unfold `lamS`. Rewrite using `[dif_pos h]`.
-/
theorem amp_lamS_lo (R : Ranks) (P : HCParam R) (i : Fin R.r) (h : i.val < R.k - 1) :
    lamS R P i = (P.v ⟨i.val, h⟩ : ℝ) := by
  unfold lamS
  rw [dif_pos h]

/- English proof (translation)
Unfold `lamS`. Rewrite using `[dif_neg h, dif_pos h']`.
-/
theorem amp_lamS_hi (R : Ranks) (P : HCParam R) (i : Fin R.r) (h : ¬ i.val < R.k - 1)
    (h' : i.val - (R.k - 1) < R.m) : lamS R P i = -(P.b ⟨i.val - (R.k - 1), h'⟩ : ℝ) := by
  unfold lamS
  rw [dif_neg h, dif_pos h']

/- English proof (translation)
Establish `h1 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨j, by omega⟩ - P.b ⟨j, by omega⟩` using `P.gap_be ⟨j, by omega⟩`. Establish `h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨j + 1, h⟩ - P.e ⟨j, by omega⟩` using `P.gap_eb ⟨j, by omega⟩ h`. Establish `ht : (0 : ℚ) ≤ (R.t : ℚ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amp_b_lt (R : Ranks) (P : HCParam R) (j : ℕ) (h : j + 1 < R.m) :
    P.b ⟨j, by omega⟩ < P.b ⟨j + 1, h⟩ := by
  have h1 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨j, by omega⟩ - P.b ⟨j, by omega⟩ := P.gap_be ⟨j, by omega⟩
  have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨j + 1, h⟩ - P.e ⟨j, by omega⟩ := P.gap_eb ⟨j, by omega⟩ h
  have ht : (0 : ℚ) ≤ (R.t : ℚ) := Nat.cast_nonneg _
  linarith

/- English proof (translation)
Introduce `a b hab`. Take `⟨a, ha⟩` from `a`. Take `⟨b, hb⟩` from `b`. Establish `hab' : a < b` using `hab`. Use `clear hab`.

Proceed by induction on `b with`. Consider the case `zero => omega`. Consider the case `succ b ih`. Break down `(show a < b ∨ a = b by omega) with h | h` into its components or cases. Conclude with `lt_trans (hf b hb) (ih (by omega) h)`.

Establish `e : (⟨a, ha⟩ : Fin n) = ⟨b, by omega⟩` using `Fin.ext h`. Rewrite using `[e]`. Conclude with `hf b hb`.
-/
private theorem strictAnti_of_succ_lt' (n : ℕ) (f : Fin n → ℝ)
    (hf : ∀ (i : ℕ) (h : i + 1 < n), f ⟨i + 1, h⟩ < f ⟨i, by omega⟩) : StrictAnti f := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a < b := hab
  clear hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases (show a < b ∨ a = b by omega) with h | h
    · exact lt_trans (hf b hb) (ih (by omega) h)
    · have e : (⟨a, ha⟩ : Fin n) = ⟨b, by omega⟩ := Fin.ext h
      rw [e]
      exact hf b hb

/- English proof (translation)
Establish `hr : R.r = R.k + R.m - 1` using `rfl`. Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Apply `strictAnti_of_succ_lt'` to reduce the goal to its premises. Introduce `i hi`.

Distinguish the cases in `h1 : i + 1 < R.k - 1`. Rewrite using `[amp_lamS_lo R P ⟨i + 1, hi⟩ h1, amp_lamS_lo R P ⟨i, by omega⟩ (show i < R.k - 1 by omega)]`. Establish `key : P.v ⟨i + 1, h1⟩ < P.v ⟨i, by omega⟩` using `lt_trans (P.u_gt_v ⟨i + 1, h1⟩) (P.v_gt_u ⟨i, by omega⟩)`. Conclude with `key` after adjusting the coercions. Distinguish the cases in `h2 : i < R.k - 1`.

Rewrite using `[amp_lamS_hi R P ⟨i + 1, hi⟩ h1 (show i + 1 - (R.k - 1) < R.m by omega), amp_lamS_lo R P ⟨i, by omega⟩ h2]`. Establish `e1 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩` using `congrArg P.b (Fin.ext (show i + 1 - (R.k - 1) = 0 by omega))`. Establish `e2 : P.u ⟨i + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩` using `congrArg P.u (Fin.ext (show i + 1 = R.k - 1 by omega))`. Establish `k1` using `P.u_last_gt (by omega) (by omega)`. Establish `k2' : P.u ⟨i + 1, by omega⟩ < P.v ⟨i, h2⟩` using `P.v_gt_u ⟨i, h2⟩`.

Rewrite `k2'` using `[e2]`. Establish `key : -P.b ⟨i + 1 - (R.k - 1), by omega⟩ < P.v ⟨i, h2⟩`. Rewrite using `[e1]`. Conclude with `lt_trans k1 k2'`. Conclude with `key` after adjusting the coercions.

Rewrite using `[amp_lamS_hi R P ⟨i + 1, hi⟩ h1 (show i + 1 - (R.k - 1) < R.m by omega), amp_lamS_hi R P ⟨i, by omega⟩ h2 (show i - (R.k - 1) < R.m by omega)]`. Establish `e1 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨i - (R.k - 1) + 1, by omega⟩` using `congrArg P.b (Fin.ext (show i + 1 - (R.k - 1) = i - (R.k - 1) + 1 by omega))`. Establish `key` using `amp_b_lt R P (i - (R.k - 1)) (by omega)`. Rewrite `key` using `[← e1]`. Conclude with `neg_lt_neg key` after adjusting the coercions.
-/
private theorem strictAnti_lamS (R : Ranks) (P : HCParam R) : StrictAnti (lamS R P) := by
  have hr : R.r = R.k + R.m - 1 := rfl
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  apply strictAnti_of_succ_lt'
  intro i hi
  by_cases h1 : i + 1 < R.k - 1
  · rw [amp_lamS_lo R P ⟨i + 1, hi⟩ h1, amp_lamS_lo R P ⟨i, by omega⟩ (show i < R.k - 1 by omega)]
    have key : P.v ⟨i + 1, h1⟩ < P.v ⟨i, by omega⟩ :=
      lt_trans (P.u_gt_v ⟨i + 1, h1⟩) (P.v_gt_u ⟨i, by omega⟩)
    exact_mod_cast key
  · by_cases h2 : i < R.k - 1
    · rw [amp_lamS_hi R P ⟨i + 1, hi⟩ h1 (show i + 1 - (R.k - 1) < R.m by omega),
        amp_lamS_lo R P ⟨i, by omega⟩ h2]
      have e1 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩ :=
        congrArg P.b (Fin.ext (show i + 1 - (R.k - 1) = 0 by omega))
      have e2 : P.u ⟨i + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ :=
        congrArg P.u (Fin.ext (show i + 1 = R.k - 1 by omega))
      have k1 := P.u_last_gt (by omega) (by omega)
      have k2' : P.u ⟨i + 1, by omega⟩ < P.v ⟨i, h2⟩ := P.v_gt_u ⟨i, h2⟩
      rw [e2] at k2'
      have key : -P.b ⟨i + 1 - (R.k - 1), by omega⟩ < P.v ⟨i, h2⟩ := by
        rw [e1]
        exact lt_trans k1 k2'
      exact_mod_cast key
    · rw [amp_lamS_hi R P ⟨i + 1, hi⟩ h1 (show i + 1 - (R.k - 1) < R.m by omega),
        amp_lamS_hi R P ⟨i, by omega⟩ h2 (show i - (R.k - 1) < R.m by omega)]
      have e1 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨i - (R.k - 1) + 1, by omega⟩ :=
        congrArg P.b (Fin.ext (show i + 1 - (R.k - 1) = i - (R.k - 1) + 1 by omega))
      have key := amp_b_lt R P (i - (R.k - 1)) (by omega)
      rw [← e1] at key
      exact_mod_cast neg_lt_neg key

/- English proof (translation)
Introduce `a b hab`. Conclude with `strictAnti_lamS R P (show Fin.cast (dimS_eq R) a < Fin.cast (dimS_eq R) b from hab)`.
-/
theorem amp_lamSH_strictAnti (R : Ranks) (P : HCParam R) : StrictAnti (lamSH R P) := by
  intro a b hab
  exact strictAnti_lamS R P (show Fin.cast (dimS_eq R) a < Fin.cast (dimS_eq R) b from hab)

/- English proof (translation)
Use `⟨amp_lamSH_strictAnti R P, fun a => ?_⟩` and prove the remaining obligations. Establish `hval : ∃ z : ℤ, lamSH R P a = z`. Simplify using `only [lamSH, lamS]`. Use `split_ifs with h1 h2`. Take `⟨z, hz⟩` from `P.v_int ⟨_, h1⟩`.

Conclude with `⟨z, by have h3 := congrArg (fun x : ℚ => (x : ℝ)) hz; simpa using h3⟩`. Take `⟨z, hz⟩` from `P.b_int ⟨_, h2⟩`. Conclude with `⟨-z, by have h3 := congrArg (fun x : ℚ => -(x : ℝ)) hz; simpa using h3⟩`. Conclude with `⟨0, by simp⟩`. Take `⟨z, hz⟩` from `hval`.

Take `⟨q, hq⟩` from `R.k_even`. Use `⟨z - (R.rS : ℤ) - (q : ℤ), ?_⟩` and prove the remaining obligations. Establish `hk : (R.k : ℝ) = (q : ℝ) + q` using `by exact_mod_cast hq`. Use `push_cast`. Combine the linear relations using `[hz, hk]`.
-/
theorem amp_isHCParam_lamSH (R : Ranks) (P : HCParam R) : IsHCParam (lamSH R P) := by
  refine ⟨amp_lamSH_strictAnti R P, fun a => ?_⟩
  have hval : ∃ z : ℤ, lamSH R P a = z := by
    simp only [lamSH, lamS]
    split_ifs with h1 h2
    · obtain ⟨z, hz⟩ := P.v_int ⟨_, h1⟩
      exact ⟨z, by have h3 := congrArg (fun x : ℚ => (x : ℝ)) hz; simpa using h3⟩
    · obtain ⟨z, hz⟩ := P.b_int ⟨_, h2⟩
      exact ⟨-z, by have h3 := congrArg (fun x : ℚ => -(x : ℝ)) hz; simpa using h3⟩
    · exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hval
  obtain ⟨q, hq⟩ := R.k_even
  refine ⟨z - (R.rS : ℤ) - (q : ℤ), ?_⟩
  have hk : (R.k : ℝ) = (q : ℝ) + q := by exact_mod_cast hq
  push_cast
  linarith [hz, hk]

/- English proof (translation)
The claim follows from `amp_isHCParam_lamSH D.R (D.hc τ)`.
-/
theorem amp_isHCParam_lamD (D : D7) (τ : D.what₂.Tau) : IsHCParam (lamD D τ) := amp_isHCParam_lamSH D.R (D.hc τ)

/- English proof (translation)
Establish `hlt : r + k < 2 * r + k + 1` using `by omega`. Take `⟨i0, hi0⟩ : ∃ i0 : Fin (2 * r + k + 1), i0.val = r + k` from `⟨⟨r + k, hlt⟩, rfl⟩`. Use `⟨Pi.single i0 ((Real.sqrt T : ℝ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Apply `Pi.single_eq_of_ne` to reduce the goal to its premises.

Introduce `h`. Rewrite `hi` using `[h, hi0]`. Use linear arithmetic over natural numbers and integers. Establish `hsum : herm (Hpk k r) (Pi.single i0 ((Real.sqrt T : ℝ) : ℂ)) (Pi.single i0 ((Real.sqrt T : ℝ) : ℂ)) = star ((Real.sqrt T : ℝ) : ℂ) * (Hpk k r i0 i0 * ((Real.sqrt T : ℝ) : ℂ))` using `by show ∑ i, star ((Pi.single i0 ((Real.sqrt T : ℝ) : ℂ) : Fin (2 * r + k + 1) → ℂ) i) * ∑ j, Hpk k r i j * (Pi.single i0 ((Real.sqrt T : ℝ) : ℂ) : Fin (2 * r + k + 1) → ℂ) j = _`. Rewrite using `[Finset.sum_eq_single i0]`.

Rewrite using `[Finset.sum_eq_single i0]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[hj]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i0) h`. Introduce `i _ hi`. Simplify using `[hi]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i0) h`.

Establish `hH : Hpk k r i0 i0 = -1`. Simplify using `[Hpk, hi0]`. Establish `hs : Real.sqrt T * Real.sqrt T = T` using `Real.mul_self_sqrt hT`. Establish `e : star ((Real.sqrt T : ℝ) : ℂ) * (-1 * ((Real.sqrt T : ℝ) : ℂ)) = ((-(Real.sqrt T * Real.sqrt T) : ℝ) : ℂ)`. Simplify using `[Complex.ext_iff]`.

Unfold `Tz`. Rewrite using `[hsum, hH, e, Complex.ofReal_re, hs, neg_neg]`.
-/
theorem amp_z_exists (k r : ℕ) (T : ℝ) (hT : 0 ≤ T) : ∃ z : Fin (2 * r + k + 1) → ℂ, inWb k r z ∧ Tz k r z = T := by
  have hlt : r + k < 2 * r + k + 1 := by omega
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (2 * r + k + 1), i0.val = r + k := ⟨⟨r + k, hlt⟩, rfl⟩
  refine ⟨Pi.single i0 ((Real.sqrt T : ℝ) : ℂ), ?_, ?_⟩
  · intro i hi
    apply Pi.single_eq_of_ne
    intro h
    rw [h, hi0] at hi
    omega
  · have hsum : herm (Hpk k r) (Pi.single i0 ((Real.sqrt T : ℝ) : ℂ)) (Pi.single i0 ((Real.sqrt T : ℝ) : ℂ)) =
        star ((Real.sqrt T : ℝ) : ℂ) * (Hpk k r i0 i0 * ((Real.sqrt T : ℝ) : ℂ)) := by
      show ∑ i, star ((Pi.single i0 ((Real.sqrt T : ℝ) : ℂ) : Fin (2 * r + k + 1) → ℂ) i) *
        ∑ j, Hpk k r i j * (Pi.single i0 ((Real.sqrt T : ℝ) : ℂ) : Fin (2 * r + k + 1) → ℂ) j = _
      rw [Finset.sum_eq_single i0]
      · rw [Finset.sum_eq_single i0]
        · simp
        · intro j _ hj
          simp [hj]
        · intro h
          exact absurd (Finset.mem_univ i0) h
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ i0) h
    have hH : Hpk k r i0 i0 = -1 := by
      simp [Hpk, hi0]
    have hs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT
    have e : star ((Real.sqrt T : ℝ) : ℂ) * (-1 * ((Real.sqrt T : ℝ) : ℂ)) =
        ((-(Real.sqrt T * Real.sqrt T) : ℝ) : ℂ) := by
      simp [Complex.ext_iff]
    unfold Tz
    rw [hsum, hH, e, Complex.ofReal_re, hs, neg_neg]

def amp_lam (k r N M : ℕ) : Fin (2 * r + k + 1) → ℝ := fun s =>
  (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 +
    (if s.val < k - 1 then (N : ℝ) * ((k : ℝ) - (s.val : ℝ)) else -(M : ℝ) - (N : ℝ) * (s.val : ℝ))

def amp_u (k r N : ℕ) (δ : ℝ) : Fin k → ℝ := fun i =>
  (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i.val : ℝ)) + (if i.val = 1 then δ else 1 / 2)

/- English proof (translation)
Simplify using `only [amp_lam, if_pos h]`.
-/
theorem amp_lam_lo (k r N M : ℕ) (s : Fin (2 * r + k + 1)) (h : s.val < k - 1) :
    amp_lam k r N M s = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (s.val : ℝ)) := by
  simp only [amp_lam, if_pos h]

/- English proof (translation)
Simplify using `only [amp_lam, if_neg h]`.
-/
theorem amp_lam_hi (k r N M : ℕ) (s : Fin (2 * r + k + 1)) (h : ¬ s.val < k - 1) :
    amp_lam k r N M s = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (-(M : ℝ) - (N : ℝ) * (s.val : ℝ)) := by
  simp only [amp_lam, if_neg h]

/- English proof (translation)
Establish `hlt : s.val < s'.val` using `h`. Establish `hss : (s.val : ℝ) + 1 ≤ (s'.val : ℝ)` using `by exact_mod_cast hlt`. Establish `hN : (0 : ℝ) ≤ (N : ℝ)` using `Nat.cast_nonneg _`. Establish `hM : (0 : ℝ) ≤ (M : ℝ)` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ (s.val : ℝ)` using `Nat.cast_nonneg _`.

Apply the tactic sequence `by_cases h1 : s.val < k - 1 <;> by_cases h2 : s'.val < k - 1`. Rewrite using `[amp_lam_lo k r N M s h1, amp_lam_lo k r N M s' h2]`. Use polynomial arithmetic with `[mul_nonneg hN (show (0 : ℝ) ≤ (s'.val : ℝ) - s.val - 1 by linarith)]`. Rewrite using `[amp_lam_lo k r N M s h1, amp_lam_hi k r N M s' h2]`. Establish `hsk : (s.val : ℝ) ≤ (k : ℝ)` using `by exact_mod_cast (show s.val ≤ k by omega)`.

Use polynomial arithmetic with `[mul_nonneg hN (show (0 : ℝ) ≤ (k : ℝ) - s.val by linarith), mul_nonneg hN (show (0 : ℝ) ≤ (s'.val : ℝ) - 1 by linarith)]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[amp_lam_hi k r N M s h1, amp_lam_hi k r N M s' h2]`. Use polynomial arithmetic with `[mul_nonneg hN (show (0 : ℝ) ≤ (s'.val : ℝ) - s.val - 1 by linarith)]`.
-/
theorem amp_lam_gap (k r N M : ℕ) (s s' : Fin (2 * r + k + 1)) (h : s < s') :
    (N : ℝ) ≤ amp_lam k r N M s - amp_lam k r N M s' := by
  have hlt : s.val < s'.val := h
  have hss : (s.val : ℝ) + 1 ≤ (s'.val : ℝ) := by exact_mod_cast hlt
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (s.val : ℝ) := Nat.cast_nonneg _
  by_cases h1 : s.val < k - 1 <;> by_cases h2 : s'.val < k - 1
  · rw [amp_lam_lo k r N M s h1, amp_lam_lo k r N M s' h2]
    nlinarith [mul_nonneg hN (show (0 : ℝ) ≤ (s'.val : ℝ) - s.val - 1 by linarith)]
  · rw [amp_lam_lo k r N M s h1, amp_lam_hi k r N M s' h2]
    have hsk : (s.val : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show s.val ≤ k by omega)
    nlinarith [mul_nonneg hN (show (0 : ℝ) ≤ (k : ℝ) - s.val by linarith),
      mul_nonneg hN (show (0 : ℝ) ≤ (s'.val : ℝ) - 1 by linarith)]
  · omega
  · rw [amp_lam_hi k r N M s h1, amp_lam_hi k r N M s' h2]
    nlinarith [mul_nonneg hN (show (0 : ℝ) ≤ (s'.val : ℝ) - s.val - 1 by linarith)]

/- English proof (translation)
Introduce `s s' hne`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `h3` using `amp_lam_gap k r N M s s' h`. Conclude with `le_trans hg (le_trans h3 (le_abs_self _))`. Establish `h3` using `amp_lam_gap k r N M s' s h`.

Rewrite using `[abs_sub_comm]`. Conclude with `le_trans hg (le_trans h3 (le_abs_self _))`.
-/
theorem amp_lam_allGaps (k r N M : ℕ) (g : ℝ) (hg : g ≤ N) : AllGaps (amp_lam k r N M) g := by
  intro s s' hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h3 := amp_lam_gap k r N M s s' h
    exact le_trans hg (le_trans h3 (le_abs_self _))
  · have h3 := amp_lam_gap k r N M s' s h
    rw [abs_sub_comm]
    exact le_trans hg (le_trans h3 (le_abs_self _))

/- English proof (translation)
Use `⟨fun s s' h => ?_, fun s => ?_⟩` and prove the remaining obligations. Establish `h3` using `amp_lam_gap k r N M s s' h`. Establish `h1 : (1 : ℝ) ≤ (N : ℝ)` using `by exact_mod_cast hN`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h1 : s.val < k - 1`.

Use `⟨(N : ℤ) * ((k : ℤ) - (s.val : ℤ)), ?_⟩` and prove the remaining obligations. Rewrite using `[amp_lam_lo k r N M s h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-(M : ℤ) - (N : ℤ) * (s.val : ℤ), ?_⟩` and prove the remaining obligations.

Rewrite using `[amp_lam_hi k r N M s h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem amp_lam_hc (k r N M : ℕ) (hN : 1 ≤ N) : IsHCParam (amp_lam k r N M) := by
  refine ⟨fun s s' h => ?_, fun s => ?_⟩
  · have h3 := amp_lam_gap k r N M s s' h
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  · by_cases h1 : s.val < k - 1
    · refine ⟨(N : ℤ) * ((k : ℤ) - (s.val : ℤ)), ?_⟩
      rw [amp_lam_lo k r N M s h1]
      push_cast
      ring
    · refine ⟨-(M : ℤ) - (N : ℤ) * (s.val : ℤ), ?_⟩
      rw [amp_lam_hi k r N M s h1]
      push_cast
      ring

/- English proof (translation)
Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Simplify using `only [amp_u]`. Apply the tactic sequence `split_ifs <;> constructor <;> linarith`.
-/
private theorem amp_u_mem_open_interval_of_lt (k r N : ℕ) (δ : ℝ) (h0 : 0 < δ) (h1 : δ < N) (hN : 1 ≤ N) (i : ℕ) (hi : i < k) :
    (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) < amp_u k r N δ ⟨i, hi⟩ ∧
      amp_u k r N δ ⟨i, hi⟩ < (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) + N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [amp_u]
  split_ifs <;> constructor <;> linarith

/- English proof (translation)
Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Use `⟨fun i hi => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `hl : amp_lam k r N M ⟨i, by omega⟩ = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ))` using `amp_lam_lo k r N M ⟨i, by omega⟩ (show i < k - 1 by omega)`. Establish `a1` using `(amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN i (by omega)).1`. Establish `a2` using `(amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN (i + 1) hi).2`.

Establish `hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1` using `by push_cast; ring`. Rewrite `a2` using `[hc]`. Rewrite using `[hl]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hl : amp_lam k r N M ⟨k - 1, by omega⟩ = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (-(M : ℝ) - (N : ℝ) * ((k - 1 : ℕ) : ℝ))` using `amp_lam_hi k r N M ⟨k - 1, by omega⟩ (show ¬ (k - 1 < k - 1) by omega)`.

Establish `a1` using `(amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN (k - 1) (by omega)).1`. Establish `hM0 : (0 : ℝ) ≤ M` using `Nat.cast_nonneg _`. Establish `hk1 : (1 : ℝ) ≤ k` using `by exact_mod_cast (show 1 ≤ k by omega)`. Establish `p` using `mul_le_mul_of_nonneg_left hk1 hN0`. Rewrite using `[hl]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amp_interlace (k r N M : ℕ) (δ : ℝ) (h0 : 0 < δ) (h1 : δ < N) (hN : 1 ≤ N) :
    InterlaceS (by omega) (amp_u k r N δ) (amp_lam k r N M) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  refine ⟨fun i hi => ?_, fun h => ?_⟩
  · have hl : amp_lam k r N M ⟨i, by omega⟩ =
        (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) :=
      amp_lam_lo k r N M ⟨i, by omega⟩ (show i < k - 1 by omega)
    have a1 := (amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN i (by omega)).1
    have a2 := (amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN (i + 1) hi).2
    have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hc] at a2
    rw [hl]
    constructor <;> linarith
  · have hl : amp_lam k r N M ⟨k - 1, by omega⟩ =
        (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (-(M : ℝ) - (N : ℝ) * ((k - 1 : ℕ) : ℝ)) :=
      amp_lam_hi k r N M ⟨k - 1, by omega⟩ (show ¬ (k - 1 < k - 1) by omega)
    have a1 := (amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN (k - 1) (by omega)).1
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have p := mul_le_mul_of_nonneg_left hk1 hN0
    rw [hl]
    linarith

/- English proof (translation)
Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨⟨i, hik⟩, hi⟩⟩`. Assume the negation of the conclusion as `h2`. Rewrite `hi` using `[amp_lam_hi k r N M s h2]`.

Establish `a1` using `(amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN i hik).1`. Establish `hik' : (i : ℝ) + 1 ≤ k` using `by exact_mod_cast (show i + 1 ≤ k by omega)`. Establish `hM0 : (0 : ℝ) ≤ M` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ s.val` using `Nat.cast_nonneg _`. Establish `p1` using `mul_nonneg hN0 hs0`.

Establish `p2` using `mul_nonneg hN0 (show (0 : ℝ) ≤ (k : ℝ) - i by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h2`. Establish `hsl` using `s.isLt`. Use `⟨⟨⟨s.val, by omega⟩, ?_⟩, ⟨⟨s.val + 1, by omega⟩, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[amp_lam_lo k r N M s h2]`. Establish `a1` using `(amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN s.val (by omega)).1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[amp_lam_lo k r N M s h2]`. Establish `a2` using `(amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN (s.val + 1) (by omega)).2`.

Establish `hc : ((s.val + 1 : ℕ) : ℝ) = (s.val : ℝ) + 1` using `by push_cast; ring`. Rewrite `a2` using `[hc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amp_cloud_iff (k r N M : ℕ) (δ : ℝ) (h0 : 0 < δ) (h1 : δ < N) (hN : 1 ≤ N) (s : Fin (2 * r + k + 1)) :
    IsCloud (amp_u k r N δ) (amp_lam k r N M) s ↔ s.val < k - 1 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  constructor
  · rintro ⟨_, ⟨⟨i, hik⟩, hi⟩⟩
    by_contra h2
    rw [amp_lam_hi k r N M s h2] at hi
    have a1 := (amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN i hik).1
    have hik' : (i : ℝ) + 1 ≤ k := by exact_mod_cast (show i + 1 ≤ k by omega)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) ≤ s.val := Nat.cast_nonneg _
    have p1 := mul_nonneg hN0 hs0
    have p2 := mul_nonneg hN0 (show (0 : ℝ) ≤ (k : ℝ) - i by linarith)
    linarith
  · intro h2
    have hsl := s.isLt
    refine ⟨⟨⟨s.val, by omega⟩, ?_⟩, ⟨⟨s.val + 1, by omega⟩, ?_⟩⟩
    · rw [amp_lam_lo k r N M s h2]
      have a1 := (amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN s.val (by omega)).1
      linarith
    · rw [amp_lam_lo k r N M s h2]
      have a2 := (amp_u_mem_open_interval_of_lt k r N δ h0 h1 hN (s.val + 1) (by omega)).2
      have hc : ((s.val + 1 : ℕ) : ℝ) = (s.val : ℝ) + 1 := by push_cast; ring
      rw [hc] at a2
      linarith

/- English proof (translation)
Introduce `s`. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ s.val` using `Nat.cast_nonneg _`. Establish `hsl` using `s.isLt`. Establish `hs : (s.val : ℝ) + 1 ≤ ((2 * r + k + 1 : ℕ) : ℝ)`.

Conclude with `(show s.val + 1 ≤ 2 * r + k + 1 by omega)` after adjusting the coercions. Establish `hk : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)`. Establish `hM' : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)`. Rewrite using `[hM]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hNk` using `mul_le_mul_of_nonneg_left hk hN0`. Establish `hNs` using `mul_nonneg hN0 hs0`. Establish `hNsc` using `mul_le_mul_of_nonneg_left (show (s.val : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith) hN0`. Establish `hNc` using `mul_nonneg hN0 (show (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith)`.

Prove the components needed by the constructor for the conclusion. Introduce `hc`. Establish `h2` using `(amp_cloud_iff k r N M δ h0 h1 hN s).1 hc`. Establish `hsk : (s.val : ℝ) ≤ k` using `by exact_mod_cast (show s.val ≤ k by omega)`. Establish `hNsk` using `mul_le_mul_of_nonneg_left hsk hN0`.

Rewrite using `[amp_lam_lo k r N M s h2]`. Apply the tactic sequence `constructor <;> nlinarith`. Introduce `hc`. Establish `h2 : ¬ s.val < k - 1` using `fun h3 => hc ((amp_cloud_iff k r N M δ h0 h1 hN s).2 h3)`. Rewrite using `[amp_lam_hi k r N M s h2]`.

Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem amp_shape (k r N M : ℕ) (δ : ℝ) (h0 : 0 < δ) (h1 : δ < N) (hN : 1 ≤ N)
    (hM : M = 9 * (2 * r + k + 1) + 9 * N * (2 * r + k + 1)) :
    ShapeS (amp_u k r N δ) (amp_lam k r N M) ((M : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2) := by
  intro s
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s.val := Nat.cast_nonneg _
  have hsl := s.isLt
  have hs : (s.val : ℝ) + 1 ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show s.val + 1 ≤ 2 * r + k + 1 by omega)
  have hk : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)
  have hM' : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    rw [hM]; push_cast; ring
  have hNk := mul_le_mul_of_nonneg_left hk hN0
  have hNs := mul_nonneg hN0 hs0
  have hNsc := mul_le_mul_of_nonneg_left (show (s.val : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith) hN0
  have hNc := mul_nonneg hN0 (show (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith)
  constructor
  · intro hc
    have h2 := (amp_cloud_iff k r N M δ h0 h1 hN s).1 hc
    have hsk : (s.val : ℝ) ≤ k := by exact_mod_cast (show s.val ≤ k by omega)
    have hNsk := mul_le_mul_of_nonneg_left hsk hN0
    rw [amp_lam_lo k r N M s h2]
    constructor <;> nlinarith
  · intro hc
    have h2 : ¬ s.val < k - 1 := fun h3 => hc ((amp_cloud_iff k r N M δ h0 h1 hN s).2 h3)
    rw [amp_lam_hi k r N M s h2]
    constructor <;> nlinarith

/- English proof (translation)
Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ s.val` using `Nat.cast_nonneg _`. Establish `hsl` using `s.isLt`. Establish `hs : (s.val : ℝ) + 1 ≤ ((2 * r + k + 1 : ℕ) : ℝ)`. Conclude with `(show s.val + 1 ≤ 2 * r + k + 1 by omega)` after adjusting the coercions.

Establish `hk : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)`. Establish `hM' : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)`. Rewrite using `[hM]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hNk` using `mul_le_mul_of_nonneg_left hk hN0`. Establish `hNs` using `mul_nonneg hN0 hs0`. Establish `hNsc` using `mul_le_mul_of_nonneg_left (show (s.val : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith) hN0`. Establish `hNc` using `mul_nonneg hN0 (show (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith)`. Rewrite using `[abs_le]`.

Distinguish the cases in `h1 : s.val < k - 1`. Rewrite using `[amp_lam_lo k r N M s h1]`. Establish `hsk : (s.val : ℝ) ≤ k` using `by exact_mod_cast (show s.val ≤ k by omega)`. Establish `hNsk` using `mul_le_mul_of_nonneg_left hsk hN0`. Apply the tactic sequence `constructor <;> nlinarith`.

Rewrite using `[amp_lam_hi k r N M s h1]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem amp_lam_abs (k r N M : ℕ) (hN : 1 ≤ N) (hM : M = 9 * (2 * r + k + 1) + 9 * N * (2 * r + k + 1))
    (s : Fin (2 * r + k + 1)) : |amp_lam k r N M s| ≤ 2 * (M : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s.val := Nat.cast_nonneg _
  have hsl := s.isLt
  have hs : (s.val : ℝ) + 1 ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show s.val + 1 ≤ 2 * r + k + 1 by omega)
  have hk : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)
  have hM' : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    rw [hM]; push_cast; ring
  have hNk := mul_le_mul_of_nonneg_left hk hN0
  have hNs := mul_nonneg hN0 hs0
  have hNsc := mul_le_mul_of_nonneg_left (show (s.val : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith) hN0
  have hNc := mul_nonneg hN0 (show (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) by linarith)
  rw [abs_le]
  by_cases h1 : s.val < k - 1
  · rw [amp_lam_lo k r N M s h1]
    have hsk : (s.val : ℝ) ≤ k := by exact_mod_cast (show s.val ≤ k by omega)
    have hNsk := mul_le_mul_of_nonneg_left hsk hN0
    constructor <;> nlinarith
  · rw [amp_lam_hi k r N M s h1]
    constructor <;> nlinarith

/- English proof (translation)
Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hil` using `i.isLt`. Establish `hi : (i.val : ℝ) + 1 ≤ k` using `by exact_mod_cast (show i.val + 1 ≤ k by omega)`. Establish `hi0 : (0 : ℝ) ≤ i.val` using `Nat.cast_nonneg _`.

Establish `hk : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)`. Establish `hc1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (show 1 ≤ 2 * r + k + 1 by omega)`. Establish `hM' : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)`. Rewrite using `[hM]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hNk` using `mul_le_mul_of_nonneg_left hk hN0`. Establish `hNi` using `mul_le_mul_of_nonneg_left (show (i.val : ℝ) ≤ k by linarith) hN0`. Establish `hNi0` using `mul_nonneg hN0 hi0`. Establish `hNc` using `mul_le_mul_of_nonneg_left hc1 hN0`.

Simplify using `only [amp_u]`. Rewrite using `[abs_le]`. Apply the tactic sequence `split_ifs <;> constructor <;> nlinarith`.
-/
theorem amp_u_abs (k r N M : ℕ) (δ : ℝ) (h0 : 0 < δ) (h1 : δ < N) (hN : 1 ≤ N)
    (hM : M = 9 * (2 * r + k + 1) + 9 * N * (2 * r + k + 1)) (i : Fin k) : |amp_u k r N δ i| ≤ 2 * (M : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hil := i.isLt
  have hi : (i.val : ℝ) + 1 ≤ k := by exact_mod_cast (show i.val + 1 ≤ k by omega)
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hk : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (show k ≤ 2 * r + k + 1 by omega)
  have hc1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * r + k + 1 by omega)
  have hM' : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    rw [hM]; push_cast; ring
  have hNk := mul_le_mul_of_nonneg_left hk hN0
  have hNi := mul_le_mul_of_nonneg_left (show (i.val : ℝ) ≤ k by linarith) hN0
  have hNi0 := mul_nonneg hN0 hi0
  have hNc := mul_le_mul_of_nonneg_left hc1 hN0
  simp only [amp_u]
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith

/- English proof (translation)
Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hU : ∀ (i : ℕ) (hi : i < k), amp_u k r N (1 / 2) ⟨i, hi⟩ = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) + 1 / 2`. Introduce `i hi`. Simplify using `only [amp_u, ite_self]`. Establish `c0` using `(amp_cloud_iff k r N M (1 / 2) (by norm_num) (by linarith) hN ⟨0, by omega⟩).2 (show 0 < k - 1 by omega)`.

Establish `c2` using `(amp_cloud_iff k r N M (1 / 2) (by norm_num) (by linarith) hN ⟨2, by omega⟩).2 (show 2 < k - 1 by omega)`. Establish `l0` using `amp_lam_lo k r N M ⟨0, by omega⟩ (show 0 < k - 1 by omega)`. Establish `l2` using `amp_lam_lo k r N M ⟨2, by omega⟩ (show 2 < k - 1 by omega)`. Use `⟨1, by omega, ?_, ⟨⟨0, by omega⟩, c0, ?_⟩, ⟨⟨2, by omega⟩, c2, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hU 1 (by omega), hU (1 + 1) (by omega)]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hU 1 (by omega), l0]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hU (1 + 1) (by omega), l2]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amp_position (k r N M : ℕ) (hk : 4 ≤ k) (hN : 1 ≤ N) (L : ℝ) (hL : L ≤ N) :
    HasSeparatingGap (amp_u k r N (1 / 2)) (amp_lam k r N M) L := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hU : ∀ (i : ℕ) (hi : i < k), amp_u k r N (1 / 2) ⟨i, hi⟩ =
      (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) + 1 / 2 := by
    intro i hi
    simp only [amp_u, ite_self]
  have c0 := (amp_cloud_iff k r N M (1 / 2) (by norm_num) (by linarith) hN ⟨0, by omega⟩).2
    (show 0 < k - 1 by omega)
  have c2 := (amp_cloud_iff k r N M (1 / 2) (by norm_num) (by linarith) hN ⟨2, by omega⟩).2
    (show 2 < k - 1 by omega)
  have l0 := amp_lam_lo k r N M ⟨0, by omega⟩ (show 0 < k - 1 by omega)
  have l2 := amp_lam_lo k r N M ⟨2, by omega⟩ (show 2 < k - 1 by omega)
  refine ⟨1, by omega, ?_, ⟨⟨0, by omega⟩, c0, ?_⟩, ⟨⟨2, by omega⟩, c2, ?_⟩⟩
  · rw [hU 1 (by omega), hU (1 + 1) (by omega)]
    push_cast
    linarith
  · rw [hU 1 (by omega), l0]
    push_cast
    linarith
  · rw [hU (1 + 1) (by omega), l2]
    push_cast
    linarith

/- English proof (translation)
Establish `hN6 : (6 : ℝ) ≤ N` using `by linarith`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - 1)` from `⟨_, rfl⟩`. Establish `e1 : amp_u k r N (1 / 2) ⟨1, by omega⟩ = A + 1 / 2` using `by rw [hA]; simp [amp_u]`. Establish `e2 : amp_u k r N ((N : ℝ) - 1 / 2) ⟨1, by omega⟩ = A + ((N : ℝ) - 1 / 2)`. Rewrite using `[hA]`.

Simplify using `[amp_u]`. Use `⟨fun h => ?_, -A - N + 5 / 2, -A - 5 / 2, ⟨⟨1, by omega⟩, -A - N + 5 / 2, -A - 5 / 2, ?_, ?_, rfl, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrFun h ⟨1, by omega⟩`. Rewrite `h2` using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[e1, e2]`. Introduce `h2`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e1, e2, min_lt_iff] right`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e1, e2, lt_max_iff] left`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `y hy`. Rewrite `hy` using `[Set.mem_Icc]`.

Rewrite using `[e1, e2]`. Conclude with `⟨le_abs.mpr (Or.inr (by linarith)), le_abs.mpr (Or.inl (by linarith))⟩`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amp_cut (k r N : ℕ) (hk : 4 ≤ k) (L : ℝ) (hL0 : 0 ≤ L) (hL : L + 6 ≤ N) :
    amp_u k r N (1 / 2) ≠ amp_u k r N ((N : ℝ) - 1 / 2) ∧
      HasCut (amp_u k r N (1 / 2)) (amp_u k r N ((N : ℝ) - 1 / 2)) L := by
  have hN6 : (6 : ℝ) ≤ N := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - 1) := ⟨_, rfl⟩
  have e1 : amp_u k r N (1 / 2) ⟨1, by omega⟩ = A + 1 / 2 := by rw [hA]; simp [amp_u]
  have e2 : amp_u k r N ((N : ℝ) - 1 / 2) ⟨1, by omega⟩ = A + ((N : ℝ) - 1 / 2) := by
    rw [hA]; simp [amp_u]
  refine ⟨fun h => ?_, -A - N + 5 / 2, -A - 5 / 2,
    ⟨⟨1, by omega⟩, -A - N + 5 / 2, -A - 5 / 2, ?_, ?_, rfl, ?_, ?_, ?_⟩, ?_⟩
  · have h2 := congrFun h ⟨1, by omega⟩
    rw [e1, e2] at h2
    linarith
  · rw [e1, e2]
    intro h2
    linarith
  · linarith
  · rw [e1, e2, min_lt_iff]
    right
    linarith
  · rw [e1, e2, lt_max_iff]
    left
    linarith
  · intro y hy
    rw [Set.mem_Icc] at hy
    rw [e1, e2]
    exact ⟨le_abs.mpr (Or.inr (by linarith)), le_abs.mpr (Or.inl (by linarith))⟩
  · linarith

/- English proof (translation)
Establish `hN : (1 : ℝ) ≤ N` using `by linarith`. Establish `hN0 : (0 : ℝ) ≤ N` using `by linarith`. Establish `hE : ∀ (i : ℕ) (hi : i < k), amp_u k r N δ ⟨i, hi⟩ = (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) + (if i = 1 then δ else 1 / 2)`. Introduce `i hi`. Both sides reduce to the same expression.

Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `a`. Take `⟨b, hb⟩` from `b`. Establish `hab1 : a < b` using `hab`. Establish `hab' : (a : ℝ) + 1 ≤ b` using `by exact_mod_cast (show a + 1 ≤ b by omega)`.

Establish `hp` using `mul_nonneg hN0 (show (0 : ℝ) ≤ (b : ℝ) - a - 1 by linarith)`. Rewrite using `[hE a ha, hE b hb]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | nlinarith`. Take `⟨i, hi⟩` from `a`. Rewrite using `[hE i hi]`.

Use `split_ifs`. Use `⟨(r : ℤ) + (N : ℤ) * ((k : ℤ) - (i : ℤ)) + d + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(r : ℤ) + (N : ℤ) * ((k : ℤ) - (i : ℤ)) + 1, ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem amp_u_hc (k r N : ℕ) (δ : ℝ) (d : ℤ) (h0 : 1 / 2 ≤ δ) (h1 : δ ≤ (N : ℝ) - 1 / 2) (hd : δ = (d : ℝ) + 1 / 2) :
    IsHCParam (amp_u k r N δ) := by
  have hN : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hE : ∀ (i : ℕ) (hi : i < k), amp_u k r N δ ⟨i, hi⟩ =
      (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 + (N : ℝ) * ((k : ℝ) - (i : ℝ)) + (if i = 1 then δ else 1 / 2) := by
    intro i hi
    rfl
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have hab1 : a < b := hab
    have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    have hp := mul_nonneg hN0 (show (0 : ℝ) ≤ (b : ℝ) - a - 1 by linarith)
    rw [hE a ha, hE b hb]
    split_ifs <;> first | (exfalso; omega) | nlinarith
  · obtain ⟨i, hi⟩ := a
    rw [hE i hi]
    split_ifs
    · refine ⟨(r : ℤ) + (N : ℤ) * ((k : ℤ) - (i : ℤ)) + d + 1, ?_⟩
      rw [hd]
      push_cast
      ring
    · refine ⟨(r : ℤ) + (N : ℤ) * ((k : ℤ) - (i : ℤ)) + 1, ?_⟩
      push_cast
      ring

/- English proof (translation)
Take `⟨N, hNX⟩` from `exists_nat_ge (|Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3| + |Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)| + |Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7| + 2 * |Cg * ((r : ℝ) + 1) ^ 2| + 7)`. Establish `a1` using `abs_nonneg (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3)`. Establish `a2` using `abs_nonneg (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3))`. Establish `a3` using `abs_nonneg (Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7)`. Establish `a4` using `abs_nonneg (Cg * ((r : ℝ) + 1) ^ 2)`.

Establish `b1` using `le_abs_self (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3)`. Establish `b2` using `le_abs_self (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3))`. Establish `b3` using `le_abs_self (Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7)`. Establish `b4` using `le_abs_self (Cg * ((r : ℝ) + 1) ^ 2)`. Establish `hN7 : (7 : ℝ) ≤ N` using `by linarith`.

Establish `hN : 1 ≤ N`. Establish `: (1 : ℝ) ≤ N` using `by linarith`. Conclude with `this` after adjusting the coercions. Take `⟨M, hM⟩ : ∃ M : ℕ, M = 9 * (2 * r + k + 1) + 9 * N * (2 * r + k + 1)` from `⟨_, rfl⟩`. Establish `hMr : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)`.

Rewrite using `[hM]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)`. Establish `: 1 ≤ 2 * r + k + 1` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `hN0 : (0 : ℝ) ≤ N` using `by linarith`. Establish `p4 : (N : ℝ) ≤ (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)` using `le_mul_of_one_le_right hN0 hn1`. Establish `hb1 : (1 : ℝ) ≤ 2 * (M : ℝ)` using `by rw [hMr]; linarith`. Establish `hp : ∀ x : ℝ, 0 ≤ x → (1 : ℝ) ≤ (2 * (M : ℝ)) ^ x` using `fun x hx => Real.one_le_rpow hb1 hx`.

Establish `hδ : (0 : ℝ) < (N : ℝ) - 1 / 2 ∧ (N : ℝ) - 1 / 2 < N` using `⟨by linarith, by linarith⟩`. Establish `hh : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < N` using `⟨by norm_num, by linarith⟩`. Establish `hbv : Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ (M : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2`. Rewrite using `[hMr]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgap : GapAtLeast ε (amp_lam k r N M) (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3))`. Introduce `a b hab`. Conclude with `amp_lam_allGaps k r N M _ (by linarith) a b (fun h => hab (by rw [h]))`. Establish `hm0 : (0 : ℝ) ≤ Ch * ((2 * r + 2 : ℕ) : ℝ)` using `mul_nonneg hCh (Nat.cast_nonneg _)`. Take `⟨hne, hcut⟩` from `amp_cut k r N hk |Cg * ((r : ℝ) + 1) ^ 2| a4 (by linarith)`.

Use `⟨amp_lam k r N M, amp_u k r N (1 / 2), amp_u k r N ((N : ℝ) - 1 / 2), 2 * (M : ℝ), amp_u_hc k r N _ 0 le_rfl (by linarith) (by norm_num), amp_u_hc k r N _ ((N : ℤ) - 1) (by linarith) le_rfl (by push_cast; ring), ?_, hne, ?_⟩` and prove the remaining obligations. Conclude with `⟨amp_lam_hc k r N M hN, amp_interlace k r N M _ hh.1 hh.2 hN, amp_interlace k r N M _ hh.1 hh.2 hN, one_pos, hp _ hCh, by rw [inv_one]; exact hp _ hCh, le_rfl, le_rfl, hp _ hm0, hp _ hm0, amp_lam_abs k r N M hN hM, amp_u_abs k r N M _ hh.1 hh.2 hN hM, amp_u_abs k r N M _ hh.1 hh. …`. Take `⟨a, b, hc, hl⟩` from `hcut`. Conclude with `⟨amp_lam_hc k r N M hN, amp_interlace k r N M _ hh.1 hh.2 hN, amp_interlace k r N M _ hδ.1 hδ.2 hN, one_pos, hp _ hCh, by rw [inv_one]; exact hp _ hCh, le_rfl, le_rfl, hp _ hm0, hp _ hm0, amp_lam_abs k r N M hN hM, amp_u_abs k r N M _ hh.1 hh.2 hN hM, amp_u_abs k r N M _ hδ.1 hδ. …`.
-/
theorem amp_stdHyp_sat (Ch Cg : ℝ) (hCh : 0 ≤ Ch) (k r : ℕ) (hk : 4 ≤ k) (ε : Fin (2 * r + k + 1) → Bool) :
    ∃ (lam : Fin (2 * r + k + 1) → ℝ) (u u' : Fin k → ℝ) (b : ℝ),
      IsHCParam u ∧ IsHCParam u' ∧
      StdHyp Ch Cg k r ε lam u u 1 1 1 b ∧ u ≠ u' ∧ StdHyp Ch Cg k r ε lam u u' 1 1 1 b := by
  obtain ⟨N, hNX⟩ := exists_nat_ge (|Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3| +
    |Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)| +
    |Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7| + 2 * |Cg * ((r : ℝ) + 1) ^ 2| + 7)
  have a1 := abs_nonneg (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3)
  have a2 := abs_nonneg (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3))
  have a3 := abs_nonneg (Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7)
  have a4 := abs_nonneg (Cg * ((r : ℝ) + 1) ^ 2)
  have b1 := le_abs_self (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3)
  have b2 := le_abs_self (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3))
  have b3 := le_abs_self (Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7)
  have b4 := le_abs_self (Cg * ((r : ℝ) + 1) ^ 2)
  have hN7 : (7 : ℝ) ≤ N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 9 * (2 * r + k + 1) + 9 * N * (2 * r + k + 1) := ⟨_, rfl⟩
  have hMr : (M : ℝ) = 9 * ((2 * r + k + 1 : ℕ) : ℝ) + 9 * (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    rw [hM]; push_cast; ring
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have p4 : (N : ℝ) ≤ (N : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := le_mul_of_one_le_right hN0 hn1
  have hb1 : (1 : ℝ) ≤ 2 * (M : ℝ) := by rw [hMr]; linarith
  have hp : ∀ x : ℝ, 0 ≤ x → (1 : ℝ) ≤ (2 * (M : ℝ)) ^ x := fun x hx => Real.one_le_rpow hb1 hx
  have hδ : (0 : ℝ) < (N : ℝ) - 1 / 2 ∧ (N : ℝ) - 1 / 2 < N := ⟨by linarith, by linarith⟩
  have hh : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < N := ⟨by norm_num, by linarith⟩
  have hbv : Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ (M : ℝ) - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 := by
    rw [hMr]; linarith
  have hgap : GapAtLeast ε (amp_lam k r N M) (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
    intro a b hab
    exact amp_lam_allGaps k r N M _ (by linarith) a b (fun h => hab (by rw [h]))
  have hm0 : (0 : ℝ) ≤ Ch * ((2 * r + 2 : ℕ) : ℝ) := mul_nonneg hCh (Nat.cast_nonneg _)
  obtain ⟨hne, hcut⟩ := amp_cut k r N hk |Cg * ((r : ℝ) + 1) ^ 2| a4 (by linarith)
  refine ⟨amp_lam k r N M, amp_u k r N (1 / 2), amp_u k r N ((N : ℝ) - 1 / 2), 2 * (M : ℝ),
    amp_u_hc k r N _ 0 le_rfl (by linarith) (by norm_num),
    amp_u_hc k r N _ ((N : ℤ) - 1) (by linarith) le_rfl (by push_cast; ring), ?_, hne, ?_⟩
  · exact ⟨amp_lam_hc k r N M hN, amp_interlace k r N M _ hh.1 hh.2 hN, amp_interlace k r N M _ hh.1 hh.2 hN,
      one_pos, hp _ hCh, by rw [inv_one]; exact hp _ hCh, le_rfl, le_rfl, hp _ hm0, hp _ hm0,
      amp_lam_abs k r N M hN hM, amp_u_abs k r N M _ hh.1 hh.2 hN hM, amp_u_abs k r N M _ hh.1 hh.2 hN hM,
      amp_lam_allGaps k r N M _ (by linarith), hgap, ⟨_, hbv, amp_shape k r N M _ hh.1 hh.2 hN hM⟩,
      Or.inl ⟨rfl, amp_position k r N M hk hN _ (by linarith)⟩⟩
  · obtain ⟨a, b, hc, hl⟩ := hcut
    exact ⟨amp_lam_hc k r N M hN, amp_interlace k r N M _ hh.1 hh.2 hN, amp_interlace k r N M _ hδ.1 hδ.2 hN,
      one_pos, hp _ hCh, by rw [inv_one]; exact hp _ hCh, le_rfl, le_rfl, hp _ hm0, hp _ hm0,
      amp_lam_abs k r N M hN hM, amp_u_abs k r N M _ hh.1 hh.2 hN hM, amp_u_abs k r N M _ hδ.1 hδ.2 hN hM,
      amp_lam_allGaps k r N M _ (by linarith), hgap, ⟨_, hbv, amp_shape k r N M _ hh.1 hh.2 hN hM⟩,
      Or.inr ⟨hne, a, b, hc, le_trans b4 hl⟩⟩

def amp_HType (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) : Prop :=
  ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)), IsHCTypeW k r z u π

def amp_HDS (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsDSHpk k r ε lam σ

def amp_HHaarW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∃ μ : Measure (Mt k r), IsHaarOn (UWset k r z) μ ∧ μ Set.univ = 1

def amp_HHaarG (k r : ℕ) : Prop := ∃ μ : Measure (Mt k r), IsHaarOn (UH (Hpk k r)) μ

def amp_HQuot (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ (μG μW : Measure (Mt k r)) (κ : ℝ≥0∞), IsHaarOn (UH (Hpk k r)) μG → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 →
    0 < κ → κ ≠ ⊤ → ∃ ν : Measure (Mt k r), IsQuotMeas μG (muS μW (haarLie (Nset k r) κ)) ν

/- English proof (translation)
Take `⟨Hs, i1, i2, i3, σ, hσ1⟩` from `hσ`. Take `⟨Wp, j1, j2, j3, π, hπ1⟩` from `hπ`. Take `⟨Wq, l1, l2, l3, π', hπ2⟩` from `hπ'`. Take `⟨μW, hμW⟩` from `hW`. Take `⟨μW', hμW'⟩` from `hW'`.

Conclude with `⟨{ ε := ε, lam := lam, hlam := hlam, z := z, z' := z', hz := hz, hz' := hz', u := u, u' := u', Hs := Hs, hsN := i1, hsI := i2, hsC := i3, σ := σ, hσ := hσ1, Wp := Wp, wpN := j1, wpI := j2, wpF := j3, π := π, hπ := hπ1, Wq := Wq, wqN := l1, wqI := l2, wqF := l3, π' := π', hπ' := h …`.
-/
theorem amp_locBessel_exists_of {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (u u' : Fin k → ℝ) (c : ℂ) (κN : ℝ≥0∞) (hlam : IsHCParam lam)
    (hz : inWb k r z ∧ 0 < Tz k r z) (hz' : inWb k r z' ∧ 0 < Tz k r z')
    (hσ : amp_HDS k r ε lam) (hπ : amp_HType k r z u) (hπ' : amp_HType k r z' u')
    (hW : amp_HHaarW k r z) (hW' : amp_HHaarW k r z') :
    ∃ L : LocBessel k r, L.ε = ε ∧ L.lam = lam ∧ L.z = z ∧ L.z' = z' ∧ L.u = u ∧ L.u' = u' ∧ L.c = c ∧ L.κN = κN := by
  obtain ⟨Hs, i1, i2, i3, σ, hσ1⟩ := hσ
  obtain ⟨Wp, j1, j2, j3, π, hπ1⟩ := hπ
  obtain ⟨Wq, l1, l2, l3, π', hπ2⟩ := hπ'
  obtain ⟨μW, hμW⟩ := hW
  obtain ⟨μW', hμW'⟩ := hW'
  exact ⟨{ ε := ε, lam := lam, hlam := hlam, z := z, z' := z', hz := hz, hz' := hz', u := u, u' := u', Hs := Hs, hsN := i1, hsI := i2, hsC := i3, σ := σ, hσ := hσ1, Wp := Wp, wpN := j1, wpI := j2, wpF := j3, π := π, hπ := hπ1, Wq := Wq, wqN := l1, wqI := l2, wqF := l3, π' := π', hπ' := hπ2, c := c, μW := μW, μW' := μW', hμW := hμW, hμW' := hμW', κN := κN }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- English proof (translation)
Take `⟨L, -⟩` from `amp_locBessel_exists_of ε lam z z u u 0 0 hlam hz hz hσ hπ hπ hW hW`. Conclude with `⟨L⟩`.
-/
theorem amp_locBessel_nonempty_of {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (hlam : IsHCParam lam) (hz : inWb k r z ∧ 0 < Tz k r z)
    (hσ : amp_HDS k r ε lam) (hπ : amp_HType k r z u) (hW : amp_HHaarW k r z) : Nonempty (LocBessel k r) := by
  obtain ⟨L, -⟩ := amp_locBessel_exists_of ε lam z z u u 0 0 hlam hz hz hσ hπ hπ hW hW
  exact ⟨L⟩

/- English proof (translation)
Conclude with `⟨⟨L.Hs, L.hsN, L.hsI, L.hsC, L.σ, L.hσ⟩, ⟨L.Wp, L.wpN, L.wpI, L.wpF, L.π, L.hπ⟩, ⟨L.Wq, L.wqN, L.wqI, L.wqF, L.π', L.hπ'⟩, ⟨L.μW, L.hμW⟩, ⟨L.μW', L.hμW'⟩⟩`.
-/
theorem amp_hDS_of_locBessel {k r : ℕ} (L : LocBessel k r) :
    amp_HDS k r L.ε L.lam ∧ amp_HType k r L.z L.u ∧ amp_HType k r L.z' L.u' ∧ amp_HHaarW k r L.z ∧ amp_HHaarW k r L.z' := by
  exact ⟨⟨L.Hs, L.hsN, L.hsI, L.hsC, L.σ, L.hσ⟩, ⟨L.Wp, L.wpN, L.wpI, L.wpF, L.π, L.hπ⟩,
    ⟨L.Wq, L.wqN, L.wqI, L.wqF, L.π', L.hπ'⟩, ⟨L.μW, L.hμW⟩, ⟨L.μW', L.hμW'⟩⟩

/- English proof (translation)
Establish `hk1 : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Take `⟨L, hLε, hLlam, hLz, hLz', hLu, hLu', hLc, hLκ⟩` from `amp_locBessel_exists_of (epsSH D.R) lam z z' u u' (cOfDpsi ((κ : ℝ) : ℂ)) 1 hlam hz hz' hσ hπ hπ' hW hW'`. Use `⟨L, ⟨hk1, hLε, hLc, ?_, ?_, ?_, ?_, ?_⟩, hLlam, hLz, hLz'⟩` and prove the remaining obligations. Rewrite using `[hLκ]`. Conclude with `one_pos`.

Rewrite using `[hLκ]`. Conclude with `ENNReal.one_ne_top`. Rewrite using `[hLε, hLu, hLu', hLz, hLz']`. Conclude with `hStd`. Rewrite using `[hLz]`.

Conclude with `h1`. Rewrite using `[hLz']`. Conclude with `h2`.
-/
theorem amp_locOk_exists_of (D : D7) (Ch Cg : ℝ) (lam lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u u' : Fin D.R.k → ℝ) (ka b κ : ℝ) (hlam : IsHCParam lam)
    (hz : inWb D.R.k D.R.rS z ∧ 0 < Tz D.R.k D.R.rS z) (hz' : inWb D.R.k D.R.rS z' ∧ 0 < Tz D.R.k D.R.rS z')
    (hσ : amp_HDS D.R.k D.R.rS (epsSH D.R) lam) (hπ : amp_HType D.R.k D.R.rS z u) (hπ' : amp_HType D.R.k D.R.rS z' u')
    (hW : amp_HHaarW D.R.k D.R.rS z) (hW' : amp_HHaarW D.R.k D.R.rS z')
    (hStd : StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) lam0 u u' (Tz D.R.k D.R.rS z * (κ / ka) ^ (2 * D.R.rS))
      (Tz D.R.k D.R.rS z' * (κ / ka) ^ (2 * D.R.rS)) ka b)
    (h1 : 1 ≤ Tz D.R.k D.R.rS z * κ ^ (2 * D.R.rS)) (h2 : 1 ≤ Tz D.R.k D.R.rS z' * κ ^ (2 * D.R.rS)) :
    ∃ L : LocBessel D.R.k D.R.rS, LocOk D Ch Cg L lam0 ka b κ ∧ L.lam = lam ∧ L.z = z ∧ L.z' = z' := by
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨L, hLε, hLlam, hLz, hLz', hLu, hLu', hLc, hLκ⟩ := amp_locBessel_exists_of (epsSH D.R) lam z z' u u'
    (cOfDpsi ((κ : ℝ) : ℂ)) 1 hlam hz hz' hσ hπ hπ' hW hW'
  refine ⟨L, ⟨hk1, hLε, hLc, ?_, ?_, ?_, ?_, ?_⟩, hLlam, hLz, hLz'⟩
  · rw [hLκ]; exact one_pos
  · rw [hLκ]; exact ENNReal.one_ne_top
  · rw [hLε, hLu, hLu', hLz, hLz']; exact hStd
  · rw [hLz]; exact h1
  · rw [hLz']; exact h2

/- English proof (translation)
Use `⟨0, 0, fun w => ?_, fun x => ?_, fun g => ?_⟩` and prove the remaining obligations. Conclude with `⟨⊥, inferInstance, by simp, fun g _ x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩`. Conclude with `⟨⊥, inferInstance, by simp, fun g _ x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩`. Simplify using the standard rewrite rules.
-/
theorem amp_isKFinCoefH_zero {k r : ℕ} (L : LocBessel k r) :
    IsKFinCoefH (k := k) (r := r) L.σ (fun _ => (0 : L.Wq →L[ℂ] L.Wp)) := by
  refine ⟨0, 0, fun w => ?_, fun x => ?_, fun g => ?_⟩
  · exact ⟨⊥, inferInstance, by simp, fun g _ x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩
  · exact ⟨⊥, inferInstance, by simp, fun g _ x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩
  · simp

/- English proof (translation)
Use `choose L hL using h`. Use `choose μsec hμ using fun v => (hL v).2.2.2`. Conclude with `⟨{ L := L, f := fun v _ => 0, μsec := μsec, hL := fun v => (hL v).1, hnear := fun v => (hL v).2.1, hcoef := fun v => amp_isKFinCoefH_zero (L v), hsec := hμ, hT := fun v => (hL v).2.2.1 }⟩`.
-/
theorem amp_bData_nonempty_of (D : D7) (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ)
    (h : ∀ v : D.what₂.Tau, ∃ L : LocBessel D.R.k D.R.rS,
      LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D) ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
      (Tz D.R.k D.R.rS L.z = T ∧ Tz D.R.k D.R.rS L.z' = T') ∧
      ∃ μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ, IsSection D.R.k D.R.rS L.z L.z' μsec) :
    Nonempty (BData D Ch Cg T T' b dist) := by
  choose L hL using h
  choose μsec hμ using fun v => (hL v).2.2.2
  exact ⟨{ L := L, f := fun v _ => 0, μsec := μsec, hL := fun v => (hL v).1, hnear := fun v => (hL v).2.1, hcoef := fun v => amp_isKFinCoefH_zero (L v), hsec := hμ, hT := fun v => (hL v).2.2.1 }⟩

/- English proof (translation)
Unfold `Host.v Host.rdE`. Apply `div_pos ?_ two_pos` to reduce the goal to its premises. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Rewrite using `[abs_pos]`. Conclude with `NumberField.discr_ne_zero _` after adjusting the coercions.
-/
theorem amp_v_pos (D : D7) : 0 < D.host.v := by
  unfold Host.v Host.rdE
  apply div_pos ?_ two_pos
  apply Real.rpow_pos_of_pos
  rw [abs_pos]
  exact_mod_cast NumberField.discr_ne_zero _

/- English proof (translation)
Establish `hv` using `amp_v_pos D`. Use `⟨?_, ENNReal.ofReal_ne_top⟩` and prove the remaining obligations. Unfold `kapN`. Rewrite using `[ENNReal.ofReal_pos]`. Conclude with `mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ`.
-/
theorem amp_kapN_pos (D : D7) (θ : ℝ) (hθ : 0 < θ) : 0 < kapN D θ ∧ kapN D θ ≠ ⊤ := by
  have hv := amp_v_pos D
  refine ⟨?_, ENNReal.ofReal_ne_top⟩
  unfold kapN
  rw [ENNReal.ofReal_pos]
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ

/- English proof (translation)
Take `⟨z, hzW, hzT⟩` from `amp_z_exists D.R.k D.R.rS (Tr D w) hT.le`. Take `⟨z', hzW', hzT'⟩` from `amp_z_exists D.R.k D.R.rS (Tr D w') hT'.le`. Establish `hz0 : 0 < Tz D.R.k D.R.rS z` using `by rw [hzT]; exact hT`. Establish `hz0' : 0 < Tz D.R.k D.R.rS z'` using `by rw [hzT']; exact hT'`. Take `⟨Wp, i1, i2, i3, π, hπ1⟩` from `hπ z hzW hz0`.

Take `⟨Wq, j1, j2, j3, π', hπ2⟩` from `hπ' z' hzW' hz0'`. Take `⟨μW, hμW, hμW1⟩` from `hW z hzW hz0`. Take `⟨μW', hμW', hμW1'⟩` from `hW z' hzW' hz0'`. Take `⟨μG, hμG⟩` from `hG`. Establish `hk` using `amp_kapN_pos D θ hθ`.

Take `⟨νS, hνS⟩` from `hQ z hzW hz0 μG μW (kapN D θ) hμG hμW hμW1 hk.1 hk.2`. Take `⟨νS', hνS'⟩` from `hQ z' hzW' hz0' μG μW' (kapN D θ) hμG hμW' hμW1' hk.1 hk.2`. Conclude with `⟨{ Wp := Wp, p1 := i1, p2 := i2, p3 := i3, Wq := Wq, q1 := j1, q2 := j2, q3 := j3, π := π, π' := π', z := z, z' := z', μG := μG, μW := μW, μW' := μW', μN := haarLie (Nset D.R.k D.R.rS) (kapN D θ), νS := νS, νS' := νS' }, hπ1, hπ2, hzW, hzW', hzT, hzT', hμG, hμW, hμW1, hμW', hμW1' …`.
-/
theorem amp_goodW_exists_of (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (hθ : 0 < θ)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w')
    (hπ : ∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HType D.R.k D.R.rS z (uS D w τ))
    (hπ' : ∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HType D.R.k D.R.rS z (uS D w' τ))
    (hW : ∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HHaarW D.R.k D.R.rS z)
    (hG : amp_HHaarG D.R.k D.R.rS)
    (hQ : ∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HQuot D.R.k D.R.rS z) :
    ∃ W : LocW D.R.k D.R.rS, GoodW D τ w w' θ W := by
  obtain ⟨z, hzW, hzT⟩ := amp_z_exists D.R.k D.R.rS (Tr D w) hT.le
  obtain ⟨z', hzW', hzT'⟩ := amp_z_exists D.R.k D.R.rS (Tr D w') hT'.le
  have hz0 : 0 < Tz D.R.k D.R.rS z := by rw [hzT]; exact hT
  have hz0' : 0 < Tz D.R.k D.R.rS z' := by rw [hzT']; exact hT'
  obtain ⟨Wp, i1, i2, i3, π, hπ1⟩ := hπ z hzW hz0
  obtain ⟨Wq, j1, j2, j3, π', hπ2⟩ := hπ' z' hzW' hz0'
  obtain ⟨μW, hμW, hμW1⟩ := hW z hzW hz0
  obtain ⟨μW', hμW', hμW1'⟩ := hW z' hzW' hz0'
  obtain ⟨μG, hμG⟩ := hG
  have hk := amp_kapN_pos D θ hθ
  obtain ⟨νS, hνS⟩ := hQ z hzW hz0 μG μW (kapN D θ) hμG hμW hμW1 hk.1 hk.2
  obtain ⟨νS', hνS'⟩ := hQ z' hzW' hz0' μG μW' (kapN D θ) hμG hμW' hμW1' hk.1 hk.2
  exact ⟨{ Wp := Wp, p1 := i1, p2 := i2, p3 := i3, Wq := Wq, q1 := j1, q2 := j2, q3 := j3, π := π, π' := π', z := z, z' := z', μG := μG, μW := μW, μW' := μW', μN := haarLie (Nset D.R.k D.R.rS) (kapN D θ), νS := νS, νS' := νS' }, hπ1, hπ2, hzW, hzW', hzT, hzT', hμG, hμW, hμW1, hμW', hμW1', rfl, hνS, hνS'⟩

def amp_HAmp (D : D7) (large₂ : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∃ (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (A : LocS W) (γ : MatKR D.R.k D.R.rS)
    (p : Point ℂ (D.R.rS + 1)) (θ' : ℝ) (νR : Measure (Mt D.R.k D.R.rS)),
    HypTT D w w' ∧ normWin D large₂ C1 θ ∧ GoodW D τ w w' θ W ∧ GoodS D (lamD D τ) A ∧ A.deg = D.dsig τ ∧
      RelPt D W.z W.z' γ p ∧ normWin D large₂ C1 θ' ∧ RMeas D W γ θ' νR

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨τ, w, w', θ, W, A, γ, p, θ', νR, h1, h2, h3, h4, h5, h6, h7, h8⟩`. Conclude with `h τ w w' h1 θ h2 W h3 A h4 h5 γ p h6 θ' h7 νR h8`. Introduce `h τ w w' h1 θ h2 W h3 A h4 h5 γ p h6 θ' h7 νR h8`. Conclude with `h ⟨τ, w, w', θ, W, A, γ, p, θ', νR, h1, h2, h3, h4, h5, h6, h7, h8⟩`.
-/
theorem amp_forAmp_false_iff (D : D7) (large₂ : SizeData₂ D) (C1 : ℝ) :
    ForAmp D large₂ C1 (fun _ _ _ _ _ _ _ _ => False) ↔ ¬ amp_HAmp D large₂ C1 := by
  constructor
  · rintro h ⟨τ, w, w', θ, W, A, γ, p, θ', νR, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact h τ w w' h1 θ h2 W h3 A h4 h5 γ p h6 θ' h7 νR h8
  · intro h τ w w' h1 θ h2 W h3 A h4 h5 γ p h6 θ' h7 νR h8
    exact h ⟨τ, w, w', θ, W, A, γ, p, θ', νR, h1, h2, h3, h4, h5, h6, h7, h8⟩

/- English proof (translation)
Establish `h1N : (1 : MatKR D.R.k D.R.rS) ∈ Nset D.R.k D.R.rS`. Use `⟨?_, fun a i _ => Matrix.one_apply, fun i j _ _ _ => Matrix.one_apply⟩` and prove the remaining obligations. Use `show (1 : MatKR D.R.k D.R.rS)ᴴ * Hpk D.R.k D.R.rS * 1 = Hpk D.R.k D.R.rS`. Simplify using the standard rewrite rules. Establish `hof : Matrix.of (fun i j => (1 : MatKR D.R.k D.R.rS) i j) = 1` using `rfl`.

Establish `hR : Matrix.of (fun i j => (1 : MatKR D.R.k D.R.rS) i j) ∈ Rset D.R.k D.R.rS γ`. Rewrite using `[hof]`. Use `⟨h1N, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_one, hγ]`. Conclude with `h1N`.

Use `haveI : IsEmpty (rootPat p) := Finset.isEmpty_coe_sort.mpr hp`. Establish `hcard : (rootPat p).card = 0` using `by rw [hp]; rfl`. Establish `hmap : (Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j)).map (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j)`. Establish `hid : (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id`. Use function extensionality and compare the values at `x i j`.

Simplify using the standard rewrite rules. Rewrite using `[hid, Measure.map_id]`. Establish `hvol : ∀ x : Mt D.R.k D.R.rS, (Measure.dirac x).map (rootCoords D.R.k D.R.rS W.z' p) = volume`. Introduce `x`. Use extensionality with `s hs`.

Break down `s.eq_empty_or_nonempty with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[h.eq_univ, Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]`. Simplify using `[MeasureTheory.volume_pi]`.

Use `⟨p, (Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j)).map (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j), ⟨1, h1N, 1, h1N, γ, by simp, hZ, Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j), ?_, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.dirac_apply]`. Simplify using `[Set.indicator, hR]`. Rewrite using `[hcard, pow_zero, ENNReal.ofReal_one, one_smul]`. Conclude with `hvol _`.

Introduce `f hf`. Establish `hc0 : ENNReal.ofReal θ' ≠ 0` using `(ENNReal.ofReal_pos.mpr hθ).ne'`. Establish `hct : ENNReal.ofReal θ' ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hx : ∀ x : Mt D.R.k D.R.rS, (fun i j => (Matrix.of (fun i j => (1 : MatKR D.R.k D.R.rS) i j) * Matrix.of x) i j) = x`. Introduce `x`.

Use function extensionality and compare the values at `i j`. Use `show ((1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) * Matrix.of x) i j = x i j`. Simplify using the standard rewrite rules. Rewrite using `[hmap]`. Simplify using `only [lintegral_smul_measure, lintegral_dirac, hx, smul_eq_mul]`.

Rewrite using `[lintegral_const_mul' _ _ hct, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]`.
-/
theorem amp_rMeas_open (D : D7) (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1))
    (hγ : γ * γ⁻¹ = 1) (hZ : ZhatO D.R.k D.R.rS W.z W.z' γ = ptMat p) (hp : rootPat p = ∅) (θ' : ℝ) (hθ : 0 < θ') :
    RMeas D W γ θ' ((ENNReal.ofReal θ')⁻¹ • W.μG) := by
  have h1N : (1 : MatKR D.R.k D.R.rS) ∈ Nset D.R.k D.R.rS := by
    refine ⟨?_, fun a i _ => Matrix.one_apply, fun i j _ _ _ => Matrix.one_apply⟩
    show (1 : MatKR D.R.k D.R.rS)ᴴ * Hpk D.R.k D.R.rS * 1 = Hpk D.R.k D.R.rS
    simp
  have hof : Matrix.of (fun i j => (1 : MatKR D.R.k D.R.rS) i j) = 1 := rfl
  have hR : Matrix.of (fun i j => (1 : MatKR D.R.k D.R.rS) i j) ∈ Rset D.R.k D.R.rS γ := by
    rw [hof]
    refine ⟨h1N, ?_⟩
    rw [mul_one, hγ]
    exact h1N
  haveI : IsEmpty (rootPat p) := Finset.isEmpty_coe_sort.mpr hp
  have hcard : (rootPat p).card = 0 := by rw [hp]; rfl
  have hmap : (Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j)).map
      (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) =
      Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j) := by
    have hid : (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id := by
      funext x i j
      simp
    rw [hid, Measure.map_id]
  have hvol : ∀ x : Mt D.R.k D.R.rS, (Measure.dirac x).map (rootCoords D.R.k D.R.rS W.z' p) = volume := by
    intro x
    ext s hs
    rcases s.eq_empty_or_nonempty with h | h
    · subst h
      simp
    · rw [h.eq_univ, Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]
      simp [MeasureTheory.volume_pi]
  refine ⟨p, (Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j)).map
      (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j),
    ⟨1, h1N, 1, h1N, γ, by simp, hZ, Measure.dirac (fun i j => (1 : MatKR D.R.k D.R.rS) i j), ?_, ?_, rfl⟩, ?_⟩
  · rw [Measure.dirac_apply]
    simp [Set.indicator, hR]
  · rw [hcard, pow_zero, ENNReal.ofReal_one, one_smul]
    exact hvol _
  · intro f hf
    have hc0 : ENNReal.ofReal θ' ≠ 0 := (ENNReal.ofReal_pos.mpr hθ).ne'
    have hct : ENNReal.ofReal θ' ≠ ⊤ := ENNReal.ofReal_ne_top
    have hx : ∀ x : Mt D.R.k D.R.rS,
        (fun i j => (Matrix.of (fun i j => (1 : MatKR D.R.k D.R.rS) i j) * Matrix.of x) i j) = x := by
      intro x
      funext i j
      show ((1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) * Matrix.of x) i j = x i j
      simp
    rw [hmap]
    simp only [lintegral_smul_measure, lintegral_dirac, hx, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hct, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/- English proof (translation)
Use `⟨{ Sm := ∅, Hs := fun _ => ℂ, σs := fun _ _ => 0, ds := fun s hs => by simp at hs, inequiv := fun s hs => by simp at hs, toSum := fun v w x y _ _ => ⟨Empty, inferInstance, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun g _ => ?_⟩, …` and prove the remaining obligations. Rewrite using `[Subsingleton.elim w 0]`. Simplify using the standard rewrite rules.
-/
theorem amp_tensorDS_nonempty_of_subsingleton (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Subsingleton H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Nonempty (TensorDS n ε μ H σ) := by
  refine ⟨{ Sm := ∅, Hs := fun _ => ℂ, σs := fun _ _ => 0, ds := fun s hs => by simp at hs, inequiv := fun s hs => by simp at hs, toSum := fun v w x y _ _ => ⟨Empty, inferInstance, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun g _ => ?_⟩, ofSum := fun s hs => by simp at hs }⟩
  rw [Subsingleton.elim w 0]
  simp

/- English proof (translation)
Take `⟨ι, hι, sI, vI, wI, hS1, hS2⟩` from `X.toSum v v (Pi.single i 1) (Pi.single i 1) hK hK`. Assume the negation of the conclusion as `hne`. Establish `hE : IsEmpty ι` using `⟨fun j => hne ⟨sI j, (hS1 j).1⟩⟩`. Establish `h3` using `hS2 1 hJ`. Rewrite `h3` using `[h1]`.

Simplify using `[hv] at h3`.
-/
theorem amp_tensorDS_Sm_nonempty (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (X : TensorDS n ε μ H σ) (i : Fin n) (v : H) (hv : v ≠ 0) (hK : IsKFin ε σ v) (h1 : σ 1 = 1)
    (hJ : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε) : X.Sm.Nonempty := by
  obtain ⟨ι, hι, sI, vI, wI, hS1, hS2⟩ := X.toSum v v (Pi.single i 1) (Pi.single i 1) hK hK
  by_contra hne
  have hE : IsEmpty ι := ⟨fun j => hne ⟨sI j, (hS1 j).1⟩⟩
  have h3 := hS2 1 hJ
  rw [h1] at h3
  simp [hv] at h3

def amp_HRepD (D : D7) : Prop :=
  (∀ lam, IsHCParam lam → amp_HDS D.R.k D.R.rS (epsSH D.R) lam) ∧
  (∀ z u, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → IsHCParam u → amp_HType D.R.k D.R.rS z u) ∧
  (∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HHaarW D.R.k D.R.rS z)

/- English proof (translation)
Establish `hk : 4 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Take `⟨lam, u, u', b, hu, hu', hS1, hne, hS2⟩` from `amp_stdHyp_sat Ch Cg hCh D.R.k D.R.rS hk (epsSH D.R)`. Take `⟨z, hzW, hzT⟩` from `amp_z_exists D.R.k D.R.rS 1 zero_le_one`. Establish `hz0 : 0 < Tz D.R.k D.R.rS z` using `by rw [hzT]; exact one_pos`. Establish `hlam : IsHCParam lam` using `hS1.1`.

Establish `hk1 : 1 ≤ D.R.k` using `by omega`. Establish `mk : ∀ v : Fin D.R.k → ℝ, IsHCParam v → StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) lam u v 1 1 1 b → ∃ L : LocBessel D.R.k D.R.rS, LocOk D Ch Cg L L.lam 1 b 1 ∧ L.u = u ∧ L.u' = v`. Introduce `v hv hSv`. Take `⟨L, hLε, hLlam, hLz, hLz', hLu, hLu', hLc, hLκ⟩` from `amp_locBessel_exists_of (epsSH D.R) lam z z u v (cOfDpsi ((1 : ℝ) : ℂ)) 1 hlam ⟨hzW, hz0⟩ ⟨hzW, hz0⟩ (H.1 lam hlam) (H.2.1 z u hzW hz0 hu) (H.2.1 z v hzW hz0 hv) (H.2.2 z hzW hz0) (H.2.2 z hzW hz0)`. Use `⟨L, ⟨hk1, hLε, hLc, ?_, ?_, ?_, ?_, ?_⟩, hLu, hLu'⟩` and prove the remaining obligations.

Rewrite using `[hLκ]`. Conclude with `one_pos`. Rewrite using `[hLκ]`. Conclude with `ENNReal.one_ne_top`. Rewrite using `[hLlam, hLu, hLu', hLz, hLz', hLε, hzT]`.

Simplify using `using hSv`. Rewrite using `[hLz, hzT]`. Simplify using the standard rewrite rules. Rewrite using `[hLz', hzT]`. Simplify using the standard rewrite rules.

Take `⟨L1, h1, h1u, h1u'⟩` from `mk u hu hS1`. Take `⟨L2, h2, h2u, h2u'⟩` from `mk u' hu' hS2`. Conclude with `⟨⟨L1, b, h1, by rw [h1u, h1u']⟩, ⟨L2, b, h2, by rw [h2u, h2u']; exact hne⟩⟩`.
-/
theorem amp_locOk_nonempty (D : D7) (Ch Cg : ℝ) (hCh : 0 ≤ Ch) (H : amp_HRepD D) :
    (∃ (L : LocBessel D.R.k D.R.rS) (b : ℝ), LocOk D Ch Cg L L.lam 1 b 1 ∧ L.u = L.u') ∧
    (∃ (L : LocBessel D.R.k D.R.rS) (b : ℝ), LocOk D Ch Cg L L.lam 1 b 1 ∧ L.u ≠ L.u') := by
  have hk : 4 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  obtain ⟨lam, u, u', b, hu, hu', hS1, hne, hS2⟩ := amp_stdHyp_sat Ch Cg hCh D.R.k D.R.rS hk (epsSH D.R)
  obtain ⟨z, hzW, hzT⟩ := amp_z_exists D.R.k D.R.rS 1 zero_le_one
  have hz0 : 0 < Tz D.R.k D.R.rS z := by rw [hzT]; exact one_pos
  have hlam : IsHCParam lam := hS1.1
  have hk1 : 1 ≤ D.R.k := by omega
  have mk : ∀ v : Fin D.R.k → ℝ, IsHCParam v → StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) lam u v 1 1 1 b →
      ∃ L : LocBessel D.R.k D.R.rS, LocOk D Ch Cg L L.lam 1 b 1 ∧ L.u = u ∧ L.u' = v := by
    intro v hv hSv
    obtain ⟨L, hLε, hLlam, hLz, hLz', hLu, hLu', hLc, hLκ⟩ := amp_locBessel_exists_of (epsSH D.R) lam z z u v
      (cOfDpsi ((1 : ℝ) : ℂ)) 1 hlam ⟨hzW, hz0⟩ ⟨hzW, hz0⟩ (H.1 lam hlam) (H.2.1 z u hzW hz0 hu)
      (H.2.1 z v hzW hz0 hv) (H.2.2 z hzW hz0) (H.2.2 z hzW hz0)
    refine ⟨L, ⟨hk1, hLε, hLc, ?_, ?_, ?_, ?_, ?_⟩, hLu, hLu'⟩
    · rw [hLκ]; exact one_pos
    · rw [hLκ]; exact ENNReal.one_ne_top
    · rw [hLlam, hLu, hLu', hLz, hLz', hLε, hzT]; simpa using hSv
    · rw [hLz, hzT]; simp
    · rw [hLz', hzT]; simp
  obtain ⟨L1, h1, h1u, h1u'⟩ := mk u hu hS1
  obtain ⟨L2, h2, h2u, h2u'⟩ := mk u' hu' hS2
  exact ⟨⟨L1, b, h1, by rw [h1u, h1u']⟩, ⟨L2, b, h2, by rw [h2u, h2u']; exact hne⟩⟩

def amp_HNumB (D : D7) (Ch Cg : ℝ) (T T' : ℕ) (b : ℝ) (u u' : D.what₂.Tau → Fin D.R.k → ℝ) : Prop :=
  (∀ v, IsHCParam (u v) ∧ IsHCParam (u' v) ∧
    StdHyp Ch Cg D.R.k D.R.rS (epsSH D.R) (lamSH D.R (D.hc v)) (u v) (u' v) T T' (kaRe D) b) ∧
  1 ≤ (T : ℝ) * kaRe D ^ (2 * D.R.rS) ∧ 1 ≤ (T' : ℝ) * kaRe D ^ (2 * D.R.rS)

/- English proof (translation)
Take `⟨hN, hT1, hT2⟩` from `hN`. Establish `hk1 : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hTpos : ∀ n : ℕ, 1 ≤ (n : ℝ) * kaRe D ^ (2 * D.R.rS) → 0 < (n : ℝ)`. Introduce `n hn`. Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases.

Substitute `h` using the available equality. Evaluate the numerical expressions using `at hn`. Conclude with `h` after adjusting the coercions. Establish `hTp` using `hTpos T hT1`. Establish `hTp'` using `hTpos T' hT2`.

Take `⟨z, hzW, hzT⟩` from `amp_z_exists D.R.k D.R.rS T hTp.le`. Take `⟨z', hzW', hzT'⟩` from `amp_z_exists D.R.k D.R.rS T' hTp'.le`. Establish `hz0 : 0 < Tz D.R.k D.R.rS z` using `by rw [hzT]; exact hTp`. Establish `hz0' : 0 < Tz D.R.k D.R.rS z'` using `by rw [hzT']; exact hTp'`. Take `⟨μsec, hsec⟩` from `hS D.R.k D.R.rS z z' hk1 hzW hzW' hz0 hz0'`.

Apply `amp_bData_nonempty_of` to reduce the goal to its premises. Introduce `v`. Take `⟨hu, hu', hSv⟩` from `hN v`. Establish `hka : 0 < kaRe D` using `hSv.2.2.2.1`. Establish `hlam` using `amp_isHCParam_lamSH D.R (D.hc v)`.

Take `⟨L, hLε, hLlam, hLz, hLz', hLu, hLu', hLc, hLκ⟩` from `amp_locBessel_exists_of (epsSH D.R) (lamSH D.R (D.hc v)) z z' (u v) (u' v) (cOfDpsi ((kaRe D : ℝ) : ℂ)) 1 hlam ⟨hzW, hz0⟩ ⟨hzW', hz0'⟩ (H.1 _ hlam) (H.2.1 z _ hzW hz0 hu) (H.2.1 z' _ hzW' hz0' hu') (H.2.2 z hzW hz0) (H.2.2 z' hzW' hz0')`. Establish `hdiv : kaRe D / kaRe D = 1` using `div_self hka.ne'`. Use `⟨L, ⟨hk1, hLε, hLc, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, μsec, ?_⟩` and prove the remaining obligations. Rewrite using `[hLκ]`. Conclude with `one_pos`.

Rewrite using `[hLκ]`. Conclude with `ENNReal.one_ne_top`. Rewrite using `[hLu, hLu', hLz, hLz', hLε, hzT, hzT', hdiv]`. Simplify using `using hSv`. Rewrite using `[hLz, hzT]`.

Conclude with `hT1`. Rewrite using `[hLz', hzT']`. Conclude with `hT2`. Rewrite using `[hLlam]`. Simplify using `[l1]`.

Rewrite using `[hLz, hzT]`. Rewrite using `[hLz', hzT']`. Rewrite using `[hLz, hLz']`. Conclude with `hsec`.
-/
theorem amp_bData_nonempty (D : D7) (Ch Cg : ℝ) (T T' : ℕ) (b : ℝ) (u u' : D.what₂.Tau → Fin D.R.k → ℝ)
    (H : amp_HRepD D) (hS : Formalism.QuantumDeterminants.SectionExists) (hN : amp_HNumB D Ch Cg T T' b u u') :
    Nonempty (BData D Ch Cg T T' b 0) := by
  obtain ⟨hN, hT1, hT2⟩ := hN
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hTpos : ∀ n : ℕ, 1 ≤ (n : ℝ) * kaRe D ^ (2 * D.R.rS) → 0 < (n : ℝ) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at hn
    · exact_mod_cast h
  have hTp := hTpos T hT1
  have hTp' := hTpos T' hT2
  obtain ⟨z, hzW, hzT⟩ := amp_z_exists D.R.k D.R.rS T hTp.le
  obtain ⟨z', hzW', hzT'⟩ := amp_z_exists D.R.k D.R.rS T' hTp'.le
  have hz0 : 0 < Tz D.R.k D.R.rS z := by rw [hzT]; exact hTp
  have hz0' : 0 < Tz D.R.k D.R.rS z' := by rw [hzT']; exact hTp'
  obtain ⟨μsec, hsec⟩ := hS D.R.k D.R.rS z z' hk1 hzW hzW' hz0 hz0'
  apply amp_bData_nonempty_of
  intro v
  obtain ⟨hu, hu', hSv⟩ := hN v
  have hka : 0 < kaRe D := hSv.2.2.2.1
  have hlam := amp_isHCParam_lamSH D.R (D.hc v)
  obtain ⟨L, hLε, hLlam, hLz, hLz', hLu, hLu', hLc, hLκ⟩ := amp_locBessel_exists_of (epsSH D.R)
    (lamSH D.R (D.hc v)) z z' (u v) (u' v) (cOfDpsi ((kaRe D : ℝ) : ℂ)) 1 hlam ⟨hzW, hz0⟩ ⟨hzW', hz0'⟩
    (H.1 _ hlam) (H.2.1 z _ hzW hz0 hu) (H.2.1 z' _ hzW' hz0' hu') (H.2.2 z hzW hz0) (H.2.2 z' hzW' hz0')
  have hdiv : kaRe D / kaRe D = 1 := div_self hka.ne'
  refine ⟨L, ⟨hk1, hLε, hLc, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, μsec, ?_⟩
  · rw [hLκ]; exact one_pos
  · rw [hLκ]; exact ENNReal.one_ne_top
  · rw [hLu, hLu', hLz, hLz', hLε, hzT, hzT', hdiv]; simpa using hSv
  · rw [hLz, hzT]; exact hT1
  · rw [hLz', hzT']; exact hT2
  · rw [hLlam]; simp [l1]
  · rw [hLz, hzT]
  · rw [hLz', hzT']
  · rw [hLz, hLz']; exact hsec

/- English proof (translation)
Unfold `ell`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Use `split_ifs with h`. Apply `Matrix.one_apply_ne` to reduce the goal to its premises.

Introduce `h2`. Establish `h3` using `congrArg Fin.val h2`. Simplify using `[eI] at h3`. Rewrite using `[Matrix.one_mulVec]`. Apply `hz` to reduce the goal to its premises.

Use `left`. Simplify using `[eI]`.
-/
theorem amp_ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : ell k r z 1 = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · apply Matrix.one_apply_ne
    intro h2
    have h3 := congrArg Fin.val h2
    simp [eI] at h3
  · rw [Matrix.one_mulVec]
    apply hz
    left
    simp [eI]

/- English proof (translation)
Establish `h1R' : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ RStab k r g`. Rewrite using `[hR]`. Conclude with `Set.mem_singleton _`. Establish `h1R : Matrix.of (fun i j => (1 : Mx k r) i j) ∈ RStab k r g` using `h1R'`. Use `haveI : IsEmpty (rootPat γ) := Finset.isEmpty_coe_sort.mpr hp`.

Establish `hcard : (rootPat γ).card = 0` using `by rw [hp]; rfl`. Establish `hvol : ∀ x : Mt k r, (Measure.dirac x).map (rootCoords k r L.z γ) = volume`. Introduce `x`. Use extensionality with `s hs`. Break down `s.eq_empty_or_nonempty with h | h` into its components or cases.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[h.eq_univ, Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]`. Simplify using `[MeasureTheory.volume_pi]`. Use `⟨hg, ?_, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `a ha`. Rewrite `ha` using `[hR]`. Establish `ha' : a = 1` using `ha`. Substitute `ha'` using the available equality. Rewrite using `[mul_one, hinv]`.

Simplify using `only [psi, amp_ell_one k r L.z L.hz.1, amp_ell_one k r L.z' L.hz'.1]`. Rewrite using `[Measure.dirac_apply]`. Simplify using `[Set.indicator, h1R]`. Rewrite using `[hcard, pow_zero, ENNReal.ofReal_one, one_smul]`. Conclude with `hvol _`.

Introduce `f hf`. Establish `hs : ∀ x : PairSp k r, stabAct g (Matrix.of (fun i j => (1 : Mx k r) i j)) x = x`. Introduce `x`. Use `show stabAct g (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) x = x`. Simplify using `[stabAct, hinv]`.

Simplify using `only [lintegral_dirac, hs]`.
-/
theorem amp_orbClass_open {k r : ℕ} (L : LocBessel k r) (γ : Point ℂ (r + 1)) (g : Mx k r) (hg : IsPtRep L γ g)
    (hinv : g⁻¹ * g = 1) (hp : rootPat γ = ∅) (hR : RStab k r g = {1}) :
    IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g (Measure.dirac (fun i j => (1 : Mx k r) i j)) ∧
      IsOrbQuot L g (Measure.dirac (fun i j => (1 : Mx k r) i j)) (pairMeas L) := by
  have h1R' : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ RStab k r g := by
    rw [hR]
    exact Set.mem_singleton _
  have h1R : Matrix.of (fun i j => (1 : Mx k r) i j) ∈ RStab k r g := h1R'
  haveI : IsEmpty (rootPat γ) := Finset.isEmpty_coe_sort.mpr hp
  have hcard : (rootPat γ).card = 0 := by rw [hp]; rfl
  have hvol : ∀ x : Mt k r, (Measure.dirac x).map (rootCoords k r L.z γ) = volume := by
    intro x
    ext s hs
    rcases s.eq_empty_or_nonempty with h | h
    · subst h
      simp
    · rw [h.eq_univ, Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]
      simp [MeasureTheory.volume_pi]
  refine ⟨hg, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [hR] at ha
    have ha' : a = 1 := ha
    subst ha'
    rw [mul_one, hinv]
    simp only [psi, amp_ell_one k r L.z L.hz.1, amp_ell_one k r L.z' L.hz'.1]
  · rw [Measure.dirac_apply]
    simp [Set.indicator, h1R]
  · rw [hcard, pow_zero, ENNReal.ofReal_one, one_smul]
    exact hvol _
  · intro f hf
    have hs : ∀ x : PairSp k r, stabAct g (Matrix.of (fun i j => (1 : Mx k r) i j)) x = x := by
      intro x
      show stabAct g (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) x = x
      simp [stabAct, hinv]
    simp only [lintegral_dirac, hs]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [lamSH, lamS, hv, hb]`.
-/
theorem amp_lamSH_congr (R : Ranks) (P P' : HCParam R) (hv : P.v = P'.v) (hb : P.b = P'.b) : lamSH R P = lamSH R P' := by
  funext i
  simp only [lamSH, lamS, hv, hb]

/- English proof (translation)
Use `⟨strictAnti_of_succ_lt' R.k _ (fun i hi => ?_), fun a => ?_⟩` and prove the remaining obligations. Establish `key : P.u ⟨i + 1, hi⟩ < P.u ⟨i, by omega⟩` using `lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)`. Conclude with `key` after adjusting the coercions. Take `⟨q, hq⟩` from `R.k_even`. Take `⟨z, hz⟩` from `P.u_half a`.

Use `⟨z - q + 1, ?_⟩` and prove the remaining obligations. Establish `hk : (R.k : ℝ) = (q : ℝ) + q` using `by exact_mod_cast hq`. Establish `hu : ((P.u a : ℚ) : ℝ) = (z : ℝ) + 1 / 2` using `by rw [hz]; push_cast; ring`. Use `push_cast`. Combine the linear relations using `[hu, hk]`.
-/
theorem amp_isHCParam_u (R : Ranks) (P : HCParam R) : IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  refine ⟨strictAnti_of_succ_lt' R.k _ (fun i hi => ?_), fun a => ?_⟩
  · have key : P.u ⟨i + 1, hi⟩ < P.u ⟨i, by omega⟩ :=
      lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
    exact_mod_cast key
  · obtain ⟨q, hq⟩ := R.k_even
    obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z - q + 1, ?_⟩
    have hk : (R.k : ℝ) = (q : ℝ) + q := by exact_mod_cast hq
    have hu : ((P.u a : ℚ) : ℝ) = (z : ℝ) + 1 / 2 := by rw [hz]; push_cast; ring
    push_cast
    linarith [hu, hk]

/- English proof (translation)
The claim follows from `amp_isHCParam_u D.R (D.hcW w τ)`.
-/
theorem amp_isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : IsHCParam (uS D w τ) := amp_isHCParam_u D.R (D.hcW w τ)

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `hd` using `dimS_eq R`. Establish `hr : R.r = R.k + R.m - 1` using `rfl`. Use `⟨fun i hi => ?_, fun h => ?_⟩` and prove the remaining obligations.

Establish `e : lamSH R P ⟨i, by omega⟩ = (P.v ⟨i, by omega⟩ : ℝ)` using `amp_lamS_lo R P (Fin.cast (dimS_eq R) ⟨i, by omega⟩) (show i < R.k - 1 by omega)`. Rewrite using `[e]`. Establish `c1 : ((P.v ⟨i, by omega⟩ : ℚ) : ℝ) < ((P.u ⟨i, by omega⟩ : ℚ) : ℝ)`. Conclude with `P.u_gt_v ⟨i, by omega⟩` after adjusting the coercions. Establish `c2 : ((P.u ⟨i + 1, hi⟩ : ℚ) : ℝ) < ((P.v ⟨i, by omega⟩ : ℚ) : ℝ)`.

Conclude with `P.v_gt_u ⟨i, by omega⟩` after adjusting the coercions. Conclude with `⟨c1, c2⟩`. Establish `e : lamSH R P ⟨R.k - 1, by omega⟩ = -(P.b ⟨R.k - 1 - (R.k - 1), by omega⟩ : ℝ)` using `amp_lamS_hi R P (Fin.cast (dimS_eq R) ⟨R.k - 1, by omega⟩) (show ¬ R.k - 1 < R.k - 1 by omega) (show R.k - 1 - (R.k - 1) < R.m by omega)`. Establish `e0 : P.b ⟨R.k - 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩` using `congrArg P.b (Fin.ext (show R.k - 1 - (R.k - 1) = 0 by omega))`. Rewrite using `[e, e0]`.

Establish `c3 : -((P.b ⟨0, by omega⟩ : ℚ) : ℝ) < ((P.u ⟨R.k - 1, by omega⟩ : ℚ) : ℝ)`. Conclude with `P.u_last_gt (by omega) (by omega)` after adjusting the coercions. Conclude with `c3`.
-/
theorem amp_interlace_P (R : Ranks) (P : HCParam R) :
    InterlaceS (by omega) (fun i => ((P.u i : ℚ) : ℝ)) (lamSH R P) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hd := dimS_eq R
  have hr : R.r = R.k + R.m - 1 := rfl
  refine ⟨fun i hi => ?_, fun h => ?_⟩
  · have e : lamSH R P ⟨i, by omega⟩ = (P.v ⟨i, by omega⟩ : ℝ) :=
      amp_lamS_lo R P (Fin.cast (dimS_eq R) ⟨i, by omega⟩) (show i < R.k - 1 by omega)
    rw [e]
    have c1 : ((P.v ⟨i, by omega⟩ : ℚ) : ℝ) < ((P.u ⟨i, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast P.u_gt_v ⟨i, by omega⟩
    have c2 : ((P.u ⟨i + 1, hi⟩ : ℚ) : ℝ) < ((P.v ⟨i, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast P.v_gt_u ⟨i, by omega⟩
    exact ⟨c1, c2⟩
  · have e : lamSH R P ⟨R.k - 1, by omega⟩ = -(P.b ⟨R.k - 1 - (R.k - 1), by omega⟩ : ℝ) :=
      amp_lamS_hi R P (Fin.cast (dimS_eq R) ⟨R.k - 1, by omega⟩) (show ¬ R.k - 1 < R.k - 1 by omega)
        (show R.k - 1 - (R.k - 1) < R.m by omega)
    have e0 : P.b ⟨R.k - 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩ :=
      congrArg P.b (Fin.ext (show R.k - 1 - (R.k - 1) = 0 by omega))
    rw [e, e0]
    have c3 : -((P.b ⟨0, by omega⟩ : ℚ) : ℝ) < ((P.u ⟨R.k - 1, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast P.u_last_gt (by omega) (by omega)
    exact c3

/- English proof (translation)
Establish `e : lamD D τ = lamSH D.R (D.hcW w τ)` using `amp_lamSH_congr D.R (D.hc τ) (D.hcW w τ) (D.hcW_v w τ).symm (D.hcW_b w τ).symm`. Rewrite using `[e]`. Conclude with `amp_interlace_P D.R (D.hcW w τ)`.
-/
theorem amp_interlace_D (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    InterlaceS (by omega) (uS D w τ) (lamD D τ) := by
  have e : lamD D τ = lamSH D.R (D.hcW w τ) :=
    amp_lamSH_congr D.R (D.hc τ) (D.hcW w τ) (D.hcW_v w τ).symm (D.hcW_b w τ).symm
  rw [e]
  exact amp_interlace_P D.R (D.hcW w τ)

/- English proof (translation)
Conclude with `amp_goodW_exists_of D τ w w' θ hθ hT hT' (fun z hz hz0 => H.2.1 z _ hz hz0 (amp_isHCParam_uS D w τ)) (fun z hz hz0 => H.2.1 z _ hz hz0 (amp_isHCParam_uS D w' τ)) H.2.2 hG hQ`.
-/
theorem amp_goodW_exists (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (hθ : 0 < θ)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (H : amp_HRepD D) (hG : amp_HHaarG D.R.k D.R.rS)
    (hQ : ∀ z, inWb D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z → amp_HQuot D.R.k D.R.rS z) :
    ∃ W : LocW D.R.k D.R.rS, GoodW D τ w w' θ W := by
  exact amp_goodW_exists_of D τ w w' θ hθ hT hT'
    (fun z hz hz0 => H.2.1 z _ hz hz0 (amp_isHCParam_uS D w τ))
    (fun z hz hz0 => H.2.1 z _ hz hz0 (amp_isHCParam_uS D w' τ)) H.2.2 hG hQ

/- English proof (translation)
Use `⟨{ Sm := ∅, Hs := fun _ => ℂ, σs := fun _ _ => 0, ds := fun s hs => by simp at hs, inequiv := fun s hs => by simp at hs, toSum := fun v w x y _ _ => ⟨Empty, inferInstance, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun g _ => ?_⟩, …` and prove the remaining obligations. Rewrite using `[Subsingleton.elim w 0]`. Simplify using the standard rewrite rules.
-/
theorem amp_tensorDSd_nonempty_of_subsingleton (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Subsingleton H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Nonempty (Formalism.MainNotions.OnePlaceEstimates.TensorDSd n ε μ H σ) := by
  refine ⟨{ Sm := ∅, Hs := fun _ => ℂ, σs := fun _ _ => 0, ds := fun s hs => by simp at hs, inequiv := fun s hs => by simp at hs, toSum := fun v w x y _ _ => ⟨Empty, inferInstance, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun i => Empty.elim i, fun g _ => ?_⟩, ofSum := fun s hs => by simp at hs }⟩
  rw [Subsingleton.elim w 0]
  simp

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -, -, -, hTr, -, -⟩` from `h`. Establish `hk5 : (5 : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(show 5 ≤ D.R.k by omega)` after adjusting the coercions.

Establish `hb0 : 0 < large₂.sc.b` using `by linarith`. Establish `h8 : 0 ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8` using `by positivity`. Establish `hgg : ((D.R.k : ℝ) * large₂.sc.b) ^ 16 ≤ gg D`. Unfold `gg`. Combine the equalities or inequalities in the displayed calculation.

Establish `hgpos : 0 < gg D` using `lt_of_lt_of_le (by positivity) hgg`. Establish `hka : D.host.ka ≤ 4`. Unfold `Host.ka`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear relations using `[Real.pi_le_four]`.

Establish `hka_pos : 0 < D.host.ka`. Unfold `Host.ka`. Conclude with `div_pos Real.pi_pos (by linarith)`. Establish `hkaS_pos : 0 < Bridge.kaS D`. Unfold `Bridge.kaS`.

Conclude with `div_pos hka_pos hgpos`. Establish `hkaS : Bridge.kaS D * large₂.sc.b ^ 16 ≤ 1`. Establish `hk16 : (5 : ℝ) ^ 16 ≤ (D.R.k : ℝ) ^ 16` using `by gcongr`. Establish `hb16 : 0 < large₂.sc.b ^ 16` using `by positivity`. Establish `e : ((D.R.k : ℝ) * large₂.sc.b) ^ 16 = (D.R.k : ℝ) ^ 16 * large₂.sc.b ^ 16` using `mul_pow _ _ _`.

Unfold `Bridge.kaS`. Rewrite using `[div_mul_eq_mul_div, div_le_one hgpos]`. Use polynomial arithmetic with `[hka, hgg, e, hk16, hb16]`. Establish `hpow : (Bridge.kaS D * large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ 1` using `pow_le_one₀ (mul_pos hkaS_pos (pow_pos hb0 16)).le hkaS`. Establish `hB : 0 < (large₂.sc.b ^ 16) ^ (2 * D.R.rS)` using `by positivity`.

Establish `hTr0 : 0 ≤ Tr D w` using `le_trans (Real.rpow_nonneg hb0.le _) (hTr w).1`. Establish `hTw` using `(hTr w).2`. Rewrite `hpow` using `[mul_pow]`. Establish `hle : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))`. Use polynomial arithmetic with `[hTw, hT, hpow, hB, hTr0]`.

Rewrite `hle` using `[← pow_mul, ← Real.rpow_natCast, Real.rpow_le_rpow_left_iff hb]`. Move the coercions through the operations in `at hle ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amp_scaledT_forces_CT (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ)
    (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hb : 1 < large₂.sc.b) (w : D.what₂.Word)
    (hT : 1 ≤ Tr D w * Bridge.kaS D ^ (2 * D.R.rS)) : ((32 * D.R.rS : ℕ) : ℝ) ≤ CT * (D.R.m : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -, -, -, hTr, -, -⟩ := h
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    exact_mod_cast (show 5 ≤ D.R.k by omega)
  have hb0 : 0 < large₂.sc.b := by linarith
  have h8 : 0 ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by positivity
  have hgg : ((D.R.k : ℝ) * large₂.sc.b) ^ 16 ≤ gg D := by
    unfold gg
    calc ((D.R.k : ℝ) * large₂.sc.b) ^ 16 = ((D.R.k : ℝ) * large₂.sc.b) ^ 8 * ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by ring
      _ ≤ (D.host.g 0 : ℝ) * D.host.g 1 := mul_le_mul hg1 hg2 h8 (le_trans h8 hg1)
  have hgpos : 0 < gg D := lt_of_lt_of_le (by positivity) hgg
  have hka : D.host.ka ≤ 4 := by
    unfold Host.ka
    rw [div_le_iff₀ (by linarith)]
    linarith [Real.pi_le_four]
  have hka_pos : 0 < D.host.ka := by
    unfold Host.ka
    exact div_pos Real.pi_pos (by linarith)
  have hkaS_pos : 0 < Bridge.kaS D := by
    unfold Bridge.kaS
    exact div_pos hka_pos hgpos
  have hkaS : Bridge.kaS D * large₂.sc.b ^ 16 ≤ 1 := by
    have hk16 : (5 : ℝ) ^ 16 ≤ (D.R.k : ℝ) ^ 16 := by gcongr
    have hb16 : 0 < large₂.sc.b ^ 16 := by positivity
    have e : ((D.R.k : ℝ) * large₂.sc.b) ^ 16 = (D.R.k : ℝ) ^ 16 * large₂.sc.b ^ 16 := mul_pow _ _ _
    unfold Bridge.kaS
    rw [div_mul_eq_mul_div, div_le_one hgpos]
    nlinarith [hka, hgg, e, hk16, hb16]
  have hpow : (Bridge.kaS D * large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ 1 :=
    pow_le_one₀ (mul_pos hkaS_pos (pow_pos hb0 16)).le hkaS
  have hB : 0 < (large₂.sc.b ^ 16) ^ (2 * D.R.rS) := by positivity
  have hTr0 : 0 ≤ Tr D w := le_trans (Real.rpow_nonneg hb0.le _) (hTr w).1
  have hTw := (hTr w).2
  rw [mul_pow] at hpow
  have hle : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := by
    nlinarith [hTw, hT, hpow, hB, hTr0]
  rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_le_rpow_left_iff hb] at hle
  push_cast at hle ⊢
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hQ, -⟩` from `h`. Assume the negation of the conclusion as `hθ`. Use `push_neg at hθ`. Establish `hv` using `amp_v_pos D`. Establish `hk0 : kapN D θ = 0`.

Unfold `kapN`. Apply `ENNReal.ofReal_of_nonpos` to reduce the goal to its premises. Conclude with `mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) hθ`. Rewrite `hN` using `[hk0]`. Establish `hN0 : W.μN = 0` using `by rw [hN]; unfold haarLie; simp`.

Establish `h1` using `hQ (fun _ => 1) measurable_const`. Rewrite `h1` using `[hN0]`. Unfold `muS at h1`. Simplify using `at h1`. Apply `hG.2.1` to reduce the goal to its premises.

Simplify `h1` using `[Measure.measure_univ_eq_zero]`.
-/
theorem amp_goodW_theta_pos (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS)
    (h : GoodW D τ w w' θ W) : 0 < θ := by
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hQ, -⟩ := h
  by_contra hθ
  push_neg at hθ
  have hv := amp_v_pos D
  have hk0 : kapN D θ = 0 := by
    unfold kapN
    apply ENNReal.ofReal_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) hθ
  rw [hk0] at hN
  have hN0 : W.μN = 0 := by rw [hN]; unfold haarLie; simp
  have h1 := hQ (fun _ => 1) measurable_const
  rw [hN0] at h1
  unfold muS at h1
  simp at h1
  apply hG.2.1
  simpa [Measure.measure_univ_eq_zero] using h1

/- English proof (translation)
Establish `h0 : 0 ≤ C1 * (D.R.m : ℝ) ^ 2` using `mul_nonneg hC (sq_nonneg _)`. Conclude with `⟨Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith), Real.one_le_rpow hb h0⟩`.
-/
theorem amp_normWin_one (D : D7) (large₂ : SizeData₂ D) (C1 : ℝ) (hC : 0 ≤ C1) (hb : 1 ≤ large₂.sc.b) : normWin D large₂ C1 1 := by
  have h0 : 0 ≤ C1 * (D.R.m : ℝ) ^ 2 := mul_nonneg hC (sq_nonneg _)
  exact ⟨Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith), Real.one_le_rpow hb h0⟩

end

end Formalism.MainNotions.S.Inh
