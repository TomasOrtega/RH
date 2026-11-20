import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Inh

namespace Formalism.L2.SG.Pf.WuBL

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `hr : R.r = R.k + R.m - 1` using `rfl`. Establish `hdim : 2 * R.rS + R.k + 1 = R.r` using `dimS_eq R`. Establish `h0 : (0 : ℚ) ≤ 16 * (R.r : ℚ) ^ 19` using `by positivity`.

Establish `bmono : ∀ n : ℕ, ∀ (j j' : Fin R.m), j'.val = j.val + n + 1 → 16 * (R.r : ℚ) ^ 19 ≤ P.b j' - P.b j`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `j j' hj`.

Establish `h` using `hg j (by omega)`. Establish `e : (⟨j.1 + 1, by omega⟩ : Fin R.m) = j'` using `Fin.ext (by simp [hj])`. Rewrite `h` using `[e]`. Conclude with `h`. Consider the case `succ n ih`.

Introduce `j j' hj`. Establish `h1` using `ih j ⟨j.1 + n + 1, by omega⟩ rfl`. Apply the tactic sequence `have h2 := hg ⟨j.1 + n + 1, by omega⟩ (by first | omega | (simp; omega))`. Apply the tactic sequence `have e : (⟨j.1 + n + 1 + 1, by omega⟩ : Fin R.m) = j' := Fin.ext (by first | omega | (simp; omega))`. Simplify using `only at h2`.

Rewrite `h2` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `umono : ∀ n : ℕ, ∀ i : Fin R.k, i.val + n = R.k - 1 → P.u ⟨R.k - 1, by omega⟩ ≤ P.u i`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `i hi`. Establish `e : i = ⟨R.k - 1, by omega⟩` using `Fin.ext (by simpa using hi)`. Rewrite using `[e]`. Consider the case `succ n ih`.

Introduce `i hi`. Apply the tactic sequence `have h1 := ih ⟨i.1 + 1, by omega⟩ (by first | omega | (simp; omega))`. Establish `h2` using `P.v_gt_u ⟨i.1, by omega⟩`. Establish `h3` using `P.u_gt_v ⟨i.1, by omega⟩`. Simplify using `only at h2 h3`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlast` using `P.u_last_gt (by omega) (by omega)`. Unfold `epsSH epsS at he`. Unfold `lamSH lamS`. Simplify using `only [Fin.coe_cast] at he ⊢`.

Establish `ha : a.val < R.r` using `by have := a.isLt; omega`. Establish `hb : b.val < R.r` using `by have := b.isLt; omega`. Establish `hab' : a.val < b.val` using `hab`. Apply the tactic sequence `by_cases hak : a.val < R.k - 1 <;> by_cases hbk : b.val < R.k - 1`. Rewrite `he` using `[if_pos hak, if_pos hbk]`.

Conclude with `absurd rfl he`. Rewrite `he` using `[if_pos hak, if_neg hbk]`. Establish `hjb : b.val - (R.k - 1) < R.m` using `by omega`. Establish `hodd : (b.val - (R.k - 1)) % 2 ≠ 0`. Introduce `h`.

Conclude with `he (by simp [h])`. Rewrite using `[dif_pos hak, dif_neg hbk, dif_pos hjb]`. Apply the tactic sequence `have h1 := bmono (b.val - (R.k - 1) - 1) ⟨0, by omega⟩ ⟨b.val - (R.k - 1), hjb⟩ (by first | omega | (simp; omega))`. Apply the tactic sequence `have h2 := umono (R.k - 1 - (a.val + 1)) ⟨a.val + 1, by omega⟩ (by first | omega | (simp; omega))`. Establish `h3` using `P.v_gt_u ⟨a.val, hak⟩`.

Simplify using `only at h3`. Establish `hq : 16 * (R.r : ℚ) ^ 19 ≤ P.v ⟨a.val, hak⟩ + P.b ⟨b.val - (R.k - 1), hjb⟩` using `by linarith`. Establish `hq'` using `(Rat.cast_le (K := ℝ)).2 hq`. Move the coercions through the operations in `at hq'`. Combine the linear equalities and inequalities to obtain the conclusion.

Use linear arithmetic over natural numbers and integers. Rewrite `he` using `[if_neg hak, if_neg hbk]`. Establish `hja : a.val - (R.k - 1) < R.m` using `by omega`. Establish `hjb : b.val - (R.k - 1) < R.m` using `by omega`. Establish `hne : a.val - (R.k - 1) ≠ b.val - (R.k - 1)`.

Introduce `h`. Conclude with `he (by simp [h])`. Rewrite using `[dif_neg hak, dif_neg hbk, dif_pos hja, dif_pos hjb]`. Apply the tactic sequence `have h1 := bmono (b.val - (R.k - 1) - (a.val - (R.k - 1)) - 1) ⟨a.val - (R.k - 1), hja⟩ ⟨b.val - (R.k - 1), hjb⟩ (by first | omega | (simp; omega))`. Establish `hq'` using `(Rat.cast_le (K := ℝ)).2 h1`.

Move the coercions through the operations in `at hq'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_lt (R : Ranks) (P : HCParam R)
    (hg : ∀ (j : Fin R.m) (h : j.1 + 1 < R.m), 16 * (R.r : ℚ) ^ 19 ≤ P.b ⟨j.1 + 1, h⟩ - P.b j)
    (a b : Fin (2 * R.rS + R.k + 1)) (hab : a < b) (he : epsSH R a ≠ epsSH R b) :
    16 * (R.r : ℝ) ^ 19 ≤ lamSH R P a - lamSH R P b := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hr : R.r = R.k + R.m - 1 := rfl
  have hdim : 2 * R.rS + R.k + 1 = R.r := dimS_eq R
  have h0 : (0 : ℚ) ≤ 16 * (R.r : ℚ) ^ 19 := by positivity
  have bmono : ∀ n : ℕ, ∀ (j j' : Fin R.m), j'.val = j.val + n + 1 →
      16 * (R.r : ℚ) ^ 19 ≤ P.b j' - P.b j := by
    intro n
    induction n with
    | zero =>
      intro j j' hj
      have h := hg j (by omega)
      have e : (⟨j.1 + 1, by omega⟩ : Fin R.m) = j' := Fin.ext (by simp [hj])
      rw [e] at h
      exact h
    | succ n ih =>
      intro j j' hj
      have h1 := ih j ⟨j.1 + n + 1, by omega⟩ rfl
      have h2 := hg ⟨j.1 + n + 1, by omega⟩ (by first | omega | (simp; omega))
      have e : (⟨j.1 + n + 1 + 1, by omega⟩ : Fin R.m) = j' := Fin.ext (by first | omega | (simp; omega))
      simp only at h2
      rw [e] at h2
      linarith
  have umono : ∀ n : ℕ, ∀ i : Fin R.k, i.val + n = R.k - 1 → P.u ⟨R.k - 1, by omega⟩ ≤ P.u i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have e : i = ⟨R.k - 1, by omega⟩ := Fin.ext (by simpa using hi)
      rw [e]
    | succ n ih =>
      intro i hi
      have h1 := ih ⟨i.1 + 1, by omega⟩ (by first | omega | (simp; omega))
      have h2 := P.v_gt_u ⟨i.1, by omega⟩
      have h3 := P.u_gt_v ⟨i.1, by omega⟩
      simp only at h2 h3
      linarith
  have hlast := P.u_last_gt (by omega) (by omega)
  unfold epsSH epsS at he
  unfold lamSH lamS
  simp only [Fin.coe_cast] at he ⊢
  have ha : a.val < R.r := by have := a.isLt; omega
  have hb : b.val < R.r := by have := b.isLt; omega
  have hab' : a.val < b.val := hab
  by_cases hak : a.val < R.k - 1 <;> by_cases hbk : b.val < R.k - 1
  · rw [if_pos hak, if_pos hbk] at he
    exact absurd rfl he
  · rw [if_pos hak, if_neg hbk] at he
    have hjb : b.val - (R.k - 1) < R.m := by omega
    have hodd : (b.val - (R.k - 1)) % 2 ≠ 0 := by
      intro h
      exact he (by simp [h])
    rw [dif_pos hak, dif_neg hbk, dif_pos hjb]
    have h1 := bmono (b.val - (R.k - 1) - 1) ⟨0, by omega⟩ ⟨b.val - (R.k - 1), hjb⟩ (by first | omega | (simp; omega))
    have h2 := umono (R.k - 1 - (a.val + 1)) ⟨a.val + 1, by omega⟩ (by first | omega | (simp; omega))
    have h3 := P.v_gt_u ⟨a.val, hak⟩
    simp only at h3
    have hq : 16 * (R.r : ℚ) ^ 19 ≤ P.v ⟨a.val, hak⟩ + P.b ⟨b.val - (R.k - 1), hjb⟩ := by linarith
    have hq' := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hq'
    linarith
  · omega
  · rw [if_neg hak, if_neg hbk] at he
    have hja : a.val - (R.k - 1) < R.m := by omega
    have hjb : b.val - (R.k - 1) < R.m := by omega
    have hne : a.val - (R.k - 1) ≠ b.val - (R.k - 1) := by
      intro h
      exact he (by simp [h])
    rw [dif_neg hak, dif_neg hbk, dif_pos hja, dif_pos hjb]
    have h1 := bmono (b.val - (R.k - 1) - (a.val - (R.k - 1)) - 1) ⟨a.val - (R.k - 1), hja⟩
      ⟨b.val - (R.k - 1), hjb⟩ (by first | omega | (simp; omega))
    have hq' := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at hq'
    linarith

/- English proof (translation)
Introduce `a b he`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Conclude with `(gap_lt R P hg a b hab he).trans (le_abs_self _)`. Conclude with `absurd rfl he`. Rewrite using `[abs_sub_comm]`.

Conclude with `(gap_lt R P hg b a hab (Ne.symm he)).trans (le_abs_self _)`.
-/
theorem gapAtLeast_of (R : Ranks) (P : HCParam R)
    (hg : ∀ (j : Fin R.m) (h : j.1 + 1 < R.m), 16 * (R.r : ℚ) ^ 19 ≤ P.b ⟨j.1 + 1, h⟩ - P.b j) :
    Formalism.QuantumDeterminants.GapAtLeast (epsSH R) (lamSH R P) (16 * (R.r : ℝ) ^ 19) := by
  intro a b he
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (gap_lt R P hg a b hab he).trans (le_abs_self _)
  · exact absurd rfl he
  · rw [abs_sub_comm]
    exact (gap_lt R P hg b a hab (Ne.symm he)).trans (le_abs_self _)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hr : R.r = R.k + R.m - 1` using `rfl`. Establish `hrs : R.rS = R.m / 2 - 1` using `rfl`. Establish `hmk` using `R.m_add_three_le_k`. Establish `hm2` using `R.two_le_m`. Establish `hN : 2 * R.rS + R.k + 1 ≤ 2 * R.r` using `by omega`.

Establish `h16 : 60 ≤ R.r ^ 16` using `le_trans (by omega) (Nat.le_self_pow (by norm_num) R.r)`. Establish `hx0 : (0:ℝ) ≤ (R.rS:ℝ)` using `Nat.cast_nonneg _`. Establish `hk0 : (0:ℝ) ≤ (R.k:ℝ)` using `Nat.cast_nonneg _`. Establish `hxr : (R.rS:ℝ) ≤ (R.r:ℝ)` using `by exact_mod_cast (show R.rS ≤ R.r by omega)`. Establish `hkr : (R.k:ℝ) ≤ (R.r:ℝ)` using `by exact_mod_cast (show R.k ≤ R.r by omega)`.

Establish `hρ : (1801:ℝ) ≤ (R.r:ℝ)` using `by exact_mod_cast h1801`. Establish `hρ0 : (0:ℝ) ≤ (R.r:ℝ)` using `by linarith`. Establish `hs : Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ 2 * (R.r:ℝ)`. Combine the equalities or inequalities in the displayed calculation. Establish `hsp : 0 < Real.sqrt (2 * ((R.rS:ℝ) + 1))` using `Real.sqrt_pos.mpr (by linarith)`.

Establish `p0 : (1:ℝ) ≤ (R.r:ℝ) ^ 2` using `by nlinarith`. Establish `p23 : 16 * (R.r:ℝ) ^ 2 ≤ (R.r:ℝ) ^ 3` using `by nlinarith`. Establish `p35 : (R.r:ℝ) ^ 3 ≤ (R.r:ℝ) ^ 5` using `by nlinarith`. Establish `p13 : (400:ℝ) ≤ (R.r:ℝ) ^ 13`. Establish `h2 : (1801:ℝ) ^ 13 ≤ (R.r:ℝ) ^ 13` using `by gcongr`.

Use the polynomial consequences of the given equalities and inequalities. Establish `p6 : 0 ≤ (R.r:ℝ) ^ 6` using `by positivity`. Establish `hbig : 6400 * (R.r:ℝ) ^ 6 ≤ 16 * (R.r:ℝ) ^ 19` using `by nlinarith`. Establish `fin : ∀ E : ℝ, E ≤ 400 * (R.r:ℝ) ^ 5 → E ≤ 16 * (R.r:ℝ) ^ 19 / (8 * Real.sqrt (2 * ((R.rS:ℝ) + 1)))`. Introduce `E hE`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `h1` using `mul_le_mul_of_nonneg_right hE hsp.le`. Establish `h2 : 400 * (R.r:ℝ) ^ 5 * Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ 400 * (R.r:ℝ) ^ 5 * (2 * R.r)` using `mul_le_mul_of_nonneg_left hs (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hxx` using `mul_le_mul hxr hxr hx0 hρ0`.

Establish `hxk` using `mul_le_mul hxr hkr hk0 hρ0`. Establish `hG : 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) ≤ 16 * (R.r:ℝ) ^ 2`. Use `mul_le_mul (show (R.k:ℝ) + R.rS ≤ 2 * R.r by linarith) (show (R.rS:ℝ) + 1 ≤ 2 * R.r by linarith) (by linarith) (by linarith)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hG0 : 0 ≤ 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1)` using `by positivity`.

Unfold `Formalism.FourierDecayAlt.ThreeDimData.GapOK Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN Formalism.FourierDecayAlt.ThreeDimData.aOf Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.Mexp`. Use `⟨by omega, ?_, fin _ ?_, fin _ ?_⟩` and prove the remaining obligations. Establish `h3 : (2 * R.rS + R.k + 1) ^ 3 ≤ (2 * R.r) ^ 3` using `Nat.pow_le_pow_left hN 3`. Establish `key : 120 * (2 * R.rS + R.k + 1) ^ 3 ≤ 16 * R.r ^ 19`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `key` after adjusting the coercions. Use `push_cast`. Establish `hD : (R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2 ≤ 6 * (R.r:ℝ) ^ 2`. Use the polynomial consequences of the given equalities and inequalities. Establish `hD0 : 0 ≤ (R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2` using `by nlinarith`.

Establish `hAS` using `mul_le_mul (show 2 * (R.rS:ℝ) + R.k ≤ 3 * R.r by linarith) hD hD0 (by linarith)`. Establish `hsum : (2 * (R.rS:ℝ) + R.k) * ((R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2) + 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) ≤ 19 * (R.r:ℝ) ^ 3` using `by nlinarith`. Establish `hsum0 : 0 ≤ (2 * (R.rS:ℝ) + R.k) * ((R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2) + 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1)` using `by positivity`. Establish `hA : 2 * (2 * ((R.rS:ℝ) ^ 2 + R.rS + 1)) ≤ 12 * (R.r:ℝ) ^ 2` using `by nlinarith`. Establish `hprod` using `mul_le_mul hA hsum hsum0 (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`. Establish `hq` using `mul_le_mul (show 2 * (R.rS:ℝ) + R.k + 1 ≤ 4 * R.r by linarith) (show 2 * (R.rS:ℝ) + R.k + 1 ≤ 4 * R.r by linarith) (by positivity) (by linarith)`. Establish `hq0 : 0 ≤ (2 * (R.rS:ℝ) + R.k + 1) * (2 * (R.rS:ℝ) + R.k + 1)` using `by positivity`. Establish `hc` using `mul_le_mul (show (R.rS:ℝ) + 1 ≤ 2 * R.r by linarith) hq hq0 (by linarith)`.

Combine the linear relations using `[hc, hG, p0, p23, p35]`.
-/
theorem gapOK_of (R : Ranks) (h1801 : 1801 ≤ R.r) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK R.k R.rS (16 * (R.r : ℝ) ^ 19) := by
  have hr : R.r = R.k + R.m - 1 := rfl
  have hrs : R.rS = R.m / 2 - 1 := rfl
  have hmk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hN : 2 * R.rS + R.k + 1 ≤ 2 * R.r := by omega
  have h16 : 60 ≤ R.r ^ 16 := le_trans (by omega) (Nat.le_self_pow (by norm_num) R.r)
  have hx0 : (0:ℝ) ≤ (R.rS:ℝ) := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ (R.k:ℝ) := Nat.cast_nonneg _
  have hxr : (R.rS:ℝ) ≤ (R.r:ℝ) := by exact_mod_cast (show R.rS ≤ R.r by omega)
  have hkr : (R.k:ℝ) ≤ (R.r:ℝ) := by exact_mod_cast (show R.k ≤ R.r by omega)
  have hρ : (1801:ℝ) ≤ (R.r:ℝ) := by exact_mod_cast h1801
  have hρ0 : (0:ℝ) ≤ (R.r:ℝ) := by linarith
  have hs : Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ 2 * (R.r:ℝ) := by
    calc Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ Real.sqrt ((2 * (R.r:ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (R.r:ℝ) := Real.sqrt_sq (by linarith)
  have hsp : 0 < Real.sqrt (2 * ((R.rS:ℝ) + 1)) := Real.sqrt_pos.mpr (by linarith)
  have p0 : (1:ℝ) ≤ (R.r:ℝ) ^ 2 := by nlinarith
  have p23 : 16 * (R.r:ℝ) ^ 2 ≤ (R.r:ℝ) ^ 3 := by nlinarith
  have p35 : (R.r:ℝ) ^ 3 ≤ (R.r:ℝ) ^ 5 := by nlinarith
  have p13 : (400:ℝ) ≤ (R.r:ℝ) ^ 13 := by
    have h2 : (1801:ℝ) ^ 13 ≤ (R.r:ℝ) ^ 13 := by gcongr
    nlinarith
  have p6 : 0 ≤ (R.r:ℝ) ^ 6 := by positivity
  have hbig : 6400 * (R.r:ℝ) ^ 6 ≤ 16 * (R.r:ℝ) ^ 19 := by nlinarith
  have fin : ∀ E : ℝ, E ≤ 400 * (R.r:ℝ) ^ 5 →
      E ≤ 16 * (R.r:ℝ) ^ 19 / (8 * Real.sqrt (2 * ((R.rS:ℝ) + 1))) := by
    intro E hE
    rw [le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right hE hsp.le
    have h2 : 400 * (R.r:ℝ) ^ 5 * Real.sqrt (2 * ((R.rS:ℝ) + 1)) ≤ 400 * (R.r:ℝ) ^ 5 * (2 * R.r) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  have hxx := mul_le_mul hxr hxr hx0 hρ0
  have hxk := mul_le_mul hxr hkr hk0 hρ0
  have hG : 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) ≤ 16 * (R.r:ℝ) ^ 2 := by
    have := mul_le_mul (show (R.k:ℝ) + R.rS ≤ 2 * R.r by linarith) (show (R.rS:ℝ) + 1 ≤ 2 * R.r by linarith)
      (by linarith) (by linarith)
    nlinarith
  have hG0 : 0 ≤ 4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) := by positivity
  unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN Formalism.FourierDecayAlt.ThreeDimData.aOf Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.Mexp
  refine ⟨by omega, ?_, fin _ ?_, fin _ ?_⟩
  · have h3 : (2 * R.rS + R.k + 1) ^ 3 ≤ (2 * R.r) ^ 3 := Nat.pow_le_pow_left hN 3
    have key : 120 * (2 * R.rS + R.k + 1) ^ 3 ≤ 16 * R.r ^ 19 := by
      calc 120 * (2 * R.rS + R.k + 1) ^ 3 ≤ 120 * (2 * R.r) ^ 3 := Nat.mul_le_mul_left 120 h3
        _ = 960 * R.r ^ 3 := by ring
        _ ≤ 16 * (R.r ^ 3 * R.r ^ 16) := by nlinarith [Nat.zero_le (R.r ^ 3)]
        _ = 16 * R.r ^ 19 := by ring
    exact_mod_cast key
  · push_cast
    have hD : (R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2 ≤ 6 * (R.r:ℝ) ^ 2 := by
      nlinarith
    have hD0 : 0 ≤ (R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2 := by nlinarith
    have hAS := mul_le_mul (show 2 * (R.rS:ℝ) + R.k ≤ 3 * R.r by linarith) hD hD0 (by linarith)
    have hsum : (2 * (R.rS:ℝ) + R.k) * ((R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2) +
        4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) ≤ 19 * (R.r:ℝ) ^ 3 := by nlinarith
    have hsum0 : 0 ≤ (2 * (R.rS:ℝ) + R.k) * ((R.rS:ℝ) * ((R.rS:ℝ) - 1) + 2 * R.rS * ((R.k:ℝ) + 1) + (R.rS:ℝ) ^ 2) +
        4 * ((R.k:ℝ) + R.rS) * ((R.rS:ℝ) + 1) := by positivity
    have hA : 2 * (2 * ((R.rS:ℝ) ^ 2 + R.rS + 1)) ≤ 12 * (R.r:ℝ) ^ 2 := by nlinarith
    have hprod := mul_le_mul hA hsum hsum0 (by positivity)
    nlinarith
  · push_cast
    have hq := mul_le_mul (show 2 * (R.rS:ℝ) + R.k + 1 ≤ 4 * R.r by linarith)
      (show 2 * (R.rS:ℝ) + R.k + 1 ≤ 4 * R.r by linarith) (by positivity) (by linarith)
    have hq0 : 0 ≤ (2 * (R.rS:ℝ) + R.k + 1) * (2 * (R.rS:ℝ) + R.k + 1) := by positivity
    have hc := mul_le_mul (show (R.rS:ℝ) + 1 ≤ 2 * R.r by linarith) hq hq0 (by linarith)
    linarith [hc, hG, p0, p23, p35]

/- English proof (translation)
Introduce `D hD τ`. Conclude with `⟨16 * (D.R.r : ℝ) ^ 19, gapAtLeast_of D.R (D.hc τ) (hD.2 τ), gapOK_of D.R hD.1⟩`.
-/
theorem parameter_gap_of_hypothesis : GapOfHyp := by
  intro D hD τ
  exact ⟨16 * (D.R.r : ℝ) ^ 19, gapAtLeast_of D.R (D.hc τ) (hD.2 τ), gapOK_of D.R hD.1⟩

end Formalism.L2.SG.Pf.WuBL
