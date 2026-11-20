import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SegmentBlockOfMonomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

/- English proof (translation)
Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun c _ => (Nat.mod_add_div _ _).symm`.
-/
theorem nb_sum_mod_div {n : ℕ} (f : Fin n → ℕ) (P : ℕ) : ∑ c, f c = ∑ c, f c % P + P * ∑ c, f c / P := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => (Nat.mod_add_div _ _).symm

/- English proof (translation)
Rewrite using `[← h, nb_sum_mod_div f P]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nb_key {n : ℕ} (P a : ℕ) (f : Fin n → ℕ) (B : ℕ) (h : P * a + ∑ c, f c = B) :
    B = P * (a + ∑ c, f c / P) + ∑ c, f c % P := by
  rw [← h, nb_sum_mod_div f P]
  ring

/- English proof (translation)
Break down `Q with _ | q` into its components or cases. Conclude with `Nat.zero_le _`. Establish `hP : 1 ≤ P` using `by omega`. Establish `hq : q ≤ q * P` using `Nat.le_mul_of_pos_right q hP`. Establish `: (q + 1) * P = q * P + P` using `by ring`.

Use linear arithmetic over natural numbers and integers.
-/
theorem nb_q_le (Q P r a : ℕ) (hr : r < P) (h : Q * P ≤ a) : Q ≤ a - r := by
  rcases Q with _ | q
  · exact Nat.zero_le _
  · have hP : 1 ≤ P := by omega
    have hq : q ≤ q * P := Nat.le_mul_of_pos_right q hP
    have : (q + 1) * P = q * P + P := by ring
    omega

/- English proof (translation)
The claim follows from `Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hP).2 h)`.
-/
theorem nb_div_le (a P n : ℕ) (hP : 0 < P) (h : a < (n + 1) * P) : a / P ≤ n :=
  Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hP).2 h)

section NB

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ)
  (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X)

/- English proof (translation)
Unfold `SegData.P`. Conclude with `pow_pos hp _`.
-/
theorem nb_Ppos (hp : 0 < X.p) (i : Fin (segS X.TT j)) : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
  unfold SegData.P
  exact pow_pos hp _

/- English proof (translation)
Establish `hP` using `nb_Ppos C0 CE1 CE2 X j hp i`. Establish `h` using `nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)`. Use `show ((X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i) / (X.seg C0 CE1 CE2 j).P X.p i = _`. Rewrite using `[h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]`. Unfold `z0A ezA`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nb_coarseA (hp : 0 < X.p)
    (dz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
      ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i) (i : Fin (segS X.TT j)) :
    coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + z0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
  have hP := nb_Ppos C0 CE1 CE2 X j hp i
  have h := nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)
  show ((X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i) /
    (X.seg C0 CE1 CE2 j).P X.p i = _
  rw [h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]
  unfold z0A ezA
  ring

/- English proof (translation)
Establish `hP` using `nb_Ppos C0 CE1 CE2 X j hp i`. Establish `h` using `nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)`. Use `show (segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i) / (X.seg C0 CE1 CE2 j).P X.p i = _`. Rewrite using `[h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]`. Unfold `y0A eyA`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nb_coarseC (hp : 0 < X.p)
    (dy : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
      ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) (i : Fin (segS X.TT j)) :
    coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i) + y0A C0 CE1 CE2 X j A i + ∑ c, eyA C0 CE1 CE2 X j A i c := by
  have hP := nb_Ppos C0 CE1 CE2 X j hp i
  have h := nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)
  show (segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i) /
    (X.seg C0 CE1 CE2 j).P X.p i = _
  rw [h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP, Fin.sum_univ_succ]
  unfold y0A eyA
  ring

/- English proof (translation)
Use `⟨fun i c => ⟨Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i), Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i)⟩, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i) show ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ (X.seg C0 CE1 CE2 j).bTop i ∧ (X.seg C0 CE1 CE2 j).P X.p i ∣ (X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X …`. Rewrite using `[h, Nat.add_sub_cancel]`. Conclude with `⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩`. Establish `h` using `nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i) show ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ segATop X.TT X.aT j i ∧ (X.seg C0 CE1 CE2 j).P X.p i ∣ segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i`.

Rewrite using `[h, Nat.add_sub_cancel]`. Conclude with `⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩`.
-/
theorem nb_digits (hp : 0 < X.p)
    (dz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
      ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i)
    (dy : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
      ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) :
    DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) := by
  refine ⟨fun i c => ⟨Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i), Nat.mod_lt _ (nb_Ppos C0 CE1 CE2 X j hp i)⟩,
    fun i => ?_, fun i => ?_⟩
  · have h := nb_key _ _ (fun c => A ((topOdd X j i, true), c)) _ (dz i)
    show ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ (X.seg C0 CE1 CE2 j).bTop i ∧
      (X.seg C0 CE1 CE2 j).P X.p i ∣
        (X.seg C0 CE1 CE2 j).bTop i - ∑ c, A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i
    rw [h, Nat.add_sub_cancel]
    exact ⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩
  · have h := nb_key _ _ (fun c => A ((topOdd X j i, false), c)) _ (dy i)
    show ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i ≤ segATop X.TT X.aT j i ∧
      (X.seg C0 CE1 CE2 j).P X.p i ∣
        segATop X.TT X.aT j i - ∑ c, A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i
    rw [h, Nat.add_sub_cancel]
    exact ⟨Nat.le_add_left _ _, Dvd.intro _ rfl⟩

/- English proof (translation)
Simplify using `only [oEff, segmentBlockOfMonomial]`. Use `split_ifs with h`. Establish `h0 : jE (X.seg C0 CE1 CE2 j) ju i.val = 0`. Unfold `jE`. Rewrite using `[dif_neg (by omega)]`.

Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree. Both sides reduce to the same expression.
-/
theorem nb_oEff (i : Fin (segS X.TT j)) :
    oEff (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
  simp only [oEff, segmentBlockOfMonomial]
  split_ifs with h
  · have h0 : jE (X.seg C0 CE1 CE2 j) ju i.val = 0 := by
      unfold jE
      rw [dif_neg (by omega)]
    rw [h0]
    ring
  · rfl

/- English proof (translation)
Unfold `blockOrd nuSeg`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[nb_oEff, Fin.sum_univ_succ]`. Establish `e1` using `nb_sum_mod_div (fun c : Fin X.m => A ((topOdd X j i, true), c.succ)) ((X.seg C0 CE1 CE2 j).P X.p i)`.

Establish `e2` using `Nat.mod_add_div (A ((topOdd X j i, false), 0)) ((X.seg C0 CE1 CE2 j).P X.p i)`. Simplify using `only [Fin.succ_ne_zero, if_false, if_true, segmentBlockOfMonomial, y0A, ezA] at e1 e2 ⊢`. Simplify using `only [Fin.val_zero, Fin.val_succ, Nat.add_one_ne_zero, if_true, if_false, zero_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nb_ord :
    blockOrd X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) = nuSeg C0 CE1 CE2 X j ju jp du A := by
  unfold blockOrd nuSeg
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nb_oEff, Fin.sum_univ_succ]
  have e1 := nb_sum_mod_div (fun c : Fin X.m => A ((topOdd X j i, true), c.succ)) ((X.seg C0 CE1 CE2 j).P X.p i)
  have e2 := Nat.mod_add_div (A ((topOdd X j i, false), 0)) ((X.seg C0 CE1 CE2 j).P X.p i)
  simp only [Fin.succ_ne_zero, if_false, if_true, segmentBlockOfMonomial, y0A, ezA] at e1 e2 ⊢
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_one_ne_zero, if_true, if_false, zero_add]
  linarith

/- English proof (translation)
Take `⟨hlt, -, -⟩` from `hd`. Use `le_trans (Finset.sum_le_sum fun c _ => ?_) h` and prove the remaining obligations. Conclude with `nb_q_le _ _ _ _ (hlt i c.succ).1 (Nat.div_mul_le_self _ _)`.
-/
theorem nb_ez_le (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (i : Fin (segS X.TT j))
    (h : ∑ c : Fin X.m, (A ((topOdd X j i, true), c.succ) - b.rz i c.succ) ≤ Qe) :
    ∑ c, ezA C0 CE1 CE2 X j A i c ≤ Qe := by
  obtain ⟨hlt, -, -⟩ := hd
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) h
  exact nb_q_le _ _ _ _ (hlt i c.succ).1 (Nat.div_mul_le_self _ _)

/- English proof (translation)
Establish `hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i` using `nb_Ppos C0 CE1 CE2 X j hp i`. Establish `hr` using `(hd.1 i 0).2`. Apply `nb_div_le _ _ _ hP` to reduce the goal to its premises. Establish `: Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i` using `Nat.le_mul_of_pos_right Qe hP`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem block_y_zero_le_of_bound (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (hQ : 1 ≤ Qe) (i : Fin (segS X.TT j)) (t : ℕ)
    (h : A ((topOdd X j i, false), 0) ≤ b.ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i * t + Qe) :
    y0A C0 CE1 CE2 X j A i ≤ t + Qe := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  have hr := (hd.1 i 0).2
  apply nb_div_le _ _ _ hP
  have : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i := Nat.le_mul_of_pos_right Qe hP
  nlinarith

/- English proof (translation)
Establish `hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i` using `nb_Ppos C0 CE1 CE2 X j hp i`. Establish `hr` using `(hd.1 i 0).2`. Establish `hq : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i` using `Nat.le_mul_of_pos_right Qe hP`. Establish `a1 : y0A C0 CE1 CE2 X j A i ≤ Qe`. Apply `nb_div_le _ _ _ hP` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `a2 : Qe ≤ z0A C0 CE1 CE2 X j A i`. Unfold `z0A`. Rewrite using `[Nat.le_div_iff_mul_le hP]`. Use the polynomial consequences of the given equalities and inequalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem block_y_zero_le_z_zero (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (Qe : ℕ) (hQ : 1 ≤ Qe) (i : Fin (segS X.TT j)) (D : ℕ)
    (hD : 1 + 2 * Qe ≤ D)
    (h1 : b.rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i * D ≤ A ((topOdd X j i, true), 0) + Qe)
    (h2 : A ((topOdd X j i, false), 0) ≤ b.ry i 0 + Qe) :
    y0A C0 CE1 CE2 X j A i ≤ z0A C0 CE1 CE2 X j A i := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  have hr := (hd.1 i 0).2
  have hq : Qe ≤ Qe * (X.seg C0 CE1 CE2 j).P X.p i := Nat.le_mul_of_pos_right Qe hP
  have a1 : y0A C0 CE1 CE2 X j A i ≤ Qe := by
    apply nb_div_le _ _ _ hP
    nlinarith
  have a2 : Qe ≤ z0A C0 CE1 CE2 X j A i := by
    unfold z0A
    rw [Nat.le_div_iff_mul_le hP]
    nlinarith
  omega

/- English proof (translation)
Establish `hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i` using `nb_Ppos C0 CE1 CE2 X j hp i`. Use `set P := (X.seg C0 CE1 CE2 j).P X.p i with hPdef`. Use `set B := (X.seg C0 CE1 CE2 j).bTop i`. Establish `hy : ∑ c : Fin (X.m + 1), (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c ≤ (X.m + 1) * P`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [segmentBlockOfMonomial]`. Conclude with `(Nat.mod_lt _ hP).le`. Use `_ = (X.m + 1) * P := by simp`. Unfold `coarseA`. Rewrite using `[← hPdef]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem nb_coarseA_ge (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m) (i : Fin (segS X.TT j)) :
    coarseA X.p (X.seg C0 CE1 CE2 j) b i ≤
      coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i + (X.m + 1) := by
  have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := nb_Ppos C0 CE1 CE2 X j hp i
  set P := (X.seg C0 CE1 CE2 j).P X.p i with hPdef
  set B := (X.seg C0 CE1 CE2 j).bTop i
  have hy : ∑ c : Fin (X.m + 1), (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c ≤ (X.m + 1) * P := by
    calc _ ≤ ∑ _c : Fin (X.m + 1), P := Finset.sum_le_sum fun c _ => by
            simp only [segmentBlockOfMonomial]
            exact (Nat.mod_lt _ hP).le
      _ = (X.m + 1) * P := by simp
  unfold coarseA
  rw [← hPdef]
  calc (B - ∑ c, b.rz i c) / P ≤ B / P := Nat.div_le_div_right (Nat.sub_le _ _)
    _ ≤ (B - ∑ c, (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).rz i c + (X.m + 1) * P) / P :=
        Nat.div_le_div_right (by omega)
    _ = _ := Nat.add_mul_div_right _ _ hP

end NB

end Formalism.MainNotions.ColumnSystems.Pf
