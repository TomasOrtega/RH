import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section Follow

variable {s r A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ d ih`.

Introduce `hd`. Establish `h0` using `ih (by omega)`. Establish `hv` using `(wb_vstep hP (2 * (i + d) + 3) (by omega) (Or.inr (by omega))).1 (r - 1 - d) (by omega)`. Establish `hc` using `(wb_cstep hP (2 * (i + d) + 4) (by omega) (by omega)).2 (r - 1 - (d + 1)) (by omega)`. Establish `e1 : 2 * (i + d) + 3 + 1 = 2 * (i + d) + 4` using `rfl`.

Establish `e2 : r - 1 - (d + 1) + 1 = r - 1 - d` using `by omega`. Establish `e3 : 2 * (i + d) + 4 + 1 = 2 * (i + (d + 1)) + 3` using `by ring`. Rewrite `hv` using `[e1]`. Rewrite `hc` using `[e2, e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nu_follow (hP : IsPair A Ai Ci mu lam) (hr : s ≤ r) (i : ℕ) :
    ∀ d : ℕ, i + d < s → wbK mu (2 * i + 3) (r - 1) ≤ wbK mu (2 * (i + d) + 3) (r - 1 - d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h0 := ih (by omega)
    have hv := (wb_vstep hP (2 * (i + d) + 3) (by omega) (Or.inr (by omega))).1 (r - 1 - d) (by omega)
    have hc := (wb_cstep hP (2 * (i + d) + 4) (by omega) (by omega)).2 (r - 1 - (d + 1)) (by omega)
    have e1 : 2 * (i + d) + 3 + 1 = 2 * (i + d) + 4 := rfl
    have e2 : r - 1 - (d + 1) + 1 = r - 1 - d := by omega
    have e3 : 2 * (i + d) + 4 + 1 = 2 * (i + (d + 1)) + 3 := by ring
    rw [e1] at hv
    rw [e2, e3] at hc
    linarith

/- English proof (translation)
Establish `hf` using `nu_follow hP hr i (s - 1 - i) (by omega)`. Establish `e : 2 * (i + (s - 1 - i)) + 3 = 2 * s + 1` using `by omega`. Rewrite `hf` using `[e, wb_last _ (by omega)]`. Establish `hI` using `(hP.2 ⟨r - 1 - (s - 1 - i), by omega⟩).1`. Establish `e2 : (⟨r - 1 - (s - 1 - i), by omega⟩ : Fin r).succ = ⟨r - 1 - (s - 1 - i) + 1, by omega⟩` using `rfl`.

Rewrite `hI` using `[e2]`. Unfold `pairN`. Rewrite using `[dif_pos (by omega)]`. Establish `e3 : (⟨r - s + i, by omega⟩ : Fin r) = ⟨r - 1 - (s - 1 - i), by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e3]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nu_le_last (hP : IsPair A Ai Ci mu lam) (hr : s ≤ r) (i : ℕ) (hi : i < s) :
    pairN (s := s) lam i ≤ -wbK mu (2 * i + 3) (r - 1) := by
  have hf := nu_follow hP hr i (s - 1 - i) (by omega)
  have e : 2 * (i + (s - 1 - i)) + 3 = 2 * s + 1 := by omega
  rw [e, wb_last _ (by omega)] at hf
  have hI := (hP.2 ⟨r - 1 - (s - 1 - i), by omega⟩).1
  have e2 : (⟨r - 1 - (s - 1 - i), by omega⟩ : Fin r).succ = ⟨r - 1 - (s - 1 - i) + 1, by omega⟩ := rfl
  rw [e2] at hI
  unfold pairN
  rw [dif_pos (by omega)]
  have e3 : (⟨r - s + i, by omega⟩ : Fin r) = ⟨r - 1 - (s - 1 - i), by omega⟩ := Fin.ext (by simp; omega)
  rw [e3]
  linarith

/- English proof (translation)
Establish `hm` using `pf_mass hP.1 (i + 1) (by omega)`. Establish `e : (⟨2 * (i + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * i + 3, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite `hm` using `[e]`. Establish `hw : wbK mu (2 * i + 3) (r - 1) = mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ`. Unfold `wbK`.

Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression. Rewrite using `[hw]`. Establish `h1 : -(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ) ≤ max 0 (-(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ))` using `le_max_right _ _`. Establish `h2 : max 0 (-(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ)) ≤ pfMass (fun t : Fin r => mu ⟨2 * i + 3, by omega⟩ t.succ)`.

Unfold `pfMass`. Conclude with `Finset.single_le_sum (f := fun t : Fin r => max 0 (-(mu ⟨2 * i + 3, by omega⟩ t.succ))) (fun t _ => le_max_left _ _) (Finset.mem_univ _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem last_ge_mass (hP : IsPair A Ai Ci mu lam) (hr : 1 ≤ r) (i : ℕ) (hi : i < s) :
    -wbK mu (2 * i + 3) (r - 1) ≤ ∑ x : Fin s, if x.val < i + 1 then (Ci x : ℤ) else 0 := by
  have hm := pf_mass hP.1 (i + 1) (by omega)
  have e : (⟨2 * (i + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * i + 3, by omega⟩ := Fin.ext (by simp; omega)
  rw [e] at hm
  have hw : wbK mu (2 * i + 3) (r - 1) = mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ := by
    unfold wbK
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  rw [hw]
  have h1 : -(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ) ≤
      max 0 (-(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ)) := le_max_right _ _
  have h2 : max 0 (-(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ)) ≤
      pfMass (fun t : Fin r => mu ⟨2 * i + 3, by omega⟩ t.succ) := by
    unfold pfMass
    exact Finset.single_le_sum (f := fun t : Fin r => max 0 (-(mu ⟨2 * i + 3, by omega⟩ t.succ)))
      (fun t _ => le_max_left _ _) (Finset.mem_univ _)
  linarith

end Follow

/- English proof (translation)
Establish `hm` using `dist_strictMono X.TT j (show l < l' from Fin.lt_def.mpr (by omega))`. Establish `ho1` using `dist_odd hs.nEven X.TT j l`. Establish `ho2` using `dist_odd hs.nEven X.TT j l'`. Establish `hlt` using `(dist_pos_lt X.TT j l').2`. Take `⟨k1, hk1⟩` from `ho1`.

Take `⟨k2, hk2⟩` from `ho2`. Establish `hdd : (segDists X.TT j).get l + 2 ≤ (segDists X.TT j).get l'` using `by omega`. Use `set P := X.p ^ (segG X.TT j - (segDists X.TT j).get l) with hP`. Use `set P' := X.p ^ (segG X.TT j - (segDists X.TT j).get l') with hP'`. Establish `hp1 : 1 ≤ X.p` using `by have := hs.p5; omega`.

Establish `hPP : X.p ^ 2 * P' ≤ P`. Rewrite using `[hP, hP', ← pow_add]`. Conclude with `Nat.pow_le_pow_right hp1 (by omega)`. Establish `hPPr : (X.p : ℝ) ^ 2 * (P' : ℝ) ≤ (P : ℝ)` using `by exact_mod_cast hPP`. Take `⟨hP0, -, -, hQ, hPQ⟩` from `hs.levels j l`.

Take `⟨hP0', -, -, -, hPQ'⟩` from `hs.levels j l'`. Establish `cb` using `coarse_bounds (X.aT (segPos X.TT j l)) P (ry l) (fun c => (hd.1 l c).2) (hd.2.2 l).1 (hd.2.2 l).2`. Establish `cb'` using `coarse_bounds (X.aT (segPos X.TT j l')) P' (ry l') (fun c => (hd.1 l' c).2) (hd.2.2 l').1 (hd.2.2 l').2`. Establish `wa` using `hs.winA _ (pos_mem X.TT j l).1`. Establish `wa'` using `hs.winA _ (pos_mem X.TT j l').1`.

Establish `hk5` using `hs.k5`. Establish `hkQ` using `hs.kQ hH`. Establish `hb` using `hs.bpos`. Establish `hY` using `hs.Y1`. Establish `eC : (clC C0 CE1 CE2 X j rz ry l : ℝ) = (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ)` using `rfl`.

Establish `eC' : (clC C0 CE1 CE2 X j rz ry l' : ℝ) = (((X.aT (segPos X.TT j l') - ∑ c, ry l' c) / P' : ℕ) : ℝ)` using `rfl`. Rewrite using `[eC, eC']`. Establish `hC0 : (0 : ℝ) ≤ (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Generalize the expression as in `(((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) = C at cb hC0 ⊢`. Generalize the expression as in `(((X.aT (segPos X.TT j l') - ∑ c, ry l' c) / P' : ℕ) : ℝ) = C' at cb' ⊢`.

Establish `hkk : ((X.m : ℝ) + 1) = X.k` using `rfl`. Rewrite `cb'` using `[hkk]`. Establish `hk0 : (0 : ℝ) < X.k` using `by linarith`. Establish `hkP : X.k * (P' : ℝ) ≤ X.b' / 25`. Establish `h1 : X.k * (P' : ℝ) ≤ X.k * X.Q` using `mul_le_mul_of_nonneg_left (le_trans hPQ' hQ) hk0.le`.

Establish `hQ1` using `hs.Q1`. Establish `h3 : 25 * (X.k * X.Q) ≤ X.k ^ 3 * X.Q`. Establish `h25 : (25 : ℝ) ≤ X.k ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ X.Q)) (by linarith : (0:ℝ) ≤ X.k ^ 2 - 25)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ha0 : (0 : ℝ) ≤ X.a` using `by linarith [wa.1, (Nat.cast_nonneg _ : (0:ℝ) ≤ (X.aT (segPos X.TT j l) : ℝ))]`. Establish `hwin : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) ≤ X.a * (7 / 5)`. Establish `: 2 / (X.k * X.Y) ≤ 2 / 5`. Apply `div_le_div_of_nonneg_left (by norm_num) (by norm_num)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities. Establish `e1 : (X.p : ℝ) ^ 2 * C * P' ≤ X.a * (7 / 5)`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (X.a : ℝ) - X.k * P' < C' * P'` using `lt_of_le_of_lt (sub_le_sub_right wa'.1 _) cb'.2`. Establish `hP'pos : (0 : ℝ) < P'` using `hP0'`.

Establish `hab : X.b' ≤ (X.a : ℝ)`. Establish `h1` using `hs.pab`. Establish `h5 : (5 : ℝ) ≤ (X.p : ℝ)` using `by exact_mod_cast hs.p5`. Rewrite `h1` using `[lt_div_iff₀ hb]`. Establish `h6 : (1 : ℝ) * X.b' ≤ (X.p : ℝ) * X.b'` using `mul_le_mul_of_nonneg_right (by linarith only [h5]) hb.le`.

Combine the linear relations using `only [h1, h6]`. Establish `key : (X.p : ℝ) ^ 2 * C * P' ≤ 2 * C' * P'` using `by linarith only [e1, e2, hkP, hab]`. Conclude with `le_of_mul_le_mul_right key hP'pos`.
-/
theorem coarse_threshold_ratio_consecutive {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (hs : Std C0 Cde CE1 CE2 H X) (hH : 1 ≤ H) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry))
    (l l' : Fin (segS X.TT j)) (hll : l.val + 1 = l'.val) :
    (X.p : ℝ) ^ 2 * (clC C0 CE1 CE2 X j rz ry l : ℝ) ≤ 2 * (clC C0 CE1 CE2 X j rz ry l' : ℝ) := by
  have hm := dist_strictMono X.TT j (show l < l' from Fin.lt_def.mpr (by omega))
  have ho1 := dist_odd hs.nEven X.TT j l
  have ho2 := dist_odd hs.nEven X.TT j l'
  have hlt := (dist_pos_lt X.TT j l').2
  obtain ⟨k1, hk1⟩ := ho1
  obtain ⟨k2, hk2⟩ := ho2
  have hdd : (segDists X.TT j).get l + 2 ≤ (segDists X.TT j).get l' := by omega
  set P := X.p ^ (segG X.TT j - (segDists X.TT j).get l) with hP
  set P' := X.p ^ (segG X.TT j - (segDists X.TT j).get l') with hP'
  have hp1 : 1 ≤ X.p := by have := hs.p5; omega
  have hPP : X.p ^ 2 * P' ≤ P := by
    rw [hP, hP', ← pow_add]
    exact Nat.pow_le_pow_right hp1 (by omega)
  have hPPr : (X.p : ℝ) ^ 2 * (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPP
  obtain ⟨hP0, -, -, hQ, hPQ⟩ := hs.levels j l
  obtain ⟨hP0', -, -, -, hPQ'⟩ := hs.levels j l'
  have cb := coarse_bounds (X.aT (segPos X.TT j l)) P (ry l) (fun c => (hd.1 l c).2) (hd.2.2 l).1 (hd.2.2 l).2
  have cb' := coarse_bounds (X.aT (segPos X.TT j l')) P' (ry l') (fun c => (hd.1 l' c).2) (hd.2.2 l').1 (hd.2.2 l').2
  have wa := hs.winA _ (pos_mem X.TT j l).1
  have wa' := hs.winA _ (pos_mem X.TT j l').1
  have hk5 := hs.k5
  have hkQ := hs.kQ hH
  have hb := hs.bpos
  have hY := hs.Y1
  have eC : (clC C0 CE1 CE2 X j rz ry l : ℝ) = (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) := rfl
  have eC' : (clC C0 CE1 CE2 X j rz ry l' : ℝ) = (((X.aT (segPos X.TT j l') - ∑ c, ry l' c) / P' : ℕ) : ℝ) := rfl
  rw [eC, eC']
  have hC0 : (0 : ℝ) ≤ (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) = C at cb hC0 ⊢
  generalize (((X.aT (segPos X.TT j l') - ∑ c, ry l' c) / P' : ℕ) : ℝ) = C' at cb' ⊢
  have hkk : ((X.m : ℝ) + 1) = X.k := rfl
  rw [hkk] at cb'
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hkP : X.k * (P' : ℝ) ≤ X.b' / 25 := by
    have h1 : X.k * (P' : ℝ) ≤ X.k * X.Q := mul_le_mul_of_nonneg_left (le_trans hPQ' hQ) hk0.le
    have hQ1 := hs.Q1
    have h3 : 25 * (X.k * X.Q) ≤ X.k ^ 3 * X.Q := by
      have h25 : (25 : ℝ) ≤ X.k ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ X.Q)) (by linarith : (0:ℝ) ≤ X.k ^ 2 - 25)]
    linarith
  have ha0 : (0 : ℝ) ≤ X.a := by linarith [wa.1, (Nat.cast_nonneg _ : (0:ℝ) ≤ (X.aT (segPos X.TT j l) : ℝ))]
  have hwin : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) ≤ X.a * (7 / 5) := by
    have : 2 / (X.k * X.Y) ≤ 2 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    nlinarith
  have e1 : (X.p : ℝ) ^ 2 * C * P' ≤ X.a * (7 / 5) := by
    calc (X.p : ℝ) ^ 2 * C * P' = C * ((X.p : ℝ) ^ 2 * P') := by ring
      _ ≤ C * P := mul_le_mul_of_nonneg_left hPPr hC0
      _ ≤ _ := le_trans cb.1 (le_trans wa.2 hwin)
  have e2 : (X.a : ℝ) - X.k * P' < C' * P' := lt_of_le_of_lt (sub_le_sub_right wa'.1 _) cb'.2
  have hP'pos : (0 : ℝ) < P' := hP0'
  have hab : X.b' ≤ (X.a : ℝ) := by
    have h1 := hs.pab
    have h5 : (5 : ℝ) ≤ (X.p : ℝ) := by exact_mod_cast hs.p5
    rw [lt_div_iff₀ hb] at h1
    have h6 : (1 : ℝ) * X.b' ≤ (X.p : ℝ) * X.b' := mul_le_mul_of_nonneg_right (by linarith only [h5]) hb.le
    linarith only [h1, h6]
  have key : (X.p : ℝ) ^ 2 * C * P' ≤ 2 * C' * P' := by linarith only [e1, e2, hkP, hab]
  exact le_of_mul_le_mul_right key hP'pos

/- English proof (translation)
Establish `hp : (25 : ℝ) ≤ (X.p : ℝ) ^ 2`. Establish `: (5 : ℝ) ≤ X.p` using `by exact_mod_cast hs.p5`. Use the polynomial consequences of the given equalities and inequalities. Introduce `⟨i, hi⟩`. Proceed by induction on `i with`.

Consider the case `zero`. Simplify using `only [Nat.not_lt_zero, if_false, Finset.sum_const_zero]`. Check the signs of the components of the expression. Consider the case `succ i ih`. Establish `ih'` using `ih (by omega)`.

Establish `hstep` using `coarse_threshold_ratio_consecutive hs hH j rz ry hd ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl`. Establish `e : (∑ l : Fin (segS X.TT j), if l.val < i + 1 then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (∑ l : Fin (segS X.TT j), if l.val < i then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) + (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ)`. Establish `h2 : (∑ l : Fin (segS X.TT j), if l = (⟨i, by omega⟩ : Fin (segS X.TT j)) then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ)` using `by simp`. Rewrite using `[← h2, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h1 : l.val < i`. Rewrite using `[if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring`. Distinguish the cases in `h3 : l.val = i`. Rewrite using `[if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring`. Rewrite using `[if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring`.

Rewrite using `[e]`. Establish `hC : (0 : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ)` using `Nat.cast_nonneg _`. Establish `hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2` using `by linarith`. Rewrite `ih'`, the goal using `[div_eq_mul_inv]`. Establish `hinv : (X.p : ℝ) ^ 2 * ((X.p : ℝ) ^ 2)⁻¹ = 1` using `mul_inv_cancel₀ hp0.ne'`.

Establish `hinv0 : ((X.p : ℝ) ^ 2)⁻¹ ≤ 1 / 25`. Rewrite using `[one_div]; exact inv_anti₀ (by norm_num) hp`. Use polynomial arithmetic with `[inv_pos.mpr hp0]`.
-/
theorem coarse_threshold_prefix_sum {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (hs : Std C0 Cde CE1 CE2 H X) (hH : 1 ≤ H) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry)) :
    ∀ i : Fin (segS X.TT j), (∑ l : Fin (segS X.TT j), if l.val < i.val then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) ≤
      4 * (clC C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 := by
  have hp : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ X.p := by exact_mod_cast hs.p5
    nlinarith
  intro ⟨i, hi⟩
  induction i with
  | zero =>
    simp only [Nat.not_lt_zero, if_false, Finset.sum_const_zero]
    positivity
  | succ i ih =>
    have ih' := ih (by omega)
    have hstep := coarse_threshold_ratio_consecutive hs hH j rz ry hd ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
    have e : (∑ l : Fin (segS X.TT j), if l.val < i + 1 then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) =
        (∑ l : Fin (segS X.TT j), if l.val < i then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) +
          (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := by
      have h2 : (∑ l : Fin (segS X.TT j), if l = (⟨i, by omega⟩ : Fin (segS X.TT j)) then
          (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := by simp
      rw [← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h1 : l.val < i
      · rw [if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring
      · by_cases h3 : l.val = i
        · rw [if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring
        · rw [if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring
    rw [e]
    have hC : (0 : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2 := by linarith
    rw [div_eq_mul_inv] at ih' ⊢
    have hinv : (X.p : ℝ) ^ 2 * ((X.p : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    have hinv0 : ((X.p : ℝ) ^ 2)⁻¹ ≤ 1 / 25 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp
    nlinarith [inv_pos.mpr hp0]

/- English proof (translation)
Introduce `X _ hD hI hc j rz ry hd A _ _ mu lam hP i`. Establish `hs` using `hstd X hD hI hc`. Establish `hroom : segS X.TT j ≤ X.m`. Establish `h1` using `(hs.segB j).2`. Establish `h2` using `hs.N1k`.

Establish `h3 : (2 * (X.N1 : ℝ) + 3 : ℝ) ≤ (X.m : ℝ) + 1` using `h2`. Establish `: 2 * X.N1 + 3 ≤ X.m + 1` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Establish `hr1 : 1 ≤ X.m` using `by have := i.2; omega`. Establish `h1` using `nu_le_last hP hroom i.val i.2`.

Establish `h2` using `last_ge_mass hP hr1 i.val i.2`. Establish `h3` using `coarse_threshold_prefix_sum hs le_rfl j rz ry hd i`. Establish `e : (∑ x : Fin (segS X.TT j), if x.val < i.val + 1 then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) = (∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) + (clC C0 CE1 CE2 X j rz ry i : ℤ)`. Establish `h2 : (∑ x : Fin (segS X.TT j), if x = i then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) = (clC C0 CE1 CE2 X j rz ry i : ℤ)` using `by simp`. Rewrite using `[← h2, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : x.val < i.val`. Rewrite using `[if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring`. Distinguish the cases in `h3 : x.val = i.val`. Rewrite using `[if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring`.

Rewrite using `[if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring`. Rewrite `h2` using `[e]`. Establish `hcast : ((∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0 : ℤ) : ℝ) = ∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℝ) else 0`. Use `push_cast`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h4 : ((pairN (s` using `segS X.TT j) lam i : ℤ) : ℝ) ≤ (∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℝ) else 0) + (clC C0 CE1 CE2 X j rz ry i : ℝ) := by`. Rewrite using `[← hcast]`. Conclude with `le_trans h1 h2` after adjusting the coercions. Establish `hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2` using `pow_pos (by exact_mod_cast (show 0 < X.p by have := hs.p5; omega)) 2`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem nUp_of_std {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    NUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A _ _ mu lam hP i
  have hs := hstd X hD hI hc
  have hroom : segS X.TT j ≤ X.m := by
    have h1 := (hs.segB j).2
    have h2 := hs.N1k
    have h3 : (2 * (X.N1 : ℝ) + 3 : ℝ) ≤ (X.m : ℝ) + 1 := h2
    have : 2 * X.N1 + 3 ≤ X.m + 1 := by exact_mod_cast h3
    omega
  have hr1 : 1 ≤ X.m := by have := i.2; omega
  have h1 := nu_le_last hP hroom i.val i.2
  have h2 := last_ge_mass hP hr1 i.val i.2
  have h3 := coarse_threshold_prefix_sum hs le_rfl j rz ry hd i
  have e : (∑ x : Fin (segS X.TT j), if x.val < i.val + 1 then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) =
      (∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) +
        (clC C0 CE1 CE2 X j rz ry i : ℤ) := by
    have h2 : (∑ x : Fin (segS X.TT j), if x = i then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) =
        (clC C0 CE1 CE2 X j rz ry i : ℤ) := by simp
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : x.val < i.val
    · rw [if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring
    · by_cases h3 : x.val = i.val
      · rw [if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring
      · rw [if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring
  rw [e] at h2
  have hcast : ((∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0 : ℤ) : ℝ) =
      ∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℝ) else 0 := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have h4 : ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤
      (∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℝ) else 0) +
        (clC C0 CE1 CE2 X j rz ry i : ℝ) := by
    rw [← hcast]
    exact_mod_cast le_trans h1 h2
  have hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2 := pow_pos (by exact_mod_cast (show 0 < X.p by have := hs.p5; omega)) 2
  calc ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ 4 * (clC C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 +
        (clC C0 CE1 CE2 X j rz ry i : ℝ) := by linarith
    _ = (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) := by field_simp; ring

/- English proof (translation)
The claim follows from `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => nUp_of_std fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc`.
-/
theorem restNUp : RestNUp :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      nUp_of_std fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

end Formalism.MainNotions.ColumnSystems.Pf
