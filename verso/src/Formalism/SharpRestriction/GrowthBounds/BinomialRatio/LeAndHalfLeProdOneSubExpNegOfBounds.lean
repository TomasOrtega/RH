import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

/- English proof (translation)
Establish `hk0 : 0 < k` using `by linarith`. Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hkQ0 : 0 < k * Q` using `mul_pos hk0 hQ0`. Establish `h1 : m * (k * Q * Y) ≤ b'` using `(le_div_iff₀ (mul_pos hkQ0 hY0)).mp hm`.

Establish `h2 : m * (k * Q) ≤ b'`. Establish `: m * (k * Q) * 1 ≤ m * (k * Q) * Y` using `mul_le_mul_of_nonneg_left hY (mul_nonneg hm0 hkQ0.le)`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : k * Q ≤ b'`. Establish `hk2 : 1 ≤ k ^ 2` using `by nlinarith`.

Establish `: k * Q * 1 ≤ k * Q * k ^ 2` using `mul_le_mul_of_nonneg_left hk2 hkQ0.le`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : M * (k * Q) ≤ 2 * b'`. Establish `: M * (k * Q) ≤ (m + 1) * (k * Q)` using `mul_le_mul_of_nonneg_right hM.le hkQ0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : 120 * b' ≤ a`. Establish `e1 : 5 ≤ k * Y` using `by nlinarith`. Establish `e2 : 120 ≤ k * Y * La` using `by nlinarith`. Establish `: 120 * b' ≤ k * Y * La * b'` using `mul_le_mul_of_nonneg_right e2 hb.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h6 : a ≤ A0 * (2 * Q)` using `(div_le_iff₀ (by linarith)).mp hA0`. Establish `hA0pos : 0 < A0`. Establish `: 0 < A0 * (2 * Q)` using `by linarith`. Assume the negation of the conclusion as `hneg`. Establish `hle : A0 ≤ 0` using `not_lt.mp hneg`.

Establish `: A0 * (2 * Q) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hle (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion. Rewrite using `[le_div_iff₀ hk0]`. Establish `e1 : 24 ≤ N1 * La` using `by nlinarith`.

Establish `e2 : A0 * 24 ≤ A0 * (N1 * La)` using `mul_le_mul_of_nonneg_left e1 hA0pos.le`. Establish `e3 : (M * k) * Q ≤ (A0 * N1 * La) * Q`. Establish `: A0 * 24 * Q ≤ A0 * (N1 * La) * Q` using `mul_le_mul_of_nonneg_right e2 hQ0.le`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_mul_le_mul_right e3 hQ0`.

Establish `hx : (k - 1) * M / A0 ≤ 1 / 30`. Rewrite using `[div_le_iff₀ hA0pos]`. Establish `e1 : (k - 1) * M ≤ k * M` using `by nlinarith`. Establish `e3 : (k * M) * Q ≤ (1 / 30 * A0) * Q` using `by nlinarith`. Use `le_of_mul_le_mul_right e3 hQ0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `he1 : Real.exp (-La / 8) ≤ 1 / 4`. Establish `a1 : Real.exp (-La / 8) ≤ Real.exp (-3)` using `Real.exp_le_exp.mpr (by linarith)`. Establish `a2 : (4 : ℝ) ≤ Real.exp 3` using `by have := Real.add_one_le_exp (3 : ℝ); linarith`. Establish `a3 : Real.exp (-3) = (Real.exp 3)⁻¹` using `Real.exp_neg 3`.

Establish `a4 : (Real.exp 3)⁻¹ ≤ (4 : ℝ)⁻¹` using `inv_anti₀ (by norm_num) a2`. Rewrite `a1` using `[a3]`. Combine the linear relations using `[a1, a4, (by norm_num : (4 : ℝ)⁻¹ = 1 / 4)]`. Establish `he2 : Real.exp (-La / 3) ≤ 1 / 9`. Establish `a1 : Real.exp (-La / 3) ≤ Real.exp (-8)` using `Real.exp_le_exp.mpr (by linarith)`.

Establish `a2 : (9 : ℝ) ≤ Real.exp 8` using `by have := Real.add_one_le_exp (8 : ℝ); linarith`. Establish `a3 : Real.exp (-8) = (Real.exp 8)⁻¹` using `Real.exp_neg 8`. Establish `a4 : (Real.exp 8)⁻¹ ≤ (9 : ℝ)⁻¹` using `inv_anti₀ (by norm_num) a2`. Rewrite `a1` using `[a3]`. Combine the linear relations using `[a1, a4, (by norm_num : (9 : ℝ)⁻¹ = 1 / 9)]`.

Establish `u1 : 3 / 4 ≤ 1 - Real.exp (-La / 8)` using `by linarith`. Establish `u2 : 8 / 9 ≤ 1 - Real.exp (-La / 3)` using `by linarith`. Establish `u3 : 29 / 30 ≤ 1 - (k - 1) * M / A0` using `by linarith`. Establish `v1 : (3 / 4 : ℝ) * (8 / 9) ≤ (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3))` using `mul_le_mul u1 u2 (by norm_num) (by linarith)`. Establish `v2 : (3 / 4 : ℝ) * (8 / 9) * (29 / 30) ≤ (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) * (1 - (k - 1) * M / A0)` using `mul_le_mul v1 u3 (by norm_num) (by linarith)`.

Combine the linear relations using `[v2, (by norm_num : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) * (8 / 9) * (29 / 30))]`.
-/
theorem le_and_half_le_prod_one_sub_exp_neg_of_bounds {a b' k Q Y La N1 A0 m M : ℝ} (hk : 5 ≤ k) (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hN1 : 1 ≤ N1) (hLa : 24 ≤ La)
    (hb : 0 < b') (hab : k * Y * La * b' ≤ a) (hkQ : k ^ 3 * Q ≤ b') (hA0 : a / (2 * Q) ≤ A0) (hm0 : 0 ≤ m)
    (hm : m ≤ b' / (k * Q * Y)) (hM0 : 0 ≤ M) (hM : M < m + 1) :
    M ≤ A0 * N1 * La / k ∧
      1 / 2 ≤ (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) * (1 - (k - 1) * M / A0) := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hY0 : 0 < Y := by linarith
  have hkQ0 : 0 < k * Q := mul_pos hk0 hQ0

  have h1 : m * (k * Q * Y) ≤ b' := (le_div_iff₀ (mul_pos hkQ0 hY0)).mp hm
  have h2 : m * (k * Q) ≤ b' := by
    have : m * (k * Q) * 1 ≤ m * (k * Q) * Y := mul_le_mul_of_nonneg_left hY (mul_nonneg hm0 hkQ0.le)
    nlinarith

  have h3 : k * Q ≤ b' := by
    have hk2 : 1 ≤ k ^ 2 := by nlinarith
    have : k * Q * 1 ≤ k * Q * k ^ 2 := mul_le_mul_of_nonneg_left hk2 hkQ0.le
    nlinarith
  have h4 : M * (k * Q) ≤ 2 * b' := by
    have : M * (k * Q) ≤ (m + 1) * (k * Q) := mul_le_mul_of_nonneg_right hM.le hkQ0.le
    linarith

  have h5 : 120 * b' ≤ a := by
    have e1 : 5 ≤ k * Y := by nlinarith
    have e2 : 120 ≤ k * Y * La := by nlinarith
    have : 120 * b' ≤ k * Y * La * b' := mul_le_mul_of_nonneg_right e2 hb.le
    linarith
  have h6 : a ≤ A0 * (2 * Q) := (div_le_iff₀ (by linarith)).mp hA0
  have hA0pos : 0 < A0 := by
    have : 0 < A0 * (2 * Q) := by linarith
    by_contra hneg
    have hle : A0 ≤ 0 := not_lt.mp hneg
    have : A0 * (2 * Q) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
    linarith
  constructor
  · rw [le_div_iff₀ hk0]
    have e1 : 24 ≤ N1 * La := by nlinarith
    have e2 : A0 * 24 ≤ A0 * (N1 * La) := mul_le_mul_of_nonneg_left e1 hA0pos.le
    have e3 : (M * k) * Q ≤ (A0 * N1 * La) * Q := by
      have : A0 * 24 * Q ≤ A0 * (N1 * La) * Q := mul_le_mul_of_nonneg_right e2 hQ0.le
      nlinarith
    exact le_of_mul_le_mul_right e3 hQ0
  · have hx : (k - 1) * M / A0 ≤ 1 / 30 := by
      rw [div_le_iff₀ hA0pos]
      have e1 : (k - 1) * M ≤ k * M := by nlinarith
      have e3 : (k * M) * Q ≤ (1 / 30 * A0) * Q := by nlinarith
      have := le_of_mul_le_mul_right e3 hQ0
      linarith
    have he1 : Real.exp (-La / 8) ≤ 1 / 4 := by
      have a1 : Real.exp (-La / 8) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
      have a2 : (4 : ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp (3 : ℝ); linarith
      have a3 : Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
      have a4 : (Real.exp 3)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) a2
      rw [a3] at a1
      linarith [a1, a4, (by norm_num : (4 : ℝ)⁻¹ = 1 / 4)]
    have he2 : Real.exp (-La / 3) ≤ 1 / 9 := by
      have a1 : Real.exp (-La / 3) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by linarith)
      have a2 : (9 : ℝ) ≤ Real.exp 8 := by have := Real.add_one_le_exp (8 : ℝ); linarith
      have a3 : Real.exp (-8) = (Real.exp 8)⁻¹ := Real.exp_neg 8
      have a4 : (Real.exp 8)⁻¹ ≤ (9 : ℝ)⁻¹ := inv_anti₀ (by norm_num) a2
      rw [a3] at a1
      linarith [a1, a4, (by norm_num : (9 : ℝ)⁻¹ = 1 / 9)]
    have u1 : 3 / 4 ≤ 1 - Real.exp (-La / 8) := by linarith
    have u2 : 8 / 9 ≤ 1 - Real.exp (-La / 3) := by linarith
    have u3 : 29 / 30 ≤ 1 - (k - 1) * M / A0 := by linarith
    have v1 : (3 / 4 : ℝ) * (8 / 9) ≤ (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) :=
      mul_le_mul u1 u2 (by norm_num) (by linarith)
    have v2 : (3 / 4 : ℝ) * (8 / 9) * (29 / 30) ≤
        (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) * (1 - (k - 1) * M / A0) :=
      mul_le_mul v1 u3 (by norm_num) (by linarith)
    linarith [v2, (by norm_num : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) * (8 / 9) * (29 / 30))]

section Plug

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

/- English proof (translation)
Establish `hA : (X.seg C0 CE1 CE2 j).A0 X.p = ⌊((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ)⌋` using `rfl`. Rewrite using `[hA]`. Establish `hp1` using `h.p1`. Establish `ha` using `h.apos`. Establish `hQ1` using `h.Q1`.

Establish `hQ0 : 0 < X.Q` using `by linarith`. Establish `hQj1 : (1 : ℝ) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ)`. Use `push_cast`. Conclude with `one_le_pow₀ hp1`. Establish `hQj0 : (0 : ℝ) < ((X.p ^ segG X.TT j : ℕ) : ℝ)` using `by linarith`.

Establish `hQjQ : ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q`. Use `push_cast`. Conclude with `pow_le_pow_right₀ hp1 (h.segB j).1`. Establish `hε : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1 / 240`. Establish `h1` using `h.LaK`.

Establish `h2` using `h.de6`. Establish `: 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k)` using `by ring`. Rewrite `h1` using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN5 : X.E0 C0 CE1 CE2 + X.Q ≤ (X.a : ℝ) / 240`.

Establish `h1` using `h.N5`. Establish `h2 : X.E0 C0 CE1 CE2 / X.a + X.Q / X.a = (X.E0 C0 CE1 CE2 + X.Q) / X.a` using `by ring`. Rewrite `h1` using `[h2]`. Establish `h3 : (X.E0 C0 CE1 CE2 + X.Q) / X.a ≤ 1 / 240` using `le_trans h1 hε`. Use `(div_le_iff₀ ha).mp h3` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnum : 0 ≤ (X.a : ℝ) - X.E0 C0 CE1 CE2` using `by linarith`. Establish `h1 : ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ)` using `div_le_div_of_nonneg_left hnum hQj0 hQjQ`. Establish `h2` using `Int.sub_one_lt_floor (((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ))`. Establish `h3 : (X.a : ℝ) / (2 * X.Q) ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q - 1`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `: (((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q - 1) * (2 * X.Q) = 2 * ((X.a : ℝ) - X.E0 C0 CE1 CE2 - X.Q)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Std.half_ratio_le_segment_base_of_std (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT)) :
    (X.a : ℝ) / (2 * X.Q) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
  have hA : (X.seg C0 CE1 CE2 j).A0 X.p =
      ⌊((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ)⌋ := rfl
  rw [hA]
  have hp1 := h.p1
  have ha := h.apos
  have hQ1 := h.Q1
  have hQ0 : 0 < X.Q := by linarith
  have hQj1 : (1 : ℝ) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ) := by
    push_cast
    exact one_le_pow₀ hp1
  have hQj0 : (0 : ℝ) < ((X.p ^ segG X.TT j : ℕ) : ℝ) := by linarith
  have hQjQ : ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q := by
    push_cast
    exact pow_le_pow_right₀ hp1 (h.segB j).1
  have hε : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1 / 240 := by
    have h1 := h.LaK
    have h2 := h.de6
    have : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
    rw [this] at h1
    linarith
  have hN5 : X.E0 C0 CE1 CE2 + X.Q ≤ (X.a : ℝ) / 240 := by
    have h1 := h.N5
    have h2 : X.E0 C0 CE1 CE2 / X.a + X.Q / X.a = (X.E0 C0 CE1 CE2 + X.Q) / X.a := by ring
    rw [h2] at h1
    have h3 : (X.E0 C0 CE1 CE2 + X.Q) / X.a ≤ 1 / 240 := le_trans h1 hε
    have := (div_le_iff₀ ha).mp h3
    linarith
  have hnum : 0 ≤ (X.a : ℝ) - X.E0 C0 CE1 CE2 := by linarith
  have h1 : ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q ≤
      ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left hnum hQj0 hQjQ
  have h2 := Int.sub_one_lt_floor (((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ))
  have h3 : (X.a : ℝ) / (2 * X.Q) ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q - 1 := by
    rw [div_le_iff₀ (by linarith)]
    have : (((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q - 1) * (2 * X.Q) =
        2 * ((X.a : ℝ) - X.E0 C0 CE1 CE2 - X.Q) := by
      field_simp
    rw [this]
    linarith
  linarith

/- English proof (translation)
Establish `h1` using `h.loga`. Establish `h2` using `h.one_le_level_alt`. Unfold `Loc.La lambdaScale`. Establish `h3 : (1 : ℝ) ≤ (X.N1 : ℝ) ^ 2` using `by nlinarith`. Establish `h4 : C0 * 1 ≤ C0 * (X.N1 : ℝ) ^ 2` using `mul_le_mul_of_nonneg_left h3 hC0`.

Establish `h5 : C0 * (X.N1 : ℝ) ^ 2 * 1 ≤ C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a` using `mul_le_mul_of_nonneg_left h1 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Std.La_ge (h : Std C0 Cde CE1 CE2 H X) (hC0 : 0 ≤ C0) : C0 ≤ X.La C0 := by
  have h1 := h.loga
  have h2 := h.one_le_level_alt
  unfold Loc.La lambdaScale
  have h3 : (1 : ℝ) ≤ (X.N1 : ℝ) ^ 2 := by nlinarith
  have h4 : C0 * 1 ≤ C0 * (X.N1 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hC0
  have h5 : C0 * (X.N1 : ℝ) ^ 2 * 1 ≤ C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

end Plug

/- English proof (translation)
Establish `hS : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => 24 ≤ C0 ∧ ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X` using `TransportedAlt.of_explicit (fun _ => 24) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 h24 h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => ⟨h24, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩`. Use `TransportedAlt.mono ?_ ((hS.and hU).and hL)` and prove the remaining obligations. Introduce and unpack `C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨h24, hstd⟩, up⟩, low⟩`. Introduce `X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hSet hH hc j m hm0 hmM rz ry hd`. Establish `hD1 : D1num X` using `⟨hSet.1.prime, hSet.1.five_le, hSet.1.two_le, hSet.1.even⟩`.

Establish `hs` using `hstd X hD1 hH hc`. Establish `hLa : 24 ≤ X.La C0` using `le_trans h24 (hs.La_ge (by linarith))`. Establish `hcore` using `le_and_half_le_prod_one_sub_exp_neg_of_bounds (M := ((⌈m⌉₊ : ℕ) : ℝ)) hs.k5 hs.Q1 hs.Y1 hs.one_le_level_alt hLa hs.bpos hs.kYLab (hs.kQ le_rfl) (hs.half_ratio_le_segment_base_of_std j) hm0 hmM (Nat.cast_nonneg _) (Nat.ceil_lt_add_one hm0)`. Use `⟨?_, up X W Qq O Kf ι σ jO w hSet hH hc j m hm0 rz ry hd⟩` and prove the remaining obligations. Establish `hlow` using `low X W Qq O Kf ι σ jO w hSet hH hc j m hm0 hcore.1 rz ry hd`.

Establish `hfac : 1 / 2 ≤ lowFac C0 CE1 CE2 X j ⌈m⌉₊`. Establish `hkm : (X.m : ℝ) = X.k - 1` using `by unfold Loc.k; ring`. Unfold `lowFac`. Rewrite using `[hkm]`. Conclude with `hcore.2`.

Establish `hmm : (0 : ℝ) ≤ (mmB C0 CE1 CE2 X j rz ry : ℝ)` using `Nat.cast_nonneg _`. Establish `h1 : 1 / 2 * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ)` using `mul_le_mul_of_nonneg_right hfac hmm`. Establish `h2 : (mmB C0 CE1 CE2 X j rz ry : ℝ) / 2 ≤ (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℝ)` using `by linarith`. Conclude with `h2`.
-/
theorem one_segment_of_upper_lower {D : Formalism.BasicNotions.D7} (hU : RestUp) (hL : RestLow) : RootMultiplicityTwoBeyond D := by
  have hS : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => 24 ≤ C0 ∧
      ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
    TransportedAlt.of_explicit (fun _ => 24) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
      fun _ _ _ _ _ _ _ _ _ _ hCc hC0 h24 h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
        ⟨h24, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩
  refine TransportedAlt.mono ?_ ((hS.and hU).and hL)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨h24, hstd⟩, up⟩, low⟩
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hSet hH hc j m hm0 hmM rz ry hd
  have hD1 : D1num X := ⟨hSet.1.prime, hSet.1.five_le, hSet.1.two_le, hSet.1.even⟩
  have hs := hstd X hD1 hH hc
  have hLa : 24 ≤ X.La C0 := le_trans h24 (hs.La_ge (by linarith))
  have hcore := le_and_half_le_prod_one_sub_exp_neg_of_bounds (M := ((⌈m⌉₊ : ℕ) : ℝ)) hs.k5 hs.Q1 hs.Y1 hs.one_le_level_alt hLa hs.bpos hs.kYLab (hs.kQ le_rfl) (hs.half_ratio_le_segment_base_of_std j)
    hm0 hmM (Nat.cast_nonneg _) (Nat.ceil_lt_add_one hm0)
  refine ⟨?_, up X W Qq O Kf ι σ jO w hSet hH hc j m hm0 rz ry hd⟩
  have hlow := low X W Qq O Kf ι σ jO w hSet hH hc j m hm0 hcore.1 rz ry hd
  have hfac : 1 / 2 ≤ lowFac C0 CE1 CE2 X j ⌈m⌉₊ := by
    have hkm : (X.m : ℝ) = X.k - 1 := by unfold Loc.k; ring
    unfold lowFac
    rw [hkm]
    exact hcore.2
  have hmm : (0 : ℝ) ≤ (mmB C0 CE1 CE2 X j rz ry : ℝ) := Nat.cast_nonneg _
  have h1 : 1 / 2 * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ) :=
    mul_le_mul_of_nonneg_right hfac hmm
  have h2 : (mmB C0 CE1 CE2 X j rz ry : ℝ) / 2 ≤ (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℝ) := by linarith
  exact h2

end Formalism.MainNotions.ColumnSystems.Pf
