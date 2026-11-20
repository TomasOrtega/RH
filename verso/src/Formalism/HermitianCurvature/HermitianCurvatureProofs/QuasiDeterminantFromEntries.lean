import Formalism.HermitianCurvature.StatementFr
import Formalism.YangianSpanCharacter.YangianRelationFirst

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring`.
-/
private theorem transpose_mul_J_mul_apply {A : Type*} [Ring A] (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (Mᵀ * Formalism.YangianSpanCharacter.T.J A * N) i j = M 0 i * N 1 j - M 1 i * N 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring

/- English proof (translation)
Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring`.
-/
private theorem mul_J_mul_transpose_apply' {A : Type*} [Ring A] (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (M * Formalism.YangianSpanCharacter.T.J A * Nᵀ) i j = M i 0 * N j 1 - M i 1 * N j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] <;> first | abel | noncomm_ring

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S h Y hY hY1`. Take `⟨-, -, h3, h4, -, -⟩` from `h`. Establish `e` using `congrFun (congrFun (h3 Y) 1) 1`. Establish `e0 : (q Y • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0` using `by simp [Formalism.YangianSpanCharacter.T.J]`. Rewrite `e` using `[mul_J_mul_transpose_apply', e0, sub_eq_zero]`.

Unfold `lf`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[(h4 (Y + 1) hY1).1, mul_one]`. Use `_ = τinv Y * (t Y 1 0 * t (Y + 1) 1 1) * τinv (Y + 1) := by simp only [mul_assoc]`. Use `_ = τinv Y * (t Y 1 1 * t (Y + 1) 1 0) * τinv (Y + 1) := by rw [e]`.

Use `_ = τinv Y * t Y 1 1 * t (Y + 1) 1 0 * τinv (Y + 1) := by simp only [mul_assoc]`. Use `_ = t (Y + 1) 1 0 * τinv (Y + 1) := by rw [(h4 Y hY).2, one_mul]`.
-/
theorem l_shift_from_determinant : LShift := by
  intro 𝕜 A _ _ _ t τinv q S h Y hY hY1
  obtain ⟨-, -, h3, h4, -, -⟩ := h
  have e := congrFun (congrFun (h3 Y) 1) 1
  have e0 : (q Y • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0 := by simp [Formalism.YangianSpanCharacter.T.J]
  rw [mul_J_mul_transpose_apply', e0, sub_eq_zero] at e
  unfold lf
  calc τinv Y * t Y 1 0 = τinv Y * t Y 1 0 * (t (Y + 1) 1 1 * τinv (Y + 1)) := by
        rw [(h4 (Y + 1) hY1).1, mul_one]
    _ = τinv Y * (t Y 1 0 * t (Y + 1) 1 1) * τinv (Y + 1) := by simp only [mul_assoc]
    _ = τinv Y * (t Y 1 1 * t (Y + 1) 1 0) * τinv (Y + 1) := by rw [e]
    _ = τinv Y * t Y 1 1 * t (Y + 1) 1 0 * τinv (Y + 1) := by simp only [mul_assoc]
    _ = t (Y + 1) 1 0 * τinv (Y + 1) := by rw [(h4 Y hY).2, one_mul]

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S h Y hY hY1`. Take `⟨-, h2, -, h4, -, -⟩` from `h`. Establish `H` using `h2 (Y - 1)`. Rewrite `H` using `[sub_add_cancel]`. Establish `e01` using `congrFun (congrFun H 0) 1`.

Establish `e11` using `congrFun (congrFun H 1) 1`. Establish `c01 : (q (Y - 1) • Formalism.YangianSpanCharacter.T.J A) 0 1 = q (Y - 1) • (1 : A)` using `by simp [Formalism.YangianSpanCharacter.T.J]`. Establish `c11 : (q (Y - 1) • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0` using `by simp [Formalism.YangianSpanCharacter.T.J]`. Rewrite `e01` using `[transpose_mul_J_mul_apply, c01]`. Rewrite `e11` using `[transpose_mul_J_mul_apply, c11, sub_eq_zero]`.

Establish `hs : t (Y - 1) 0 1 = τinv Y * t Y 0 1 * t (Y - 1) 1 1`. Rewrite using `[mul_assoc, e11, ← mul_assoc, (h4 Y hY).2, one_mul]`. Establish `key : (t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1) * t (Y - 1) 1 1 = q (Y - 1) • (1 : A)`. Rewrite using `[← e01, hs]`. Use `noncomm_ring`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc _ (t (Y - 1) 1 1), (h4 (Y - 1) hY1).1, mul_one]`. Use `_ = q (Y - 1) • τinv (Y - 1) := by rw [key, smul_mul_assoc, one_mul]`.
-/
theorem quasi_determinant_from_entries : QuasiDetT := by
  intro 𝕜 A _ _ _ t τinv q S h Y hY hY1
  obtain ⟨-, h2, -, h4, -, -⟩ := h
  have H := h2 (Y - 1)
  rw [sub_add_cancel] at H
  have e01 := congrFun (congrFun H 0) 1
  have e11 := congrFun (congrFun H 1) 1
  have c01 : (q (Y - 1) • Formalism.YangianSpanCharacter.T.J A) 0 1 = q (Y - 1) • (1 : A) := by simp [Formalism.YangianSpanCharacter.T.J]
  have c11 : (q (Y - 1) • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0 := by simp [Formalism.YangianSpanCharacter.T.J]
  rw [transpose_mul_J_mul_apply, c01] at e01
  rw [transpose_mul_J_mul_apply, c11, sub_eq_zero] at e11
  have hs : t (Y - 1) 0 1 = τinv Y * t Y 0 1 * t (Y - 1) 1 1 := by
    rw [mul_assoc, e11, ← mul_assoc, (h4 Y hY).2, one_mul]
  have key : (t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1) * t (Y - 1) 1 1 = q (Y - 1) • (1 : A) := by
    rw [← e01, hs]
    noncomm_ring
  calc t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1
      = (t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1) * t (Y - 1) 1 1 * τinv (Y - 1) := by
        rw [mul_assoc _ (t (Y - 1) 1 1), (h4 (Y - 1) hY1).1, mul_one]
    _ = q (Y - 1) • τinv (Y - 1) := by rw [key, smul_mul_assoc, one_mul]

/- English proof (translation)
Introduce `𝕜 A _ _ _ t τinv q S h Y hY hY1`. Establish `h'` using `h`. Take `⟨-, -, -, h4, -, -⟩` from `h'`. Establish `hY' : Y - 1 + 1 ∈ S` using `by rw [sub_add_cancel]; exact hY`. Establish `hl` using `l_shift_from_determinant 𝕜 A t τinv q S h (Y - 1) hY1 hY'`.

Rewrite `hl` using `[sub_add_cancel]`. Establish `hB : lf t τinv (Y - 1) * t Y 1 1 = t Y 1 0`. Rewrite using `[hl, mul_assoc, (h4 Y hY).2, mul_one]`. Establish `hC : t Y 1 1 * mf t τinv Y = t Y 0 1`. Unfold `mf`.

Rewrite using `[← mul_assoc, (h4 Y hY).1, one_mul]`. Establish `hA : q (Y - 1) • τinv (Y - 1) + lf t τinv (Y - 1) * t Y 1 1 * mf t τinv Y = t Y 0 0`. Rewrite using `[hB, ← quasi_determinant_from_entries 𝕜 A t τinv q S h Y hY hY1]`. Unfold `mf`. Use `noncomm_ring`.

Rewrite using `[Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.eta_fin_two (t Y)ᵀ]`. Simplify using `only [Matrix.transpose_apply, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]`. Rewrite using `[hA, hB, hC]`.
-/
theorem gauss_decomp_minus_letter : GaussMinus := by
  intro 𝕜 A _ _ _ t τinv q S h Y hY hY1
  have h' := h
  obtain ⟨-, -, -, h4, -, -⟩ := h'
  have hY' : Y - 1 + 1 ∈ S := by rw [sub_add_cancel]; exact hY
  have hl := l_shift_from_determinant 𝕜 A t τinv q S h (Y - 1) hY1 hY'
  rw [sub_add_cancel] at hl
  have hB : lf t τinv (Y - 1) * t Y 1 1 = t Y 1 0 := by
    rw [hl, mul_assoc, (h4 Y hY).2, mul_one]
  have hC : t Y 1 1 * mf t τinv Y = t Y 0 1 := by
    unfold mf
    rw [← mul_assoc, (h4 Y hY).1, one_mul]
  have hA : q (Y - 1) • τinv (Y - 1) + lf t τinv (Y - 1) * t Y 1 1 * mf t τinv Y = t Y 0 0 := by
    rw [hB, ← quasi_determinant_from_entries 𝕜 A t τinv q S h Y hY hY1]
    unfold mf
    noncomm_ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.eta_fin_two (t Y)ᵀ]
  simp only [Matrix.transpose_apply, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
  rw [hA, hB, hC]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases l <;>`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.E1, Formalism.YangianSpanCharacter.T.E2]`.
-/
private theorem e1_mul_e2_apply {B : Type*} [Ring B] (X Y : Matrix (Fin 2) (Fin 2) B) (a b j l : Fin 2) :
    (Formalism.YangianSpanCharacter.T.E1 X * Formalism.YangianSpanCharacter.T.E2 Y) (a, b) (j, l) = X a j * Y b l := by
  fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.E1, Formalism.YangianSpanCharacter.T.E2]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases l <;>`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.E1, Formalism.YangianSpanCharacter.T.E2]`.
-/
private theorem e2_mul_e1_apply {B : Type*} [Ring B] (X Y : Matrix (Fin 2) (Fin 2) B) (a b j l : Fin 2) :
    (Formalism.YangianSpanCharacter.T.E2 Y * Formalism.YangianSpanCharacter.T.E1 X) (a, b) (j, l) = Y b l * X a j := by
  fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.E1, Formalism.YangianSpanCharacter.T.E2]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases k <;>`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Pf]`.
-/
private theorem pf_mul_apply {B : Type*} [Ring B] (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B)
    (i k j l : Fin 2) : (Formalism.YangianSpanCharacter.T.Pf B * N) (i, k) (j, l) = N (k, i) (j, l) := by
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Pf]

/- English proof (translation)
Apply the tactic sequence `fin_cases j <;> fin_cases l <;>`. Simplify using `[Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Pf]`.
-/
private theorem mul_pf_apply {B : Type*} [Ring B] (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B)
    (i k j l : Fin 2) : (N * Formalism.YangianSpanCharacter.T.Pf B) (i, k) (j, l) = N (i, k) (l, j) := by
  fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Pf]

/- English proof (translation)
Introduce `K B _ _ _ M v u hR i j k l`. Establish `h` using `congrFun (congrFun hR (i, k)) (j, l)`. Rewrite `h` using `[mul_assoc, sub_mul, smul_mul_assoc, one_mul, Matrix.sub_apply, Matrix.smul_apply, e1_mul_e2_apply, pf_mul_apply, e1_mul_e2_apply]`. Rewrite `h` using `[mul_sub, mul_smul_comm, mul_one, Matrix.sub_apply, Matrix.smul_apply, e2_mul_e1_apply, mul_pf_apply, e2_mul_e1_apply]`. Rewrite using `[smul_sub, sub_eq_sub_iff_sub_eq_sub]`.

Conclude with `h`.
-/
theorem rtt_relation_entries : RTTEntries := by
  intro K B _ _ _ M v u hR i j k l
  have h := congrFun (congrFun hR (i, k)) (j, l)
  rw [mul_assoc, sub_mul, smul_mul_assoc, one_mul, Matrix.sub_apply, Matrix.smul_apply,
    e1_mul_e2_apply, pf_mul_apply, e1_mul_e2_apply] at h
  rw [mul_sub, mul_smul_comm, mul_one, Matrix.sub_apply, Matrix.smul_apply,
    e2_mul_e1_apply, mul_pf_apply, e2_mul_e1_apply] at h
  rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
  exact h

/- English proof (translation)
Introduce `𝕜 A _ _ _ _ t τinv q S RR h hRR Y hY hY1 hst`. Take `⟨-, h2, -, h4, -, -⟩` from `h`. Establish `H` using `congrFun (congrFun (h2 Y) 1) 1`. Establish `c11 : (q Y • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0` using `by simp [Formalism.YangianSpanCharacter.T.J]`. Rewrite `H` using `[transpose_mul_J_mul_apply, c11, sub_eq_zero]`.

Establish `hm : mf t τinv (Y + 1) = t Y 0 1 * τinv Y`. Unfold `mf`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc (τinv (Y + 1)), mul_assoc, (h4 Y hY).1, mul_one]`. Use `_ = t Y 0 1 * τinv Y := by`.

Rewrite using `[H, ← mul_assoc, (h4 (Y + 1) hY1).2, one_mul]`. Establish `s11 : star (t Y 1 1) * RR = RR * t Y 1 1`. Use `hst 1 1` as an intermediate fact. Rewrite `this` using `[star_mul, hRR]`. Then use the resulting hypothesis. Establish `s10 : star (t Y 1 0) * RR = RR * t Y 0 1`.

Use `hst 1 0` as an intermediate fact. Rewrite `this` using `[star_mul, hRR]`. Then use the resulting hypothesis. Establish `sτ : star (τinv Y) * RR = RR * τinv Y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc (star (τinv Y)), mul_assoc RR, (h4 Y hY).1, mul_one]`.

Use `_ = star (t Y 1 1 * τinv Y) * RR * τinv Y := by`. Rewrite using `[← s11, star_mul]`. Use `noncomm_ring`. Use `_ = RR * τinv Y := by rw [(h4 Y hY).1, star_one, one_mul]`. Rewrite using `[hm]`.

Unfold `lf`. Rewrite using `[star_mul, mul_assoc, sτ, ← mul_assoc (star (t Y 1 0)), s10, mul_assoc]`.
-/
theorem adjoint_l_shift_relation : AdjL := by
  intro 𝕜 A _ _ _ _ t τinv q S RR h hRR Y hY hY1 hst
  obtain ⟨-, h2, -, h4, -, -⟩ := h
  have H := congrFun (congrFun (h2 Y) 1) 1
  have c11 : (q Y • Formalism.YangianSpanCharacter.T.J A) 1 1 = 0 := by simp [Formalism.YangianSpanCharacter.T.J]
  rw [transpose_mul_J_mul_apply, c11, sub_eq_zero] at H
  have hm : mf t τinv (Y + 1) = t Y 0 1 * τinv Y := by
    unfold mf
    calc τinv (Y + 1) * t (Y + 1) 0 1 = τinv (Y + 1) * (t (Y + 1) 0 1 * t Y 1 1) * τinv Y := by
          rw [mul_assoc (τinv (Y + 1)), mul_assoc, (h4 Y hY).1, mul_one]
      _ = t Y 0 1 * τinv Y := by
          rw [H, ← mul_assoc, (h4 (Y + 1) hY1).2, one_mul]
  have s11 : star (t Y 1 1) * RR = RR * t Y 1 1 := by
    have := hst 1 1
    rwa [star_mul, hRR] at this
  have s10 : star (t Y 1 0) * RR = RR * t Y 0 1 := by
    have := hst 1 0
    rwa [star_mul, hRR] at this
  have sτ : star (τinv Y) * RR = RR * τinv Y := by
    calc star (τinv Y) * RR = star (τinv Y) * (RR * t Y 1 1) * τinv Y := by
          rw [mul_assoc (star (τinv Y)), mul_assoc RR, (h4 Y hY).1, mul_one]
      _ = star (t Y 1 1 * τinv Y) * RR * τinv Y := by
          rw [← s11, star_mul]
          noncomm_ring
      _ = RR * τinv Y := by rw [(h4 Y hY).1, star_one, one_mul]
  rw [hm]
  unfold lf
  rw [star_mul, mul_assoc, sτ, ← mul_assoc (star (t Y 1 0)), s10, mul_assoc]

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L f Y Ya hY`. Establish `hc : Y - Ya ≠ 0` using `sub_ne_zero.mpr hY`. Establish `hio : ∀ (c : ℂ) (x : A), (Matrix.scalar (Ix S) (c • x) : SlopeTestRemainingChoices S A) = c • Matrix.scalar (Ix S) x`. Introduce `c x`. Use extensionality with `i j`.

Apply the tactic sequence `simp [Matrix.scalar_apply, Matrix.diagonal_apply, smul_ite] <;> split_ifs <;> simp`. Establish `hl0 : L.l0 Y - L.l0 Ya = -((Y - Ya) • (L.ζb * L.GGi))`. Simplify using `only [Formalism.FourierDecayAlt.R.LevelData.l0, ← Algebra.smul_def, sub_smul, add_smul]`. Normalize the expressions using the abelian group laws. Simplify using `only [Formalism.FourierDecayAlt.Fr.FrameData.l, Formalism.FourierDecayAlt.Fr.FrameData.DD, Formalism.FourierDecayAlt.Fr.kapL, io]`.

Establish `e : Matrix.scalar (Ix S) (L.l0 Y) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * f.ee Y - (Matrix.scalar (Ix S) (L.l0 Ya) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * f.ee Ya) = Matrix.scalar (Ix S) (L.l0 Y - L.l0 Ya) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * (f.ee Y - f.e …`. Rewrite using `[map_sub, mul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hl0, map_neg, hio, smul_add, mul_smul_comm, smul_neg, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem divided_difference_l : EtaLevel := by
  intro A S _ _ _ _ _ _ r L f Y Ya hY
  have hc : Y - Ya ≠ 0 := sub_ne_zero.mpr hY
  have hio : ∀ (c : ℂ) (x : A),
      (Matrix.scalar (Ix S) (c • x) : SlopeTestRemainingChoices S A) = c • Matrix.scalar (Ix S) x := by
    intro c x
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, smul_ite] <;> split_ifs <;> simp
  have hl0 : L.l0 Y - L.l0 Ya = -((Y - Ya) • (L.ζb * L.GGi)) := by
    simp only [Formalism.FourierDecayAlt.R.LevelData.l0, ← Algebra.smul_def, sub_smul, add_smul]
    abel
  simp only [Formalism.FourierDecayAlt.Fr.FrameData.l, Formalism.FourierDecayAlt.Fr.FrameData.DD, Formalism.FourierDecayAlt.Fr.kapL, io]
  have e : Matrix.scalar (Ix S) (L.l0 Y) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * f.ee Y -
      (Matrix.scalar (Ix S) (L.l0 Ya) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * f.ee Ya) =
      Matrix.scalar (Ix S) (L.l0 Y - L.l0 Ya) +
        Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * (f.ee Y - f.ee Ya) := by
    rw [map_sub, mul_sub]
    abel
  rw [e, hl0, map_neg, hio, smul_add, mul_smul_comm, smul_neg, smul_smul, inv_mul_cancel₀ hc, one_smul]

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L f hf`. Establish `hGGi : L.GGi ∈ zfns L` using `by simp [zfns]`. Establish `hGG : L.GG ∈ zfns L` using `by simp [zfns]`. Establish `hio_mul : ∀ a b : A, (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b` using `fun a b => by`. Simplify using `only [io, map_mul]`.

Establish `hio_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1` using `by simp only [io, map_one]`. Establish `hGG1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1` using `by rw [← hio_mul, L.GG_GGi, hio_one]`. Establish `hGG2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1` using `by rw [← hio_mul, L.GGi_GG, hio_one]`. Establish `hFFi` using `hf.F_Fi`. Establish `hFiF` using `hf.Fi_F`.

Establish `hc_mul : ∀ a b : SlopeTestRemainingChoices S A, f.F * a * f.Fi * (f.F * b * f.Fi) = f.F * (a * b) * f.Fi`. Introduce `a b`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = f.F * (a * b) * f.Fi := by rw [hFiF, mul_one, mul_assoc f.F]`.

Establish `hT : ∀ Y ∈ f.reg, f.hatT Y = (f.TT Y).map (fun b => f.F * b * f.Fi)`. Introduce `Y hY`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.hatT`. Rewrite using `[if_pos hY]`. Establish `hT0 : ∀ Y, Y ∉ f.reg → f.hatT Y = 0`.

Introduce `Y hY`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.hatT`. Rewrite using `[if_neg hY]`. Establish `hτ11 : ∀ Y ∈ f.reg, f.hatT Y 1 1 = io L.GG * f.x Y`. Introduce `Y hY`.

Rewrite using `[hT Y hY, Matrix.map_apply, hf.frame_τ Y hY, mul_assoc, hFFi, mul_one]`. Establish `hxiG : ∀ Y ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi Y) (io g)`. Introduce `Y hY g hg`. Establish `hx` using `hf.x_fn Y g hg`. Take `⟨h1, h2⟩` from `hf.x_xi Y hY`.

Use `show f.xi Y * io g = io g * f.xi Y`. Combine the equalities or inequalities in the displayed calculation. Establish `hq : ∀ Y, Y ∈ f.reg → Y + 1 ∈ f.reg → f.hatQ Y = f.q Y`. Introduce `Y h1 h2`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.hatQ`.

Rewrite using `[if_pos ⟨h1, h2⟩]`. Establish `hq0 : ∀ Y, ¬ (Y ∈ f.reg ∧ Y + 1 ∈ f.reg) → f.hatQ Y = 0`. Introduce `Y h`. Unfold `Formalism.FourierDecayAlt.Fr.FrameData.hatQ`. Rewrite using `[if_neg h]`.

Establish `hJ : ∀ i j : Fin 2, f.F * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j * f.Fi = Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j`. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, hFFi]`. Establish `h1 : ∀ (u v : ℂ) (i j k l : Fin 2), (u - v) • (f.hatT u i j * f.hatT v k l - f.hatT v k l * f.hatT u i j) = f.hatT u k j * f.hatT v i l - f.hatT v k j * f.hatT u i l`. Introduce `u v i j k l`.

Distinguish the cases in `hu : u ∈ f.reg`. Distinguish the cases in `hv : v ∈ f.reg`. Establish `hR` using `rtt_relation_entries ℂ (SlopeTestRemainingChoices S A) f.TT v u (hf.module.rtt v hv u hu) i j k l`. Simplify using `only [hT u hu, hT v hv, Matrix.map_apply, hc_mul]`. Simplify using `only [← sub_mul, ← mul_sub]`.

Rewrite using `[← smul_mul_assoc, ← mul_smul_comm, hR]`. Simplify using `[hT0 v hv]`. Simplify using `[hT0 u hu]`. Establish `h2 : ∀ Y, (f.hatT (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * f.hatT Y = f.hatQ Y • Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)`. Introduce `Y`.

Distinguish the cases in `hY : Y ∈ f.reg ∧ Y + 1 ∈ f.reg`. Rewrite using `[hq Y hY.1 hY.2]`. Establish `hD` using `(hf.module.det Y hY.1 hY.2).1`. Use extensionality with `i j : 1`. Establish `e` using `congrFun (congrFun hD i) j`.

Rewrite `e`, the goal using `[transpose_mul_J_mul_apply]`. Rewrite using `[hT Y hY.1, hT (Y + 1) hY.2]`. Simplify using `only [Matrix.map_apply, hc_mul]`. Simplify using `only [← sub_mul, ← mul_sub]`. Rewrite using `[e]`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hJ]`. Rewrite using `[hq0 Y hY, zero_smul]`. Distinguish the cases in `h1 : Y ∈ f.reg`. Establish `h2' : Y + 1 ∉ f.reg` using `fun h => hY ⟨h1, h⟩`.

Rewrite using `[hT0 _ h2']`. Simplify using the standard rewrite rules. Rewrite using `[hT0 _ h1]`. Simplify using the standard rewrite rules. Establish `h3 : ∀ Y, f.hatT Y * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (f.hatT (Y + 1))ᵀ = f.hatQ Y • Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)`.

Introduce `Y`. Distinguish the cases in `hY : Y ∈ f.reg ∧ Y + 1 ∈ f.reg`. Rewrite using `[hq Y hY.1 hY.2]`. Establish `hD` using `(hf.module.det Y hY.1 hY.2).2`. Use extensionality with `i j : 1`.

Establish `e` using `congrFun (congrFun hD i) j`. Rewrite `e`, the goal using `[mul_J_mul_transpose_apply']`. Rewrite using `[hT Y hY.1, hT (Y + 1) hY.2]`. Simplify using `only [Matrix.map_apply, hc_mul]`. Simplify using `only [← sub_mul, ← mul_sub]`.

Rewrite using `[e]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hJ]`. Rewrite using `[hq0 Y hY, zero_smul]`. Distinguish the cases in `h1 : Y ∈ f.reg`.

Establish `h2' : Y + 1 ∉ f.reg` using `fun h => hY ⟨h1, h⟩`. Rewrite using `[hT0 _ h2']`. Simplify using the standard rewrite rules. Rewrite using `[hT0 _ h1]`. Simplify using the standard rewrite rules.

Establish `h4 : ∀ u ∈ f.inv, f.hatT u 1 1 * (io L.GGi * f.xi u) = 1 ∧ io L.GGi * f.xi u * f.hatT u 1 1 = 1`. Introduce `u hu`. Rewrite using `[hτ11 u (hf.inv_reg hu)]`. Take `⟨hx1, hx2⟩` from `hf.x_xi u hu`. Establish `hc1` using `(hf.x_fn u L.GGi hGGi).eq`.

Establish `hc2` using `(hxiG u hu L.GG hGG).eq`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = io L.GG * (io L.GGi * f.x u) * f.xi u := by rw [hc1]`.

Use `_ = (io L.GG * io L.GGi) * (f.x u * f.xi u) := by simp only [mul_assoc]`. Use `_ = 1 := by rw [hGG1, hx1, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = io L.GGi * (io L.GG * f.xi u) * f.x u := by rw [hc2]`.

Use `_ = (io L.GGi * io L.GG) * (f.xi u * f.x u) := by simp only [mul_assoc]`. Use `_ = 1 := by rw [hGG2, hx2, one_mul]`. Establish `h5 : ∀ u v, Commute (f.hatT u 1 1) (f.hatT v 1 1)`. Introduce `u v`. Distinguish the cases in `hu : u ∈ f.reg`.

Distinguish the cases in `hv : v ∈ f.reg`. Rewrite using `[hτ11 u hu, hτ11 v hv]`. Establish `hGGx : ∀ w, Commute (io L.GG : SlopeTestRemainingChoices S A) (f.x w)` using `fun w => (hf.x_fn w L.GG hGG).symm`. Conclude with `Commute.mul_left ((Commute.refl _).mul_right (hGGx v)) (((hGGx u).symm).mul_right (hf.x_commute u v))`. Rewrite using `[hT0 v hv]`.

Simplify using the standard rewrite rules. Rewrite using `[hT0 u hu]`. Simplify using the standard rewrite rules. Establish `h6 : ∀ u v, Commute (f.hatT u 1 0) (f.hatT v 1 0)`. Introduce `u v`.

Distinguish the cases in `hu : u ∈ f.reg`. Distinguish the cases in `hv : v ∈ f.reg`. Rewrite using `[hT u hu, hT v hv, Matrix.map_apply, Matrix.map_apply] show _ * _ = _ * _`. Rewrite using `[hc_mul, hc_mul, (hf.lowerLeftEntry_commute u hu v hv).eq]`. Rewrite using `[hT0 v hv]`.

Simplify using the standard rewrite rules. Rewrite using `[hT0 u hu]`. Simplify using the standard rewrite rules. Use `⟨⟨h1, h2, h3, h4, h5, h6⟩, ?_⟩` and prove the remaining obligations. Introduce `Y hY hY1`.

Establish `hr` using `hf.inv_reg hY`. Unfold `lf`. Rewrite using `[hT Y hr, Matrix.map_apply, hf.frame_l Y hY hY1]`. Take `⟨hx1, hx2⟩` from `hf.x_xi Y hY`. Establish `hc2` using `(hxiG Y hY L.GG hGG).eq`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem frame_gives_one_letter_hyps : FrameModHyp := by
  intro A S _ _ _ _ _ _ r L f hf
  have hGGi : L.GGi ∈ zfns L := by simp [zfns]
  have hGG : L.GG ∈ zfns L := by simp [zfns]
  have hio_mul : ∀ a b : A, (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := fun a b => by
    simp only [io, map_mul]
  have hio_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by simp only [io, map_one]
  have hGG1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1 := by rw [← hio_mul, L.GG_GGi, hio_one]
  have hGG2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← hio_mul, L.GGi_GG, hio_one]
  have hFFi := hf.F_Fi
  have hFiF := hf.Fi_F
  have hc_mul : ∀ a b : SlopeTestRemainingChoices S A, f.F * a * f.Fi * (f.F * b * f.Fi) = f.F * (a * b) * f.Fi := by
    intro a b
    calc f.F * a * f.Fi * (f.F * b * f.Fi) = f.F * a * (f.Fi * f.F) * b * f.Fi := by
          simp only [mul_assoc]
      _ = f.F * (a * b) * f.Fi := by rw [hFiF, mul_one, mul_assoc f.F]
  have hT : ∀ Y ∈ f.reg, f.hatT Y = (f.TT Y).map (fun b => f.F * b * f.Fi) := by
    intro Y hY
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatT
    rw [if_pos hY]
  have hT0 : ∀ Y, Y ∉ f.reg → f.hatT Y = 0 := by
    intro Y hY
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatT
    rw [if_neg hY]
  have hτ11 : ∀ Y ∈ f.reg, f.hatT Y 1 1 = io L.GG * f.x Y := by
    intro Y hY
    rw [hT Y hY, Matrix.map_apply, hf.frame_τ Y hY, mul_assoc, hFFi, mul_one]
  have hxiG : ∀ Y ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi Y) (io g) := by
    intro Y hY g hg
    have hx := hf.x_fn Y g hg
    obtain ⟨h1, h2⟩ := hf.x_xi Y hY
    show f.xi Y * io g = io g * f.xi Y
    calc f.xi Y * io g = f.xi Y * io g * (f.x Y * f.xi Y) := by rw [h1, mul_one]
      _ = f.xi Y * (io g * f.x Y) * f.xi Y := by simp only [mul_assoc]
      _ = f.xi Y * (f.x Y * io g) * f.xi Y := by rw [← hx.eq]
      _ = (f.xi Y * f.x Y) * io g * f.xi Y := by simp only [mul_assoc]
      _ = io g * f.xi Y := by rw [h2, one_mul]
  have hq : ∀ Y, Y ∈ f.reg → Y + 1 ∈ f.reg → f.hatQ Y = f.q Y := by
    intro Y h1 h2
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatQ
    rw [if_pos ⟨h1, h2⟩]
  have hq0 : ∀ Y, ¬ (Y ∈ f.reg ∧ Y + 1 ∈ f.reg) → f.hatQ Y = 0 := by
    intro Y h
    unfold Formalism.FourierDecayAlt.Fr.FrameData.hatQ
    rw [if_neg h]
  have hJ : ∀ i j : Fin 2, f.F * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j * f.Fi = Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, hFFi]
  have h1 : ∀ (u v : ℂ) (i j k l : Fin 2),
      (u - v) • (f.hatT u i j * f.hatT v k l - f.hatT v k l * f.hatT u i j) =
        f.hatT u k j * f.hatT v i l - f.hatT v k j * f.hatT u i l := by
    intro u v i j k l
    by_cases hu : u ∈ f.reg
    · by_cases hv : v ∈ f.reg
      · have hR := rtt_relation_entries ℂ (SlopeTestRemainingChoices S A) f.TT v u (hf.module.rtt v hv u hu) i j k l
        simp only [hT u hu, hT v hv, Matrix.map_apply, hc_mul]
        simp only [← sub_mul, ← mul_sub]
        rw [← smul_mul_assoc, ← mul_smul_comm, hR]
      · simp [hT0 v hv]
    · simp [hT0 u hu]
  have h2 : ∀ Y, (f.hatT (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * f.hatT Y =
      f.hatQ Y • Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
    intro Y
    by_cases hY : Y ∈ f.reg ∧ Y + 1 ∈ f.reg
    · rw [hq Y hY.1 hY.2]
      have hD := (hf.module.det Y hY.1 hY.2).1
      ext i j : 1
      have e := congrFun (congrFun hD i) j
      rw [transpose_mul_J_mul_apply] at e ⊢
      rw [hT Y hY.1, hT (Y + 1) hY.2]
      simp only [Matrix.map_apply, hc_mul]
      simp only [← sub_mul, ← mul_sub]
      rw [e]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hJ]
    · rw [hq0 Y hY, zero_smul]
      by_cases h1 : Y ∈ f.reg
      · have h2' : Y + 1 ∉ f.reg := fun h => hY ⟨h1, h⟩
        rw [hT0 _ h2']
        simp
      · rw [hT0 _ h1]
        simp
  have h3 : ∀ Y, f.hatT Y * Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (f.hatT (Y + 1))ᵀ =
      f.hatQ Y • Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
    intro Y
    by_cases hY : Y ∈ f.reg ∧ Y + 1 ∈ f.reg
    · rw [hq Y hY.1 hY.2]
      have hD := (hf.module.det Y hY.1 hY.2).2
      ext i j : 1
      have e := congrFun (congrFun hD i) j
      rw [mul_J_mul_transpose_apply'] at e ⊢
      rw [hT Y hY.1, hT (Y + 1) hY.2]
      simp only [Matrix.map_apply, hc_mul]
      simp only [← sub_mul, ← mul_sub]
      rw [e]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hJ]
    · rw [hq0 Y hY, zero_smul]
      by_cases h1 : Y ∈ f.reg
      · have h2' : Y + 1 ∉ f.reg := fun h => hY ⟨h1, h⟩
        rw [hT0 _ h2']
        simp
      · rw [hT0 _ h1]
        simp
  have h4 : ∀ u ∈ f.inv, f.hatT u 1 1 * (io L.GGi * f.xi u) = 1 ∧
      io L.GGi * f.xi u * f.hatT u 1 1 = 1 := by
    intro u hu
    rw [hτ11 u (hf.inv_reg hu)]
    obtain ⟨hx1, hx2⟩ := hf.x_xi u hu
    have hc1 := (hf.x_fn u L.GGi hGGi).eq
    have hc2 := (hxiG u hu L.GG hGG).eq
    constructor
    · calc io L.GG * f.x u * (io L.GGi * f.xi u) = io L.GG * (f.x u * io L.GGi) * f.xi u := by
            simp only [mul_assoc]
        _ = io L.GG * (io L.GGi * f.x u) * f.xi u := by rw [hc1]
        _ = (io L.GG * io L.GGi) * (f.x u * f.xi u) := by simp only [mul_assoc]
        _ = 1 := by rw [hGG1, hx1, one_mul]
    · calc io L.GGi * f.xi u * (io L.GG * f.x u) = io L.GGi * (f.xi u * io L.GG) * f.x u := by
            simp only [mul_assoc]
        _ = io L.GGi * (io L.GG * f.xi u) * f.x u := by rw [hc2]
        _ = (io L.GGi * io L.GG) * (f.xi u * f.x u) := by simp only [mul_assoc]
        _ = 1 := by rw [hGG2, hx2, one_mul]
  have h5 : ∀ u v, Commute (f.hatT u 1 1) (f.hatT v 1 1) := by
    intro u v
    by_cases hu : u ∈ f.reg
    · by_cases hv : v ∈ f.reg
      · rw [hτ11 u hu, hτ11 v hv]
        have hGGx : ∀ w, Commute (io L.GG : SlopeTestRemainingChoices S A) (f.x w) := fun w => (hf.x_fn w L.GG hGG).symm
        exact Commute.mul_left ((Commute.refl _).mul_right (hGGx v))
          (((hGGx u).symm).mul_right (hf.x_commute u v))
      · rw [hT0 v hv]
        simp
    · rw [hT0 u hu]
      simp
  have h6 : ∀ u v, Commute (f.hatT u 1 0) (f.hatT v 1 0) := by
    intro u v
    by_cases hu : u ∈ f.reg
    · by_cases hv : v ∈ f.reg
      · rw [hT u hu, hT v hv, Matrix.map_apply, Matrix.map_apply]
        show _ * _ = _ * _
        rw [hc_mul, hc_mul, (hf.lowerLeftEntry_commute u hu v hv).eq]
      · rw [hT0 v hv]
        simp
    · rw [hT0 u hu]
      simp
  refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, ?_⟩
  intro Y hY hY1
  have hr := hf.inv_reg hY
  unfold lf
  rw [hT Y hr, Matrix.map_apply, hf.frame_l Y hY hY1]
  obtain ⟨hx1, hx2⟩ := hf.x_xi Y hY
  have hc2 := (hxiG Y hY L.GG hGG).eq
  calc io L.GGi * f.xi Y * (io L.GG * f.x Y * f.l L Y * f.F * f.Fi)
      = io L.GGi * (f.xi Y * io L.GG) * f.x Y * f.l L Y * (f.F * f.Fi) := by simp only [mul_assoc]
    _ = io L.GGi * (io L.GG * f.xi Y) * f.x Y * f.l L Y * (f.F * f.Fi) := by rw [hc2]
    _ = (io L.GGi * io L.GG) * (f.xi Y * f.x Y) * f.l L Y * (f.F * f.Fi) := by simp only [mul_assoc]
    _ = f.l L Y := by simp only [hGG2, hx2, hFFi, one_mul, mul_one]

/- English proof (translation)
Introduce `hSM A S _ _ _ _ _ _ r L st hst`. Establish `hio_mul : ∀ a b : A, (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b` using `fun a b => by`. Simplify using `only [io, map_mul]`. Establish `hio_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1` using `by simp only [io, map_one]`. Establish `hio_comm : ∀ a b : A, Commute a b → Commute (io a : SlopeTestRemainingChoices S A) (io b)` using `fun a b h => by`.

Simplify using `only [io]`. Conclude with `h.map _`. Establish `hio_star : ∀ a : A, star (io a : SlopeTestRemainingChoices S A) = io (star a)` using `fun a => by`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[io, Matrix.star_apply, Matrix.scalar_apply]`. Simplify using `[io, Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply, h, Ne.symm h]`. Use `{ module := ?_, lowerLeftEntry_commute := ?_, inv_reg := ?_, F_Fi := ?_, Fi_F := ?_, x_xi := ?_, c_ci := ?_, x_commute := ?_, x_c := ?_, x_fn := ?_, x_nab := ?_, c_fn := ?_, x_star := ?_, c_star := ?_, ee_fn := ?_, form := ?_, frame_τ := ?_, frame_l := ?_ }` and prove the remaining obligations. Apply the tactic sequence `all_goals dsimp only [Start.frame]`.

Conclude with `hSM ℂ A S st.QQ st.q hst.start`. Introduce `Y _ Y' _`. Simplify using `only [lift0, Matrix.map_apply]`. Conclude with `hio_comm _ _ (hst.lowerLeftEntry_commute Y Y')`. Conclude with `Set.subset_univ _`.

Conclude with `mul_one 1`. Conclude with `mul_one 1`. Introduce `Y hY`. Conclude with `⟨by rw [← hio_mul, (hst.x_xi Y hY).1, hio_one], by rw [← hio_mul, (hst.x_xi Y hY).2, hio_one]⟩`. Conclude with `⟨mul_one 1, mul_one 1⟩`.

Introduce `Y Y'`. Conclude with `hio_comm _ _ (hst.x_commute Y Y')`. Introduce `Y`. Conclude with `Commute.one_right _`. Introduce `Y g hg`.

Conclude with `hio_comm _ _ (hst.x_fn Y g hg)`. Introduce `Y`. Conclude with `hio_comm _ _ (hst.x_nab Y)`. Introduce `g _`. Conclude with `Commute.one_left _`.

Introduce `Y hY`. Rewrite using `[hio_star, hst.x_star Y hY]`. Conclude with `star_one _`. Introduce `Y g hg`. Conclude with `hio_comm _ _ (hst.ee_fn Y g hg)`.

Simplify using `[Formalism.FourierDecayAlt.Fr.FrameData.d, Start.frame]`. Introduce `Y _`. Simplify using `only [lift0, Matrix.map_apply, one_mul, mul_one]`. Rewrite using `[hst.tau Y]`. Simplify using `only [io, map_mul]`.

Introduce `Y hY _`. Simplify using `only [lift0, Matrix.map_apply, one_mul, mul_one, Formalism.FourierDecayAlt.Fr.FrameData.l, Formalism.FourierDecayAlt.Fr.kapL]`. Rewrite using `[hst.low Y hY]`. Simplify using `only [io, map_mul, map_add]`.
-/
theorem start_is_frame : StartFrame := by
  intro hSM A S _ _ _ _ _ _ r L st hst
  have hio_mul : ∀ a b : A, (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := fun a b => by
    simp only [io, map_mul]
  have hio_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by simp only [io, map_one]
  have hio_comm : ∀ a b : A, Commute a b → Commute (io a : SlopeTestRemainingChoices S A) (io b) := fun a b h => by
    simp only [io]
    exact h.map _
  have hio_star : ∀ a : A, star (io a : SlopeTestRemainingChoices S A) = io (star a) := fun a => by
    ext i j
    by_cases h : i = j
    · subst h
      simp [io, Matrix.star_apply, Matrix.scalar_apply]
    · simp [io, Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply, h, Ne.symm h]
  refine
    { module := ?_, lowerLeftEntry_commute := ?_, inv_reg := ?_, F_Fi := ?_, Fi_F := ?_, x_xi := ?_, c_ci := ?_,
      x_commute := ?_, x_c := ?_, x_fn := ?_, x_nab := ?_, c_fn := ?_, x_star := ?_, c_star := ?_,
      ee_fn := ?_, form := ?_, frame_τ := ?_, frame_l := ?_ }
  all_goals dsimp only [Start.frame]
  · exact hSM ℂ A S st.QQ st.q hst.start
  · intro Y _ Y' _
    simp only [lift0, Matrix.map_apply]
    exact hio_comm _ _ (hst.lowerLeftEntry_commute Y Y')
  · exact Set.subset_univ _
  · exact mul_one 1
  · exact mul_one 1
  · intro Y hY
    exact ⟨by rw [← hio_mul, (hst.x_xi Y hY).1, hio_one], by rw [← hio_mul, (hst.x_xi Y hY).2, hio_one]⟩
  · exact ⟨mul_one 1, mul_one 1⟩
  · intro Y Y'
    exact hio_comm _ _ (hst.x_commute Y Y')
  · intro Y
    exact Commute.one_right _
  · intro Y g hg
    exact hio_comm _ _ (hst.x_fn Y g hg)
  · intro Y
    exact hio_comm _ _ (hst.x_nab Y)
  · intro g _
    exact Commute.one_left _
  · intro Y hY
    rw [hio_star, hst.x_star Y hY]
  · exact star_one _
  · intro Y g hg
    exact hio_comm _ _ (hst.ee_fn Y g hg)
  · simp [Formalism.FourierDecayAlt.Fr.FrameData.d, Start.frame]
  · intro Y _
    simp only [lift0, Matrix.map_apply, one_mul, mul_one]
    rw [hst.tau Y]
    simp only [io, map_mul]
  · intro Y hY _
    simp only [lift0, Matrix.map_apply, one_mul, mul_one, Formalism.FourierDecayAlt.Fr.FrameData.l, Formalism.FourierDecayAlt.Fr.kapL]
    rw [hst.low Y hY]
    simp only [io, map_mul, map_add]

/- English proof (translation)
Introduce `A S _ _ _ _ _ _ r L st w`. Proceed by induction on `w with`. Consider the case `nil`. Use `⟨rfl, ?_, ?_, rfl, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `Y`. Both sides reduce to the same expression. Use extensionality with `Y`. Simplify using `[ofWord, Start.frame, Reg]`.

Consider the case `cons l w ih`. Take `⟨h1, h2, h3, h4, h5⟩` from `ih`. Distinguish the cases in `hl : l.plus`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[ofWord, hl, FrameData.plus, RRw, h1, h2]`.

Use function extensionality and compare the values at `Y`. Simplify using `[ofWord, hl, FrameData.plus, TTw, h2]`. Use function extensionality and compare the values at `Y`. Simplify using `[ofWord, hl, FrameData.plus, qw, h3]`. Simplify using `[ofWord, hl, FrameData.plus, h4]`.

Use extensionality with `Y`. Simplify using `[ofWord, hl, FrameData.plus, h5, Reg, RegL, and_comm]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[ofWord, hl, FrameData.minus, RRw, h1, h2]`. Use function extensionality and compare the values at `Y`.

Simplify using `[ofWord, hl, FrameData.minus, TTw, h2]`. Use function extensionality and compare the values at `Y`. Simplify using `[ofWord, hl, FrameData.minus, qw, h3]`. Simplify using `[ofWord, hl, FrameData.minus, h4]`. Use extensionality with `Y`.

Simplify using `[ofWord, hl, FrameData.minus, h5, Reg, RegL, and_comm]`.
-/
theorem frame_module_of_word : WordJoint := by
  intro A S _ _ _ _ _ _ r L st w
  induction w with
  | nil =>
    refine ⟨rfl, ?_, ?_, rfl, ?_⟩
    · funext Y; rfl
    · funext Y; rfl
    · ext Y; simp [ofWord, Start.frame, Reg]
  | cons l w ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    by_cases hl : l.plus
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [ofWord, hl, FrameData.plus, RRw, h1, h2]
      · funext Y; simp [ofWord, hl, FrameData.plus, TTw, h2]
      · funext Y; simp [ofWord, hl, FrameData.plus, qw, h3]
      · simp [ofWord, hl, FrameData.plus, h4]
      · ext Y; simp [ofWord, hl, FrameData.plus, h5, Reg, RegL, and_comm]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [ofWord, hl, FrameData.minus, RRw, h1, h2]
      · funext Y; simp [ofWord, hl, FrameData.minus, TTw, h2]
      · funext Y; simp [ofWord, hl, FrameData.minus, qw, h3]
      · simp [ofWord, hl, FrameData.minus, h4]
      · ext Y; simp [ofWord, hl, FrameData.minus, h5, Reg, RegL, and_comm]

/- English proof (translation)
Introduce `B _ _ Z γ Ya Y h1 h2 h3`. Establish `e1 : Y - γ ≠ 0` using `sub_ne_zero.mpr h1`. Establish `e2 : Ya - γ ≠ 0` using `sub_ne_zero.mpr h2`. Establish `e3 : Y - Ya ≠ 0` using `sub_ne_zero.mpr h3`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [← sub_smul, smul_smul]`. Use `congr 1`. Apply the tactic sequence `first | (field_simp; ring) | field_simp | ring`. Simplify using `only [← sub_smul, ← add_smul, smul_smul]`. Use `congr 1`.

Apply the tactic sequence `first | (field_simp; ring) | field_simp | ring`.
-/
theorem residue_partial_fractions : ResidueStep := by
  intro B _ _ Z γ Ya Y h1 h2 h3
  have e1 : Y - γ ≠ 0 := sub_ne_zero.mpr h1
  have e2 : Ya - γ ≠ 0 := sub_ne_zero.mpr h2
  have e3 : Y - Ya ≠ 0 := sub_ne_zero.mpr h3
  constructor
  · simp only [← sub_smul, smul_smul]
    congr 1
    first | (field_simp; ring) | field_simp | ring
  · simp only [← sub_smul, ← add_smul, smul_smul]
    congr 1
    first | (field_simp; ring) | field_simp | ring

end Formalism.FourierDecayAlt.P
