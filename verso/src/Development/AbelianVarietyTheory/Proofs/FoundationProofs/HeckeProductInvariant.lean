import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.HeckeCosetLevel

/- English proof (translation)
Simplify using `[toGQ, h]`.
-/
lemma toGQ_val (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma ofSL_val (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  rfl

/- English proof (translation)
Establish `hAB : 0 < (A * B).det` using `by rw [Matrix.det_mul]; exact mul_pos hA hB`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[toGQ_val _ hAB]`. Simplify using `only [Subgroup.coe_mul, Units.val_mul]`.

Rewrite using `[toGQ_val _ hA, toGQ_val _ hB, Matrix.map_mul]`.
-/
lemma toGQ_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (hB : 0 < B.det) :
    toGQ (A * B) = toGQ A * toGQ B := by
  have hAB : 0 < (A * B).det := by rw [Matrix.det_mul]; exact mul_pos hA hB
  apply Subtype.ext; apply Units.ext
  rw [toGQ_val _ hAB]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [toGQ_val _ hA, toGQ_val _ hB, Matrix.map_mul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[toGQ_val _ (by simp), ofSL_val]`.
-/
lemma toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  apply Subtype.ext; apply Units.ext
  rw [toGQ_val _ (by simp), ofSL_val]

/- English proof (translation)
Establish `hu : IsUnit (q : ZMod M)`. Use `(ZMod.unitOfCoprime q hqM).isUnit` as an intermediate fact. Rewrite `this` using `[ZMod.coe_unitOfCoprime]`. Then use the resulting hypothesis. Establish `e : ∀ i j, ((m i j : ℤ) : ZMod M) = ((N : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ZMod M) * (B 0 j : ZMod M) + ((N : Matrix (Fin 2) (Fin 2) ℤ) i 1 : ZMod M) * (B 1 j : ZMod M)`. Introduce `i j`.

Rewrite using `[← hm]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e00` using `e 0 0`. Establish `e01` using `e 0 1`. Establish `e10` using `e 1 0`.

Establish `e11` using `e 1 1`. Rewrite `e00` using `[b00, b10, h00]`. Rewrite `e01` using `[b01, b11, h01]`. Rewrite `e10` using `[b00, b10, h10]`. Rewrite `e11` using `[b01, b11, h11]`.

Simplify using `only [mul_one, mul_zero, add_zero, zero_add] at e00 e01 e10 e11`. Use `CongruenceSubgroup.Gamma_mem.mpr ⟨e00.symm, ?_, e10.symm, ?_⟩` and prove the remaining obligations. Conclude with `(hu.mul_left_eq_zero).mp e01.symm`. Conclude with `hu.mul_right_cancel (by rw [one_mul]; exact e11.symm)`.
-/
lemma mem_Gamma_of_mul (M q : ℕ) (hqM : Nat.Coprime q M) (N : SL(2, ℤ)) (B m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : (N : Matrix (Fin 2) (Fin 2) ℤ) * B = m)
    (b00 : (B 0 0 : ZMod M) = 1) (b01 : (B 0 1 : ZMod M) = 0) (b10 : (B 1 0 : ZMod M) = 0) (b11 : (B 1 1 : ZMod M) = q)
    (h00 : (m 0 0 : ZMod M) = 1) (h01 : (m 0 1 : ZMod M) = 0) (h10 : (m 1 0 : ZMod M) = 0) (h11 : (m 1 1 : ZMod M) = q) :
    N ∈ CongruenceSubgroup.Gamma M := by
  have hu : IsUnit (q : ZMod M) := by
    have := (ZMod.unitOfCoprime q hqM).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  have e : ∀ i j, ((m i j : ℤ) : ZMod M) = ((N : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ZMod M) * (B 0 j : ZMod M) +
      ((N : Matrix (Fin 2) (Fin 2) ℤ) i 1 : ZMod M) * (B 1 j : ZMod M) := by
    intro i j; rw [← hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [b00, b10, h00] at e00
  rw [b01, b11, h01] at e01
  rw [b00, b10, h10] at e10
  rw [b01, b11, h11] at e11
  simp only [mul_one, mul_zero, add_zero, zero_add] at e00 e01 e10 e11
  refine CongruenceSubgroup.Gamma_mem.mpr ⟨e00.symm, ?_, e10.symm, ?_⟩
  · exact (hu.mul_left_eq_zero).mp e01.symm
  · exact hu.mul_right_cancel (by rw [one_mul]; exact e11.symm)

/- English proof (translation)
Introduce `B`. Take `⟨s01, s10, s11⟩` from `hσ`. Establish `hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1` using `σ.2`. Rewrite `hd` using `[Matrix.det_fin_two]`. Establish `hd'` using `congrArg (fun x : ℤ => (x : ZMod M)) hd`.

Simplify using `only [en] at s01 s10 s11`. Move the coercions through the operations in `at hd'`. Rewrite `hd'` using `[s01, s10, s11]`. Simplify using `[B, Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]`. Take the linear combination `hd'`.
-/
lemma sigma_diag_mod (M q : ℕ) (σ : SL(2, ℤ))
    (hσ : (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) :
    let B := (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
    (B 0 0 : ZMod M) = 1 ∧ (B 0 1 : ZMod M) = 0 ∧ (B 1 0 : ZMod M) = 0 ∧ (B 1 1 : ZMod M) = q := by
  intro B
  obtain ⟨s01, s10, s11⟩ := hσ
  have hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
  rw [Matrix.det_fin_two] at hd
  have hd' := congrArg (fun x : ℤ => (x : ZMod M)) hd
  simp only [en] at s01 s10 s11
  push_cast at hd'
  rw [s01, s10, s11] at hd'
  simp [B, Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]
  linear_combination hd'

def reps (M q : ℕ) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < q then !![1, ((i : ℕ) * M : ℤ); 0, (q : ℤ)] else (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]

/- English proof (translation)
Apply the tactic sequence `unfold reps; split_ifs <;> simp [Matrix.det_fin_two]`.
-/
lemma reps_det (M q : ℕ) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : (reps M q σ i).det = q := by
  unfold reps; split_ifs <;> simp [Matrix.det_fin_two]

/- English proof (translation)
Use `haveI := Fact.mk hq`. Establish `hq0 : (q : ℤ) ≠ 0` using `by exact_mod_cast hq.ne_zero`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Distinguish the cases in `hdiv : (q : ℤ) ∣ m 0 0 ∧ (q : ℤ) ∣ m 1 0`. Use `right`.

Take `⟨⟨a', ha⟩, ⟨c', hc⟩⟩` from `hdiv`. Establish `hd1 : a' * m 1 1 - m 0 1 * c' = 1`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Rewrite `hdet` using `[ha, hc]`. Take the linear combination `hdet`.

Establish `hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1` using `σ.2`. Set `N0 : Matrix (Fin 2) (Fin 2) ℤ` to `!![a', m 0 1; c', m 1 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate`. Establish `hN : N0.det = 1`. Simplify using `only [N0, Matrix.det_mul, Matrix.det_adjugate, hσd, Matrix.det_fin_two_of]`. Simplify using `[hd1]`.

Set `N : SL(2, ℤ)` to `⟨N0, hN⟩`. Establish `hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = m` using `by show N0 * _ = m`. Simplify using `only [N0]`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate, Matrix.adjugate_mul, hσd, one_smul, Matrix.mul_one]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hc] <;> ring`.

Take `⟨b00, b01, b10, b11⟩` from `sigma_diag_mod M q σ hσ`. Conclude with `⟨N, mem_Gamma_of_mul M q hqM N _ m hNm b00 b01 b10 b11 h00 h01 h10 h11, hNm.symm⟩`. Use `left`. Establish `hMq : ((M : ℕ) : ZMod q) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`.

Conclude with `(Nat.Prime.coprime_iff_not_dvd hq).mp hqM`. Establish `hz : ∀ x : ℤ, (q : ℤ) ∣ x ↔ ((x : ℤ) : ZMod q) = 0` using `fun x => (ZMod.intCast_zmod_eq_zero_iff_dvd x q).symm`. Establish `hdz : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ZMod q) - (m 0 1 : ZMod q) * (m 1 0 : ZMod q) = 0`. Use `congrArg (fun x : ℤ => (x : ZMod q)) hdet` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[this]`. Conclude with `ZMod.natCast_self q`. Use `set a : ZMod q := ((m 0 0 : ℤ) : ZMod q) with ha`. Use `set b : ZMod q := ((m 0 1 : ℤ) : ZMod q) with hb`. Use `set c : ZMod q := ((m 1 0 : ℤ) : ZMod q) with hc`.

Use `set d : ZMod q := ((m 1 1 : ℤ) : ZMod q) with hd`. Establish `hac : a ≠ 0 ∨ c ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hdiv ⟨(hz _).mpr hcon.1, (hz _).mpr hcon.2⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht1, ht2⟩ : ∃ t : ZMod q, b = a * t * (M : ZMod q) ∧ d = c * t * (M : ZMod q) := by`. Break down `hac with ha0 | hc0` into its components or cases. Use `⟨b / (a * (M : ZMod q)), ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hdz`. Distinguish the cases in `ha0 : a = 0`. Use `⟨d / (c * (M : ZMod q)), ?_, ?_⟩` and prove the remaining obligations. Rewrite `hdz`, the goal using `[ha0]`. Establish `: b * c = 0` using `by linear_combination -hdz`.

Break down `mul_eq_zero.mp this with h | h` into its components or cases. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd h hc0`. Clear the denominators using the available nonvanishing facts.

Use `⟨b / (a * (M : ZMod q)), ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts. Take the linear combination `hdz`. Use `⟨t.val, ZMod.val_lt t, ?_⟩` and prove the remaining obligations.

Establish `ht : ((t.val : ℤ) : ZMod q) = t` using `by simp`. Choose the witnesses or unpack the hypotheses as in `⟨t1, e1⟩ : (q : ℤ) ∣ m 0 1 - m 0 0 * ((t.val : ℤ) * M) := by`. Rewrite using `[hz]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, ← hb, ← ha, ht1]`.

Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨t2, e2⟩ : (q : ℤ) ∣ m 1 1 - m 1 0 * ((t.val : ℤ) * M) := by`. Rewrite using `[hz]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, ← hd, ← hc, ht2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hd1 : m 0 0 * t2 - t1 * m 1 0 = 1`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Take the linear combination `hdet - m 0 0 * e2 + m 1 0 * e1`. Set `N : SL(2, ℤ)` to `⟨!![m 0 0, t1; m 1 0, t2], by rw [Matrix.det_fin_two_of]; exact hd1⟩`.

Establish `hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * !![1, ((t.val : ℕ) * M : ℤ); 0, (q : ℤ)] = m` using `by show !![m 0 0, t1; m 1 0, t2] * _ = m`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [-ZMod.natCast_val] <;> first | linear_combination -e1 | linear_combination -e2`. Use `⟨N, mem_Gamma_of_mul M q hqM N _ m hNm (by simp) (by simp) (by simp) (by simp) h00 h01 h10 h11, hNm.symm⟩` and prove the remaining obligations.
-/
theorem exists_coset (M q : ℕ) (hM : 0 < M) (hq : q.Prime) (hqM : Nat.Coprime q M) (σ : SL(2, ℤ))
    (hσ : (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = q) (h00 : (m 0 0 : ZMod M) = 1) (h01 : (m 0 1 : ZMod M) = 0)
    (h10 : (m 1 0 : ZMod M) = 0) (h11 : (m 1 1 : ZMod M) = q) :
    (∃ j < q, ∃ γ ∈ CongruenceSubgroup.Gamma M, m = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (j * M : ℤ); 0, (q : ℤ)]) ∨
      ∃ γ ∈ CongruenceSubgroup.Gamma M, m = (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) := by
  haveI := Fact.mk hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hdiv : (q : ℤ) ∣ m 0 0 ∧ (q : ℤ) ∣ m 1 0
  · right
    obtain ⟨⟨a', ha⟩, ⟨c', hc⟩⟩ := hdiv
    have hd1 : a' * m 1 1 - m 0 1 * c' = 1 := by
      apply mul_left_cancel₀ hq0
      rw [ha, hc] at hdet; linear_combination hdet
    have hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
    let N0 : Matrix (Fin 2) (Fin 2) ℤ := !![a', m 0 1; c', m 1 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate
    have hN : N0.det = 1 := by
      simp only [N0, Matrix.det_mul, Matrix.det_adjugate, hσd, Matrix.det_fin_two_of]
      simp [hd1]
    let N : SL(2, ℤ) := ⟨N0, hN⟩
    have hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = m := by
      show N0 * _ = m
      simp only [N0]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate, Matrix.adjugate_mul, hσd, one_smul,
        Matrix.mul_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hc] <;> ring
    obtain ⟨b00, b01, b10, b11⟩ := sigma_diag_mod M q σ hσ
    exact ⟨N, mem_Gamma_of_mul M q hqM N _ m hNm b00 b01 b10 b11 h00 h01 h10 h11, hNm.symm⟩
  · left
    have hMq : ((M : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqM
    have hz : ∀ x : ℤ, (q : ℤ) ∣ x ↔ ((x : ℤ) : ZMod q) = 0 := fun x => (ZMod.intCast_zmod_eq_zero_iff_dvd x q).symm
    have hdz : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ZMod q) - (m 0 1 : ZMod q) * (m 1 0 : ZMod q) = 0 := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
      push_cast at this; rw [this]; exact ZMod.natCast_self q
    set a : ZMod q := ((m 0 0 : ℤ) : ZMod q) with ha
    set b : ZMod q := ((m 0 1 : ℤ) : ZMod q) with hb
    set c : ZMod q := ((m 1 0 : ℤ) : ZMod q) with hc
    set d : ZMod q := ((m 1 1 : ℤ) : ZMod q) with hd
    have hac : a ≠ 0 ∨ c ≠ 0 := by
      by_contra hcon; push_neg at hcon
      exact hdiv ⟨(hz _).mpr hcon.1, (hz _).mpr hcon.2⟩
    obtain ⟨t, ht1, ht2⟩ : ∃ t : ZMod q, b = a * t * (M : ZMod q) ∧ d = c * t * (M : ZMod q) := by
      rcases hac with ha0 | hc0
      · refine ⟨b / (a * (M : ZMod q)), ?_, ?_⟩
        · field_simp
        · field_simp; linear_combination hdz
      · by_cases ha0 : a = 0
        · refine ⟨d / (c * (M : ZMod q)), ?_, ?_⟩
          · rw [ha0] at hdz ⊢
            have : b * c = 0 := by linear_combination -hdz
            rcases mul_eq_zero.mp this with h | h
            · rw [h]; ring
            · exact absurd h hc0
          · field_simp
        · refine ⟨b / (a * (M : ZMod q)), ?_, ?_⟩
          · field_simp
          · field_simp; linear_combination hdz
    refine ⟨t.val, ZMod.val_lt t, ?_⟩
    have ht : ((t.val : ℤ) : ZMod q) = t := by simp
    obtain ⟨t1, e1⟩ : (q : ℤ) ∣ m 0 1 - m 0 0 * ((t.val : ℤ) * M) := by
      rw [hz]; push_cast; rw [ZMod.natCast_zmod_val, ← hb, ← ha, ht1]; ring
    obtain ⟨t2, e2⟩ : (q : ℤ) ∣ m 1 1 - m 1 0 * ((t.val : ℤ) * M) := by
      rw [hz]; push_cast; rw [ZMod.natCast_zmod_val, ← hd, ← hc, ht2]; ring
    have hd1 : m 0 0 * t2 - t1 * m 1 0 = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet - m 0 0 * e2 + m 1 0 * e1
    let N : SL(2, ℤ) := ⟨!![m 0 0, t1; m 1 0, t2], by rw [Matrix.det_fin_two_of]; exact hd1⟩
    have hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * !![1, ((t.val : ℕ) * M : ℤ); 0, (q : ℤ)] = m := by
      show !![m 0 0, t1; m 1 0, t2] * _ = m
      ext i j; fin_cases i <;> fin_cases j <;> simp [-ZMod.natCast_val] <;> first | linear_combination -e1 | linear_combination -e2
    refine ⟨N, mem_Gamma_of_mul M q hqM N _ m hNm (by simp) (by simp) (by simp) (by simp) h00 h01 h10 h11, hNm.symm⟩

/- English proof (translation)
Establish `hq1 : ¬ (q : ℤ) ∣ 1`. Introduce `h`. Use `Int.natCast_dvd_natCast.mp (by exact_mod_cast h)` as an intermediate fact. Conclude with `hq.one_lt.ne' (Nat.dvd_one.mp this)`. Establish `E : ∀ a b, reps M q σ i a b = ((g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) a b` using `fun a b => by rw [h]`.

Establish `e00` using `E 0 0`. Establish `e01` using `E 0 1`. Establish `e10` using `E 1 0`. Establish `e11` using `E 1 1`. Unfold `reps at e00 e01 e10 e11`.

Apply the tactic sequence `by_cases hi : (i : ℕ) < q <;> by_cases hk : (k : ℕ) < q <;>`. Apply the tactic sequence `simp only [hi, hk, if_true, if_false] at e00 e01 e10 e11 <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11`. Establish `hdv : (q : ℤ) ∣ ((i : ℕ) - (k : ℕ) : ℤ) * M` using `⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by`. Rewrite `e01` using `[← e00]`.

Take the linear combination `e01⟩`. Establish `hcop : IsCoprime (q : ℤ) (M : ℤ)` using `Nat.isCoprime_iff_coprime.mpr hqM`. Establish `hdv'` using `hcop.dvd_of_dvd_mul_right hdv`. Apply the tactic sequence `have h0 := Int.eq_zero_of_abs_lt_dvd hdv' (by rw [abs_lt]; constructor <;> omega)`. Conclude with `Fin.ext (by omega)`.

Conclude with `absurd ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by linear_combination e00⟩ hq1`. Establish `hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1` using `σ.2`. Rewrite `hσd` using `[Matrix.det_fin_two]`. Apply `absurd _ hq1` to reduce the goal to its premises. Conclude with `⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by`.

Take the linear combination `-hσd + (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e11 - (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e01 - ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e10 + ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e00⟩`. Conclude with `Fin.ext (by omega)`.
-/
theorem reps_distinct (M q : ℕ) (hq : q.Prime) (hqM : Nat.Coprime q M) (σ : SL(2, ℤ)) (i k : Fin (q + 1))
    (g : SL(2, ℤ)) (h : reps M q σ i = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) : i = k := by
  have hq1 : ¬ (q : ℤ) ∣ 1 := by
    intro h
    have := Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have E : ∀ a b, reps M q σ i a b = ((g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) a b := fun a b => by rw [h]
  have e00 := E 0 0
  have e01 := E 0 1
  have e10 := E 1 0
  have e11 := E 1 1
  unfold reps at e00 e01 e10 e11
  by_cases hi : (i : ℕ) < q <;> by_cases hk : (k : ℕ) < q <;>
    simp only [hi, hk, if_true, if_false] at e00 e01 e10 e11 <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ·
    have hdv : (q : ℤ) ∣ ((i : ℕ) - (k : ℕ) : ℤ) * M := ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by
      rw [← e00] at e01; linear_combination e01⟩
    have hcop : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
    have hdv' := hcop.dvd_of_dvd_mul_right hdv
    have h0 := Int.eq_zero_of_abs_lt_dvd hdv' (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  ·
    exact absurd ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by linear_combination e00⟩ hq1
  ·
    have hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
    rw [Matrix.det_fin_two] at hσd
    apply absurd _ hq1
    exact ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by
      linear_combination -hσd + (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e11 - (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e01 -
        ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e10 + ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e00⟩
  · exact Fin.ext (by omega)

end GlobalTheory.HeckeCosetLevel

open GlobalTheory.HeckeCosetLevel in
/- English proof (translation)
Introduce `Ω _ _ ε X M q f hM hq hqM hf σ hσ γ hγ`. Establish `hprod : (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f`. Rewrite using `[Fin.prod_univ_castSucc, Finset.prod_range]`. Simplify using `[reps]`. Rewrite using `[hprod, map_prod]`.

Take `⟨g00, g01, g10, g11⟩` from `CongruenceSubgroup.Gamma_mem.mp hγ`. Establish `hpos : ∀ i, 0 < (reps M q σ i).det` using `fun i => by rw [reps_det]; exact_mod_cast hq.pos`. Establish `hrM : ∀ i, ((reps M q σ i) 0 0 : ZMod M) = 1 ∧ ((reps M q σ i) 0 1 : ZMod M) = 0 ∧ ((reps M q σ i) 1 0 : ZMod M) = 0 ∧ ((reps M q σ i) 1 1 : ZMod M) = q`. Introduce `i`. Unfold `reps`.

Use `split_ifs with hi`. Simplify using the standard rewrite rules. Take `⟨s01, s10, s11⟩` from `hσ`. Establish `hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1` using `σ.2`. Rewrite `hd` using `[Matrix.det_fin_two]`.

Establish `hd'` using `congrArg (fun x : ℤ => (x : ZMod M)) hd`. Simplify using `only [en] at s01 s10 s11`. Move the coercions through the operations in `at hd'`. Rewrite `hd'` using `[s01, s10, s11]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]`.

Take the linear combination `hd'`. Establish `key : ∀ i, ∃ k, ∃ g ∈ CongruenceSubgroup.Gamma M, reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k`. Introduce `i`. Take `⟨a00, a01, a10, a11⟩` from `hrM i`. Establish `hdet : (reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = q`.

Rewrite using `[Matrix.det_mul, reps_det]`. Simplify using the standard rewrite rules. Break down `exists_coset M q hM hq hqM σ hσ _ hdet (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g00, g10]) (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g01, g11]) (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g00, g10]) (by simp [Matrix.mul_apply, Fin.sum_univ …` into its components or cases. Use `⟨⟨j, by omega⟩, g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Simplify using `[reps, hj]`. Use `⟨Fin.last q, g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Simplify using `[reps]`. Use `choose π g hg hπ using key`.

Establish `inj : Function.Injective π`. Introduce `i j hij`. Establish `h1` using `hπ i`. Establish `h2` using `hπ j`. Rewrite `h1` using `[hij]`.

Apply `reps_distinct M q hq hqM σ i j (g i * (g j)⁻¹)` to reduce the goal to its premises. Establish `hγi : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]`. Establish `hgj : ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]`.

Establish `hgj' : (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hγi, Matrix.mul_one]`. Use `_ = (g i : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((g j : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ (π j)) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by`.

Rewrite using `[h1]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (g j : Matrix (Fin 2) (Fin 2) ℤ), hgj', Matrix.one_mul]`. Use `_ = ((g i * (g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ j := by`. Rewrite using `[← h2, Matrix.SpecialLinearGroup.coe_mul]`.

Simplify using `only [Matrix.mul_assoc, hγi, Matrix.mul_one]`. Set `e` to `Equiv.ofBijective π (Finite.injective_iff_bijective.mp inj)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← X.sl_mul, ← toGQ_SL γ, ← toGQ_mul _ _ (hpos i) (by simp), hπ i, toGQ_mul _ _ (by simp) (hpos _), toGQ_SL, X.sl_mul, hf _ (hg i)]`.

Both sides reduce to the same expression. Use `_ = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := Equiv.prod_comp e (fun i => X.sl (toGQ (reps M q σ i)) f)`.
-/
theorem GlobalTheory.hecke_product_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M q : ℕ) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f := by
  intro Ω _ _ ε X M q f hM hq hqM hf σ hσ γ hγ
  have hprod : (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := by
    rw [Fin.prod_univ_castSucc, Finset.prod_range]
    simp [reps]
  rw [hprod, map_prod]
  obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have hpos : ∀ i, 0 < (reps M q σ i).det := fun i => by rw [reps_det]; exact_mod_cast hq.pos
  have hrM : ∀ i, ((reps M q σ i) 0 0 : ZMod M) = 1 ∧ ((reps M q σ i) 0 1 : ZMod M) = 0 ∧
      ((reps M q σ i) 1 0 : ZMod M) = 0 ∧ ((reps M q σ i) 1 1 : ZMod M) = q := by
    intro i
    unfold reps
    split_ifs with hi
    · simp
    · obtain ⟨s01, s10, s11⟩ := hσ
      have hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
      rw [Matrix.det_fin_two] at hd
      have hd' := congrArg (fun x : ℤ => (x : ZMod M)) hd
      simp only [en] at s01 s10 s11
      push_cast at hd'
      rw [s01, s10, s11] at hd'
      simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]
      linear_combination hd'
  have key : ∀ i, ∃ k, ∃ g ∈ CongruenceSubgroup.Gamma M,
      reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k := by
    intro i
    obtain ⟨a00, a01, a10, a11⟩ := hrM i
    have hdet : (reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = q := by
      rw [Matrix.det_mul, reps_det]; simp
    rcases exists_coset M q hM hq hqM σ hσ _ hdet
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g00, g10])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g01, g11])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g00, g10])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g01, g11]) with ⟨j, hj, g, hg, h⟩ | ⟨g, hg, h⟩
    · refine ⟨⟨j, by omega⟩, g, hg, ?_⟩
      rw [h]; simp [reps, hj]
    · refine ⟨Fin.last q, g, hg, ?_⟩
      rw [h]; simp [reps]
  choose π g hg hπ using key
  have inj : Function.Injective π := by
    intro i j hij
    have h1 := hπ i
    have h2 := hπ j
    rw [hij] at h1
    apply reps_distinct M q hq hqM σ i j (g i * (g j)⁻¹)
    have hγi : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgj : ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgj' : (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc reps M q σ i = reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = (g i : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            ((g j : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ (π j)) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [h1]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (g j : Matrix (Fin 2) (Fin 2) ℤ), hgj', Matrix.one_mul]
      _ = ((g i * (g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ j := by
          rw [← h2, Matrix.SpecialLinearGroup.coe_mul]
          simp only [Matrix.mul_assoc, hγi, Matrix.mul_one]
  let e := Equiv.ofBijective π (Finite.injective_iff_bijective.mp inj)
  calc ∏ i : Fin (q + 1), X.sl (ofSL γ) (X.sl (toGQ (reps M q σ i)) f)
      = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ (e i))) f := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [← X.sl_mul, ← toGQ_SL γ, ← toGQ_mul _ _ (hpos i) (by simp), hπ i,
          toGQ_mul _ _ (by simp) (hpos _), toGQ_SL, X.sl_mul, hf _ (hg i)]
        rfl
    _ = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := Equiv.prod_comp e (fun i => X.sl (toGQ (reps M q σ i)) f)
