import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in
/- English proof (translation)
Establish `hXQ : Xᴴ * Q = 0` using `by rw [← hQ, ← conjTranspose_mul, hX, conjTranspose_zero]`. Establish `hYQ : Yᴴ * Q = 0` using `by rw [← hQ, ← conjTranspose_mul, hY, conjTranspose_zero]`. Establish `e2 : Xᴴ * Q = Yᴴ * Q` using `by rw [hXQ, hYQ]`. Establish `e3 : Qᴴ * X = Qᴴ * Y` using `by rw [hQ, hX, hY]`. Establish `hG : (fromCols X Q)ᴴ * fromCols X Q = (fromCols Y Q)ᴴ * fromCols Y Q`.

Use extensionality with `(i | i) (j | j)`. Simplify `congrFun (congrFun h i) j` using `[Matrix.mul_apply]`. Simplify `congrFun (congrFun e2 i) j` using `[Matrix.mul_apply]`. Simplify `congrFun (congrFun e3 i) j` using `[Matrix.mul_apply]`. Simplify using `[Matrix.mul_apply]`.

Take `⟨W, hWu, hW⟩` from `_root_.GlobalTheory.UnitaryExtension.exists_unitary_mul_eq _ _ hG`. Rewrite `hW` using `[mul_fromCols, fromCols_inj.eq_iff]`. Conclude with `⟨W, hWu, hW.2, hW.1⟩`.
-/
private lemma exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Qᴴ = Q)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (h : Xᴴ * X = Yᴴ * Y) (hX : Q * X = 0) (hY : Q * Y = 0) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧ W * Q = Q ∧ W * X = Y := by
  have hXQ : Xᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hX, conjTranspose_zero]
  have hYQ : Yᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hY, conjTranspose_zero]
  have e2 : Xᴴ * Q = Yᴴ * Q := by rw [hXQ, hYQ]
  have e3 : Qᴴ * X = Qᴴ * Y := by rw [hQ, hX, hY]
  have hG : (fromCols X Q)ᴴ * fromCols X Q = (fromCols Y Q)ᴴ * fromCols Y Q := by
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e2 i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e3 i) j
    · simp [Matrix.mul_apply]
  obtain ⟨W, hWu, hW⟩ := _root_.GlobalTheory.UnitaryExtension.exists_unitary_mul_eq _ _ hG
  rw [mul_fromCols, fromCols_inj.eq_iff] at hW
  exact ⟨W, hWu, hW.2, hW.1⟩

open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in

/- English proof (translation)
Take `⟨Pp, hPp⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 + H)` from `⟨_, rfl⟩`. Take `⟨Pm, hPm⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 - H)` from `⟨_, rfl⟩`. Establish `hPpH : Ppᴴ = Pp` using `by simp [hPp, hH, conjTranspose_smul]`. Establish `hPmH : Pmᴴ = Pm` using `by simp [hPm, hH, conjTranspose_smul]`. Establish `hPpPp : Pp * Pp = Pp`.

Simplify using `only [hPp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]`. Use `module`. Establish `hPmPm : Pm * Pm = Pm`. Simplify using `only [hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHH]`. Use `module`.

Establish `hPpPm : Pp * Pm = 0`. Simplify using `only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHH]`. Use `module`. Establish `hPmPp : Pm * Pp = 0`. Simplify using `only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]`.

Use `module`. Establish `hsum : Pp + Pm = 1` using `by rw [hPp, hPm]; module`. Establish `hHdec : H = Pp - Pm` using `by rw [hPp, hPm]; module`. Establish `h2' : Aᴴ * (H * A) = Bᴴ * (H * B)` using `by simpa only [Matrix.mul_assoc] using h2`. Establish `gramP : ∀ Z : Matrix (Fin n) (Fin m) ℂ, (Pp * Z)ᴴ * (Pp * Z) = (1 / 2 : ℂ) • (Zᴴ * Z + Zᴴ * (H * Z))`.

Introduce `Z`. Rewrite using `[conjTranspose_mul, hPpH, Matrix.mul_assoc, ← Matrix.mul_assoc Pp, hPpPp, hPp]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul]`. Establish `gramM : ∀ Z : Matrix (Fin n) (Fin m) ℂ, (Pm * Z)ᴴ * (Pm * Z) = (1 / 2 : ℂ) • (Zᴴ * Z - Zᴴ * (H * Z))`. Introduce `Z`.

Rewrite using `[conjTranspose_mul, hPmH, Matrix.mul_assoc, ← Matrix.mul_assoc Pm, hPmPm, hPm]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]`. Take `⟨Wp, hWpu, hWpP, hWpA⟩` from `exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pm hPmH (Pp * A) (Pp * B) (by rw [gramP, gramP, h1, h2']) (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul]) (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])`. Take `⟨Wm, hWmu, hWmP, hWmA⟩` from `exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pp hPpH (Pm * A) (Pm * B) (by rw [gramM, gramM, h1, h2']) (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul]) (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])`. Establish `hWpHPm : Wpᴴ * Pm = Pm` using `by rw [← hWpP, ← Matrix.mul_assoc, hWpu, Matrix.one_mul, hWpP]`.

Establish `hWmHPp : Wmᴴ * Pp = Pp` using `by rw [← hWmP, ← Matrix.mul_assoc, hWmu, Matrix.one_mul, hWmP]`. Establish `hPmWp : Pm * Wp = Pm`. Use `congrArg conjTranspose hWpHPm` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_conjTranspose, hPmH]`. Then use the resulting hypothesis. Establish `hPpWm : Pp * Wm = Pp`.

Use `congrArg conjTranspose hWmHPp` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_conjTranspose, hPpH]`. Then use the resulting hypothesis. Establish `hA : Pp * Wp * Pp = Wp * Pp` using `calc Pp * Wp * Pp = (Pp + Pm) * Wp * Pp - Pm * Wp * Pp := by`. Rewrite using `[Matrix.add_mul, Matrix.add_mul]`. Normalize the expressions using the abelian group laws.

Use `_ = Wp * Pp := by rw [hsum, Matrix.one_mul, hPmWp, hPmPp, sub_zero]`. Establish `hB : Pm * Wm * Pm = Wm * Pm` using `calc Pm * Wm * Pm = (Pp + Pm) * Wm * Pm - Pp * Wm * Pm := by`. Rewrite using `[Matrix.add_mul, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Use `_ = Wm * Pm := by rw [hsum, Matrix.one_mul, hPpWm, hPpPm, sub_zero]`.

Establish `hX1 : Pp * Wpᴴ * Wp = Pp` using `by rw [Matrix.mul_assoc, hWpu, Matrix.mul_one]`. Establish `hX2 : Pm * Wmᴴ * Wm = Pm` using `by rw [Matrix.mul_assoc, hWmu, Matrix.mul_one]`. Establish `hX3 : Pp * Wpᴴ * Wm * Pm = 0` using `calc Pp * Wpᴴ * Wm * Pm = Pp * Wpᴴ * (Pm * Wm * Pm) := by rw [hB, Matrix.mul_assoc (Pp * Wpᴴ)] _ = Pp * (Wpᴴ * Pm) * Wm * Pm := by simp only [Matrix.mul_assoc] _ = 0 := by rw [hWpHPm, hPpPm, Matrix.zero_mul, Matrix.zero_mul]`. Establish `hX4 : Pm * Wmᴴ * Wp * Pp = 0` using `calc Pm * Wmᴴ * Wp * Pp = Pm * Wmᴴ * (Pp * Wp * Pp) := by rw [hA, Matrix.mul_assoc (Pm * Wmᴴ)] _ = Pm * (Wmᴴ * Pp) * Wp * Pp := by simp only [Matrix.mul_assoc] _ = 0 := by rw [hWmHPp, hPmPp, Matrix.zero_mul, Matrix.zero_mul]`. Use `⟨Wp * Pp + Wm * Pm, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [conjTranspose_add, conjTranspose_mul, hPpH, hPmH, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, hX1, hX2, hX3, hX4, hPpPp, hPmPm]`. Rewrite using `[add_zero, zero_add, hsum]`. Establish `hUH : (Wp * Pp + Wm * Pm) * H = Wp * Pp - Wm * Pm`. Rewrite using `[hHdec]`. Simplify using `only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, hPpPp, hPpPm, hPmPp, hPmPm, Matrix.mul_zero]`.

Normalize the expressions using the abelian group laws. Establish `hHU : H * (Wp * Pp + Wm * Pm) = Wp * Pp - Wm * Pm`. Rewrite using `[hHdec]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_add, ← Matrix.mul_assoc, hPpWm, hPmWp, hPpPm, hPmPp, hA, hB]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hUH, hHU]`. Rewrite using `[Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWpA, hWmA, ← Matrix.add_mul, hsum, Matrix.one_mul]`.
-/
theorem _root_.GlobalTheory.HCXi.exists_unitary_comm_mul_eq_of_gram {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  obtain ⟨Pp, hPp⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 + H) := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 - H) := ⟨_, rfl⟩
  have hPpH : Ppᴴ = Pp := by simp [hPp, hH, conjTranspose_smul]
  have hPmH : Pmᴴ = Pm := by simp [hPm, hH, conjTranspose_smul]
  have hPpPp : Pp * Pp = Pp := by
    simp only [hPp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPm : Pm * Pm = Pm := by
    simp only [hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPpPm : Pp * Pm = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPp : Pm * Pp = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hsum : Pp + Pm = 1 := by rw [hPp, hPm]; module
  have hHdec : H = Pp - Pm := by rw [hPp, hPm]; module
  have h2' : Aᴴ * (H * A) = Bᴴ * (H * B) := by simpa only [Matrix.mul_assoc] using h2
  have gramP : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pp * Z)ᴴ * (Pp * Z) = (1 / 2 : ℂ) • (Zᴴ * Z + Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPpH, Matrix.mul_assoc, ← Matrix.mul_assoc Pp, hPpPp, hPp]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul]
  have gramM : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pm * Z)ᴴ * (Pm * Z) = (1 / 2 : ℂ) • (Zᴴ * Z - Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPmH, Matrix.mul_assoc, ← Matrix.mul_assoc Pm, hPmPm, hPm]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
  obtain ⟨Wp, hWpu, hWpP, hWpA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pm hPmH (Pp * A) (Pp * B)
    (by rw [gramP, gramP, h1, h2']) (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
  obtain ⟨Wm, hWmu, hWmP, hWmA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pp hPpH (Pm * A) (Pm * B)
    (by rw [gramM, gramM, h1, h2']) (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
  have hWpHPm : Wpᴴ * Pm = Pm := by rw [← hWpP, ← Matrix.mul_assoc, hWpu, Matrix.one_mul, hWpP]
  have hWmHPp : Wmᴴ * Pp = Pp := by rw [← hWmP, ← Matrix.mul_assoc, hWmu, Matrix.one_mul, hWmP]
  have hPmWp : Pm * Wp = Pm := by
    have := congrArg conjTranspose hWpHPm
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPmH] at this
  have hPpWm : Pp * Wm = Pp := by
    have := congrArg conjTranspose hWmHPp
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPpH] at this
  have hA : Pp * Wp * Pp = Wp * Pp := calc
    Pp * Wp * Pp = (Pp + Pm) * Wp * Pp - Pm * Wp * Pp := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wp * Pp := by rw [hsum, Matrix.one_mul, hPmWp, hPmPp, sub_zero]
  have hB : Pm * Wm * Pm = Wm * Pm := calc
    Pm * Wm * Pm = (Pp + Pm) * Wm * Pm - Pp * Wm * Pm := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wm * Pm := by rw [hsum, Matrix.one_mul, hPpWm, hPpPm, sub_zero]
  have hX1 : Pp * Wpᴴ * Wp = Pp := by rw [Matrix.mul_assoc, hWpu, Matrix.mul_one]
  have hX2 : Pm * Wmᴴ * Wm = Pm := by rw [Matrix.mul_assoc, hWmu, Matrix.mul_one]
  have hX3 : Pp * Wpᴴ * Wm * Pm = 0 := calc
    Pp * Wpᴴ * Wm * Pm = Pp * Wpᴴ * (Pm * Wm * Pm) := by rw [hB, Matrix.mul_assoc (Pp * Wpᴴ)]
    _ = Pp * (Wpᴴ * Pm) * Wm * Pm := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWpHPm, hPpPm, Matrix.zero_mul, Matrix.zero_mul]
  have hX4 : Pm * Wmᴴ * Wp * Pp = 0 := calc
    Pm * Wmᴴ * Wp * Pp = Pm * Wmᴴ * (Pp * Wp * Pp) := by rw [hA, Matrix.mul_assoc (Pm * Wmᴴ)]
    _ = Pm * (Wmᴴ * Pp) * Wp * Pp := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWmHPp, hPmPp, Matrix.zero_mul, Matrix.zero_mul]
  refine ⟨Wp * Pp + Wm * Pm, ?_, ?_, ?_⟩
  · simp only [conjTranspose_add, conjTranspose_mul, hPpH, hPmH, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, hX1, hX2, hX3, hX4, hPpPp, hPmPm]
    rw [add_zero, zero_add, hsum]
  · have hUH : (Wp * Pp + Wm * Pm) * H = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, hPpPp, hPpPm, hPmPp, hPmPm,
        Matrix.mul_zero]
      abel
    have hHU : H * (Wp * Pp + Wm * Pm) = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.sub_mul, Matrix.mul_add, ← Matrix.mul_assoc, hPpWm, hPmWp, hPpPm, hPmPp,
        hA, hB]
      abel
    rw [hUH, hHU]
  · rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWpA, hWmA, ← Matrix.add_mul, hsum,
      Matrix.one_mul]

end GlobalTheory.HCXi
