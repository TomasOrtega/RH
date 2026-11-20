import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

noncomputable section

namespace GlobalTheory.MatrixHomBijective

variable {F : Type} [Field F] [CharZero F]

/- English proof (translation)
Establish `hs : s ≠ 0`. Introduce and unpack `rfl`. Establish `: a * t ^ 2 ≠ 0` using `mul_ne_zero ha (pow_ne_zero 2 ht)`. Conclude with `this (by rw [← h]; ring)`. Establish `ha' : a = s ^ 2 / t ^ 2`.

Rewrite using `[h]`. Clear the denominators using the available nonvanishing facts. Use `⟨(b + 1) / 2, (b - 1) * t / (2 * s), ?_⟩` and prove the remaining obligations. Rewrite using `[ha']`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rep_of_sq {a b s t : F} (ha : a ≠ 0) (ht : t ≠ 0) (h : s ^ 2 = a * t ^ 2) :
    ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  have hs : s ≠ 0 := by
    rintro rfl
    have : a * t ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 ht)
    exact this (by rw [← h]; ring)
  have ha' : a = s ^ 2 / t ^ 2 := by
    rw [h]; field_simp
  refine ⟨(b + 1) / 2, (b - 1) * t / (2 * s), ?_⟩
  rw [ha']
  field_simp
  ring

/- English proof (translation)
Take `⟨x0, x1, x2, x3⟩` from `x`. Simplify using `only [GlobalTheory.QSA.nrm] at hn`. Distinguish the cases in `hd : x2 ^ 2 - a * x3 ^ 2 = 0`. Distinguish the cases in `h3 : x3 = 0`. Substitute `h3` using the available equality.

Establish `h2 : x2 = 0`. Establish `: x2 ^ 2 = 0` using `by linear_combination hd`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 this`. Substitute `h2` using the available equality. Establish `h1 : x1 ≠ 0`.

Introduce and unpack `rfl`. Establish `: x0 ^ 2 = 0` using `by linear_combination hn`. Establish `h0 : x0 = 0` using `pow_eq_zero_iff (two_ne_zero) |>.1 this`. Substitute `h0` using the available equality. Conclude with `hx rfl`.

Conclude with `rep_of_sq (s := x0) ha h1 (by linear_combination hn)`. Conclude with `rep_of_sq (s := x2) ha h3 (by linear_combination hd)`. Use `⟨(x0 * x2 - a * x1 * x3) / (x2 ^ 2 - a * x3 ^ 2), (x1 * x2 - x0 * x3) / (x2 ^ 2 - a * x3 ^ 2), ?_⟩` and prove the remaining obligations. Take `⟨d, hdd⟩ : ∃ d, d = x2 ^ 2 - a * x3 ^ 2` from `⟨_, rfl⟩`. Rewrite `hd`, the goal using `[← hdd]`.

Establish `key : b * d ^ 2 = (x0 * x2 - a * x1 * x3) ^ 2 - a * (x1 * x2 - x0 * x3) ^ 2`. Rewrite using `[hdd]`. Take the linear combination `(-(x2 ^ 2 - a * x3 ^ 2)) * hn`. Clear the denominators using the available nonvanishing facts. Take the linear combination `key`.
-/
theorem rep_of_isotropic {a b : F} (ha : a ≠ 0) (x : QuaternionAlgebra F a 0 b) (hx : x ≠ 0)
    (hn : GlobalTheory.QSA.nrm x = 0) : ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [GlobalTheory.QSA.nrm] at hn
  by_cases hd : x2 ^ 2 - a * x3 ^ 2 = 0
  · by_cases h3 : x3 = 0
    · subst h3
      have h2 : x2 = 0 := by
        have : x2 ^ 2 = 0 := by linear_combination hd
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      subst h2
      have h1 : x1 ≠ 0 := by
        rintro rfl
        have : x0 ^ 2 = 0 := by linear_combination hn
        have h0 : x0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
        subst h0
        exact hx rfl
      exact rep_of_sq (s := x0) ha h1 (by linear_combination hn)
    · exact rep_of_sq (s := x2) ha h3 (by linear_combination hd)
  · refine ⟨(x0 * x2 - a * x1 * x3) / (x2 ^ 2 - a * x3 ^ 2),
      (x1 * x2 - x0 * x3) / (x2 ^ 2 - a * x3 ^ 2), ?_⟩
    obtain ⟨d, hdd⟩ : ∃ d, d = x2 ^ 2 - a * x3 ^ 2 := ⟨_, rfl⟩
    rw [← hdd] at hd ⊢
    have key : b * d ^ 2 = (x0 * x2 - a * x1 * x3) ^ 2 - a * (x1 * x2 - x0 * x3) ^ 2 := by
      rw [hdd]
      linear_combination (-(x2 ^ 2 - a * x3 ^ 2)) * hn
    field_simp
    linear_combination key

def mat {a b : F} (p q : F) (x : QuaternionAlgebra F a 0 b) : Matrix (Fin 2) (Fin 2) F :=
  !![x.re + p * x.imJ + a * q * x.imK, a * x.imI - a * q * x.imJ - a * p * x.imK;
    x.imI + q * x.imJ + p * x.imK, x.re - p * x.imJ - a * q * x.imK]

def hom {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    QuaternionAlgebra F a 0 b →ₐ[F] Matrix (Fin 2) (Fin 2) F where
  toFun := mat p q
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_mul' x y := by
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat, QuaternionAlgebra.algebraMap_eq, Matrix.algebraMap_matrix_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `e00` using `congrFun (congrFun hxy 0) 0`. Establish `e01` using `congrFun (congrFun hxy 0) 1`. Establish `e10` using `congrFun (congrFun hxy 1) 0`.

Establish `e11` using `congrFun (congrFun hxy 1) 1`. Simplify using `only [mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e00 e01 e10 e11`. Establish `two : (2 : F) ≠ 0` using `two_ne_zero`. Use `ext`. Apply `mul_left_cancel₀ two` to reduce the goal to its premises.

Take the linear combination `e00 + e11`. Apply `mul_left_cancel₀ (mul_ne_zero two ha)` to reduce the goal to its premises. Take the linear combination `e01 + a * e10`. Apply `mul_left_cancel₀ (mul_ne_zero two hb)` to reduce the goal to its premises. Take the linear combination `p * (e00 - e11) - q * (a * e10 - e01) + 2 * (x.imJ - y.imJ) * h`.

Apply `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two ha) hb)` to reduce the goal to its premises. Take the linear combination `p * (a * e10 - e01) - a * q * (e00 - e11) + 2 * a * (x.imK - y.imK) * h`. Introduce `M`. Use `⟨⟨(M 0 0 + M 1 1) / 2, (M 0 1 / a + M 1 0) / 2, (p * (M 0 0 - M 1 1) - q * (a * M 1 0 - M 0 1)) / (2 * b), (p * (a * M 1 0 - M 0 1) - a * q * (M 0 0 - M 1 1)) / (2 * a * b)⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [mat] <;> field_simp <;> rw [h] <;> ring`.
-/
theorem mat_bijective {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    Function.Bijective (mat (a := a) (b := b) p q) := by
  constructor
  · intro x y hxy
    have e00 := congrFun (congrFun hxy 0) 0
    have e01 := congrFun (congrFun hxy 0) 1
    have e10 := congrFun (congrFun hxy 1) 0
    have e11 := congrFun (congrFun hxy 1) 1
    simp only [mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at e00 e01 e10 e11
    have two : (2 : F) ≠ 0 := two_ne_zero
    ext
    · apply mul_left_cancel₀ two
      linear_combination e00 + e11
    · apply mul_left_cancel₀ (mul_ne_zero two ha)
      linear_combination e01 + a * e10
    · apply mul_left_cancel₀ (mul_ne_zero two hb)
      linear_combination p * (e00 - e11) - q * (a * e10 - e01) + 2 * (x.imJ - y.imJ) * h
    · apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two ha) hb)
      linear_combination p * (a * e10 - e01) - a * q * (e00 - e11) + 2 * a * (x.imK - y.imK) * h
  · intro M
    refine ⟨⟨(M 0 0 + M 1 1) / 2, (M 0 1 / a + M 1 0) / 2,
      (p * (M 0 0 - M 1 1) - q * (a * M 1 0 - M 0 1)) / (2 * b),
      (p * (a * M 1 0 - M 0 1) - a * q * (M 0 0 - M 1 1)) / (2 * a * b)⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> field_simp <;> rw [h] <;> ring

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `only [mat, Matrix.det_fin_two_of, GlobalTheory.QSA.nrm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mat {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) (x : QuaternionAlgebra F a 0 b) :
    (mat p q x).det = GlobalTheory.QSA.nrm x := by
  subst h
  simp only [mat, Matrix.det_fin_two_of, GlobalTheory.QSA.nrm]
  ring

/- English proof (translation)
Take `⟨x, hx, hn⟩` from `hx`. Take `⟨p, q, h⟩` from `rep_of_isotropic ha x hx hn`. Conclude with `⟨AlgEquiv.ofBijective (hom p q h) (mat_bijective ha hb p q h), fun y => det_mat p q h y⟩`.
-/
theorem split_of_isotropic (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : ∃ x : QuaternionAlgebra F a 0 b, x ≠ 0 ∧ GlobalTheory.QSA.nrm x = 0) :
    ∃ φ : QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F,
      ∀ x, Matrix.det (φ x) = GlobalTheory.QSA.nrm x := by
  obtain ⟨x, hx, hn⟩ := hx
  obtain ⟨p, q, h⟩ := rep_of_isotropic ha x hx hn
  exact ⟨AlgEquiv.ofBijective (hom p q h) (mat_bijective ha hb p q h), fun y => det_mat p q h y⟩

end GlobalTheory.MatrixHomBijective
