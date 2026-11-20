import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S
open GlobalTheory.DSSU (SUJ)
open GlobalTheory.SqIntSU (scalarMul unitScalar)

noncomputable section

namespace GlobalTheory.ExtChar

variable {n : ℕ} (ε : Fin n → Bool)

def detRoot (x : UJ ε) : Circle := Circle.exp (Complex.arg (umat x).det / n)

/- English proof (translation)
Establish `h1` using `GlobalTheory.SqIntSU.norm_det_umat ε x`. Rewrite using `[detRoot, Circle.coe_exp, ← Complex.exp_nat_mul]`. Establish `e : (n : ℂ) * (((Complex.arg (umat x).det / n : ℝ)) * Complex.I) = (Complex.arg (umat x).det : ℂ) * Complex.I`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Use `conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I (umat x).det, h1]`. Simplify using the standard rewrite rules.
-/
theorem detRoot_pow (hn : n ≠ 0) (x : UJ ε) : ((detRoot ε x : Circle) : ℂ) ^ n = (umat x).det := by
  have h1 := GlobalTheory.SqIntSU.norm_det_umat ε x
  rw [detRoot, Circle.coe_exp, ← Complex.exp_nat_mul]
  have e : (n : ℂ) * (((Complex.arg (umat x).det / n : ℝ)) * Complex.I) =
      (Complex.arg (umat x).det : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [e]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I (umat x).det, h1]
  simp

/- English proof (translation)
Rewrite using `[eq_comm, ← mul_eq_one_iff_eq_inv, ← GlobalTheory.SqIntSU.unitScalar_mul, inv_mul_cancel, GlobalTheory.SqIntSU.unitScalar_one]`.
-/
theorem unitScalar_inv (z : Circle) : (unitScalar ε z)⁻¹ = unitScalar ε z⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← GlobalTheory.SqIntSU.unitScalar_mul, inv_mul_cancel, GlobalTheory.SqIntSU.unitScalar_one]

/- English proof (translation)
Use `show ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * umat x).det = _`. Rewrite using `[Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Fintype.card_fin]`.
-/
theorem det_unitScalar_mul (z : Circle) (x : UJ ε) :
    (umat (unitScalar ε z * x)).det = (z : ℂ) ^ n * (umat x).det := by
  show ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * umat x).det = _
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Fintype.card_fin]

variable [NeZero n]

def root (x : UJ ε) (j : ZMod n) : Circle := detRoot ε x * ZMod.toCircle j

/- English proof (translation)
Establish `h : (ZMod.toCircle j : Circle) ^ n = 1`. Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]`. Rewrite using `[← Circle.coe_pow, h, Circle.coe_one]`.
-/
theorem toCircle_pow (j : ZMod n) : ((ZMod.toCircle j : Circle) : ℂ) ^ n = 1 := by
  have h : (ZMod.toCircle j : Circle) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  rw [← Circle.coe_pow, h, Circle.coe_one]

/- English proof (translation)
Rewrite using `[root, Circle.coe_mul, mul_pow, detRoot_pow ε (NeZero.ne n), toCircle_pow, mul_one]`.
-/
theorem root_pow (x : UJ ε) (j : ZMod n) : ((root ε x j : Circle) : ℂ) ^ n = (umat x).det := by
  rw [root, Circle.coe_mul, mul_pow, detRoot_pow ε (NeZero.ne n), toCircle_pow, mul_one]

def part (x : UJ ε) (j : ZMod n) : SUJ ε :=
  ⟨unitScalar ε (root ε x j)⁻¹ * x, by
    show (umat (unitScalar ε (root ε x j)⁻¹ * x)).det = 1
    rw [det_unitScalar_mul, Circle.coe_inv, inv_pow, root_pow, inv_mul_cancel₀]
    intro h0
    have := GlobalTheory.SqIntSU.norm_det_umat ε x
    rw [h0, norm_zero] at this
    exact zero_ne_one this⟩

def extChar (m : ℤ) (Θ' : SUJ ε → ℂ) (x : UJ ε) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j : ZMod n, ((root ε x j : Circle) : ℂ) ^ m * Θ' (part ε x j)

def cen (j : ZMod n) : SUJ ε :=
  ⟨unitScalar ε (ZMod.toCircle j)⁻¹, by
    show (umat (unitScalar ε (ZMod.toCircle j)⁻¹)).det = 1
    have h := det_unitScalar_mul ε (ZMod.toCircle j)⁻¹ 1
    rw [mul_one] at h
    rw [h, Circle.coe_inv, inv_pow, toCircle_pow, inv_one, one_mul]
    exact Matrix.det_one⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem suMat_cen (j : ZMod n) :
    GlobalTheory.SUChar.suMat ε (cen ε j) = ((ZMod.toCircle j)⁻¹ : Circle) • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl

def avgChar (m : ℤ) (Θ' : SUJ ε → ℂ) (g : SUJ ε) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j : ZMod n, ((ZMod.toCircle j : Circle) : ℂ) ^ m * Θ' (cen ε j * g)

end GlobalTheory.ExtChar

namespace GlobalTheory.ExtChar

variable {n : ℕ} (ε : Fin n → Bool) [NeZero n]

/- English proof (translation)
Establish `hu : (toUnits w : Circleˣ) ∈ rootsOfUnity n Circle`. Rewrite using `[mem_rootsOfUnity, ← map_pow, hw, map_one]`. Take `⟨i, hi⟩` from `(bijective_rootsOfUnityAddChar n).2 ⟨_, hu⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun u : rootsOfUnity n Circle => ((u : Circleˣ) : Circle)) hi`.

Simplify using `using h`.
-/
theorem exists_toCircle_eq (w : Circle) (hw : w ^ n = 1) : ∃ i : ZMod n, ZMod.toCircle i = w := by
  have hu : (toUnits w : Circleˣ) ∈ rootsOfUnity n Circle := by
    rw [mem_rootsOfUnity, ← map_pow, hw, map_one]
  obtain ⟨i, hi⟩ := (bijective_rootsOfUnityAddChar n).2 ⟨_, hu⟩
  refine ⟨i, ?_⟩
  have h := congrArg (fun u : rootsOfUnity n Circle => ((u : Circleˣ) : Circle)) hi
  simpa using h

/- English proof (translation)
Establish `hdet : (umat (scalarMul ε (z, g))).det = (z : ℂ) ^ n`. Rewrite using `[GlobalTheory.SqIntSU.scalarMul_apply, det_unitScalar_mul]`. Establish `: (umat (g : UJ ε)).det = 1` using `g.2`. Rewrite using `[this, mul_one]`. Establish `hd : detRoot ε (scalarMul ε (z, g)) ^ n = z ^ n` using `Circle.ext (by rw [Circle.coe_pow, Circle.coe_pow, detRoot_pow ε (NeZero.ne n), hdet])`.

Establish `hw : (detRoot ε (scalarMul ε (z, g)) * z⁻¹) ^ n = 1`. Rewrite using `[mul_pow, hd, inv_pow, mul_inv_cancel]`. Take `⟨i, hi⟩` from `exists_toCircle_eq (n := n) _ hw`. Use `⟨i, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[root, AddChar.map_add_eq_mul, hi, mul_comm (detRoot ε _) z⁻¹, mul_assoc, mul_inv_cancel_left]`.
-/
theorem root_scalarMul (z : Circle) (g : SUJ ε) :
    ∃ i : ZMod n, ∀ j, root ε (scalarMul ε (z, g)) j = z * ZMod.toCircle (i + j) := by
  have hdet : (umat (scalarMul ε (z, g))).det = (z : ℂ) ^ n := by
    rw [GlobalTheory.SqIntSU.scalarMul_apply, det_unitScalar_mul]
    have : (umat (g : UJ ε)).det = 1 := g.2
    rw [this, mul_one]
  have hd : detRoot ε (scalarMul ε (z, g)) ^ n = z ^ n :=
    Circle.ext (by rw [Circle.coe_pow, Circle.coe_pow, detRoot_pow ε (NeZero.ne n), hdet])
  have hw : (detRoot ε (scalarMul ε (z, g)) * z⁻¹) ^ n = 1 := by
    rw [mul_pow, hd, inv_pow, mul_inv_cancel]
  obtain ⟨i, hi⟩ := exists_toCircle_eq (n := n) _ hw
  refine ⟨i, fun j => ?_⟩
  rw [root, AddChar.map_add_eq_mul, hi, mul_comm (detRoot ε _) z⁻¹, mul_assoc, mul_inv_cancel_left]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show unitScalar ε (root ε (scalarMul ε (z, g)) j)⁻¹ * (unitScalar ε z * (g : UJ ε)) = unitScalar ε (ZMod.toCircle (i + j))⁻¹ * (g : UJ ε)`. Establish `e : (z * ZMod.toCircle (i + j))⁻¹ * z = (ZMod.toCircle (i + j))⁻¹`. Rewrite using `[mul_inv, mul_comm z⁻¹, mul_assoc, inv_mul_cancel, mul_one]`. Rewrite using `[h, ← mul_assoc, ← GlobalTheory.SqIntSU.unitScalar_mul, e]`.
-/
theorem part_scalarMul (z : Circle) (g : SUJ ε) (i : ZMod n)
    (h : ∀ j, root ε (scalarMul ε (z, g)) j = z * ZMod.toCircle (i + j)) (j : ZMod n) :
    part ε (scalarMul ε (z, g)) j = cen ε (i + j) * g := by
  apply Subtype.ext
  show unitScalar ε (root ε (scalarMul ε (z, g)) j)⁻¹ * (unitScalar ε z * (g : UJ ε)) =
    unitScalar ε (ZMod.toCircle (i + j))⁻¹ * (g : UJ ε)
  have e : (z * ZMod.toCircle (i + j))⁻¹ * z = (ZMod.toCircle (i + j))⁻¹ := by
    rw [mul_inv, mul_comm z⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  rw [h, ← mul_assoc, ← GlobalTheory.SqIntSU.unitScalar_mul, e]

/- English proof (translation)
Take `⟨i, hi⟩` from `root_scalarMul ε z g`. Rewrite using `[extChar, avgChar]`. Simplify using `only [hi, part_scalarMul ε z g i hi, Circle.coe_mul, mul_zpow, Finset.mul_sum]`. Conclude with `Fintype.sum_equiv (Equiv.addLeft i) _ _ fun j => by simp only [Equiv.coe_addLeft]; ring`.
-/
theorem extChar_scalarMul (m : ℤ) (Θ' : SUJ ε → ℂ) (z : Circle) (g : SUJ ε) :
    extChar ε m Θ' (scalarMul ε (z, g)) = (z : ℂ) ^ m * avgChar ε m Θ' g := by
  obtain ⟨i, hi⟩ := root_scalarMul ε z g
  rw [extChar, avgChar]
  simp only [hi, part_scalarMul ε z g i hi, Circle.coe_mul, mul_zpow, Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft i) _ _ fun j => by simp only [Equiv.coe_addLeft]; ring

end GlobalTheory.ExtChar
