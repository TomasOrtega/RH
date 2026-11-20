import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

/- English proof (translation)
Simplify using `[toBlocks₁₁_mul', Cm, Matrix.mul_smul]`.
-/
theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂ := by
  simp [toBlocks₁₁_mul', Cm, Matrix.mul_smul]

/- English proof (translation)
Simplify using `only [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring`.
-/
theorem cmS : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0
    ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/- English proof (translation)
Rewrite using `[← fromBlocks_one, fromBlocks_smul]`. Simplify using `only [Cmi, fromBlocks_conjTranspose, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring`.
-/
theorem cmiH_cmi : (Cmi n)ᴴ * Cmi n = (1 / 2 : ℂ) • (1 : M2 n) := by
  rw [← fromBlocks_one, fromBlocks_smul]
  simp only [Cmi, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 cm_mul_cmi`.
-/
theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.1 cm_mul_cmi

/- English proof (translation)
Simplify using `[mR, Matrix.coe_units_inv]`.
-/
theorem mR_inv_mul (y y' : GR n) : mR (y⁻¹ * y') = (mR y)⁻¹ * mR y' := by
  simp [mR, Matrix.coe_units_inv]

/- English proof (translation)
The claim follows from `(y.1).isUnit`.
-/
theorem isUnit_mR (y : GR n) : IsUnit (mR y) := (y.1).isUnit

/- English proof (translation)
Introduce `n y y' hz`. Establish `hGk : InG (mR (y⁻¹ * y'))` using `(y⁻¹ * y').2`. Use `⟨hGk, ?_⟩` and prove the remaining obligations. Use `set x := mR y with hxdef`. Use `set x' := mR y' with hx'def`.

Use `set k := mR (y⁻¹ * y') with hkdef`. Establish `hkxx : k = x⁻¹ * x'` using `mR_inv_mul y y'`. Establish `hxu : IsUnit x` using `isUnit_mR y`. Establish `hxdet : IsUnit x.det` using `(Matrix.isUnit_iff_isUnit_det x).1 hxu`. Establish `hu1 : (u1 x).det ≠ 0` using `(detU1 n y).1`.

Establish `hu1' : (u1 x').det ≠ 0` using `(detU1 n y').1`. Establish `hu1u : IsUnit (u1 x).det` using `isUnit_iff_ne_zero.2 hu1`. Establish `hu1u' : IsUnit (u1 x').det` using `isUnit_iff_ne_zero.2 hu1'`. Use `set c := (u1 x)⁻¹ * u1 x' with hc`. Establish `h21 : (x' * Cm n).toBlocks₂₁ = (x * Cm n).toBlocks₂₁ * c`.

Rewrite using `[mul_cm₂₁, mul_cm₂₁, hc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1u, Matrix.one_mul]`. Establish `h11 : (x' * Cm n).toBlocks₁₁ = (x * Cm n).toBlocks₁₁ * c`. Rewrite using `[mul_cm₁₁, mul_cm₁₁]`. Establish `hz' : (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹ = (Complex.I • x'.toBlocks₁₁ + x'.toBlocks₁₂) * (u1 x')⁻¹` using `hz`. Use `congrArg (· * u1 x') hz'` as an intermediate fact.

Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1u', Matrix.mul_one] at this`. Rewrite using `[hc]`. Conclude with `this.symm`. Use `set D := Cmi n * k * Cm n with hD`. Establish `hDE : D * fromBlocks 1 0 0 0 = fromBlocks c 0 0 0`.

Establish `e1 : x' * Cm n * fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 0 = x * Cm n * fromBlocks c 0 0 0` using `by conv_lhs => rw [← fromBlocks_toBlocks (x' * Cm n), fromBlocks_multiply] conv_rhs => rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_multiply]`. Rewrite using `[h11, h21]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hD, hkxx]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Cmi n * x⁻¹ * (x * Cm n * fromBlocks c 0 0 0) := by rw [e1]`. Use `_ = Cmi n * (x⁻¹ * x) * Cm n * fromBlocks c 0 0 0 := by simp only [Matrix.mul_assoc]`. Use `_ = fromBlocks c 0 0 0 := by`. Rewrite using `[Matrix.nonsing_inv_mul _ hxdet, Matrix.mul_one, cmi_mul_cm, Matrix.one_mul]`.

Establish `hD0 : D = fromBlocks c D.toBlocks₁₂ 0 D.toBlocks₂₂`. Use `hDE` as an intermediate fact. Use `conv_lhs at this => rw [← fromBlocks_toBlocks D, fromBlocks_multiply]`. Simplify using `only [Matrix.mul_one, Matrix.mul_zero, add_zero] at this`. Take `⟨e11, -, e21, -⟩` from `Matrix.fromBlocks_inj.1 this`.

Use `conv_lhs => rw [← fromBlocks_toBlocks D]`. Rewrite using `[e11, e21]`. Establish `hk : kᴴ * JJ n * k = JJ n` using `hGk`. Establish `hS : Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D = (Cm n)ᴴ * JJ n * Cm n`. Establish `hcc : (Cmi n)ᴴ * (Cm n)ᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, cm_mul_cmi, Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hD]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (Cm n)ᴴ * (kᴴ * JJ n * k) * Cm n := by`.

Rewrite using `[hcc, cm_mul_cmi]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = (Cm n)ᴴ * JJ n * Cm n := by rw [hk]`. Rewrite `hS` using `[cmS, hD0]`. Simplify using `only [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hS`.

Take `⟨s11, s12, -, s22⟩` from `Matrix.fromBlocks_inj.1 hS`. Establish `hI : (-2 * Complex.I) ≠ 0` using `by simp [Complex.ext_iff]`. Establish `hI' : (2 * Complex.I) ≠ 0` using `by simp [Complex.ext_iff]`. Establish `hcc : cᴴ * c = 1`. Use `congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s11` as an intermediate fact.

Simplify `this` using `[smul_smul, inv_mul_cancel₀ hI]`. Establish `hcc' : c * cᴴ = 1` using `mul_eq_one_comm.1 hcc`. Establish `hB : D.toBlocks₁₂ = 0`. Establish `h1 : cᴴ * D.toBlocks₁₂ = 0`. Use `congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s12` as an intermediate fact.

Simplify `this` using `[smul_smul, inv_mul_cancel₀ hI]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc' : (D.toBlocks₂₂)ᴴ * D.toBlocks₂₂ = 1`. Rewrite `s22` using `[hB]`. Simplify using `only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, smul_zero] at s22`.

Use `congrArg (fun M => (2 * Complex.I)⁻¹ • M) s22` as an intermediate fact. Simplify `this` using `[smul_smul, inv_mul_cancel₀ hI']`. Establish `hDD : Dᴴ * D = 1`. Rewrite using `[hD0, hB, fromBlocks_conjTranspose, fromBlocks_multiply, hcc, hc', ← fromBlocks_one]`. Simplify using the standard rewrite rules.

Establish `hkD : k = Cm n * D * Cmi n`. Rewrite using `[hD]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[cm_mul_cmi, Matrix.one_mul, Matrix.mul_assoc, cm_mul_cmi, Matrix.mul_one]`. Establish `hcm2 : (Cm n)ᴴ * Cm n = (2 : ℂ) • (1 : M2 n)`.

Rewrite using `[← fromBlocks_one, fromBlocks_smul]`. Simplify using `only [Cm, fromBlocks_conjTranspose, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hkD]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (2 : ℂ) • ((Cmi n)ᴴ * Cmi n) := by`. Rewrite using `[hcm2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Use `_ = 1 := by rw [cmiH_cmi, smul_smul]; norm_num`.
-/
theorem fib : Fib := by
  intro n y y' hz
  have hGk : InG (mR (y⁻¹ * y')) := (y⁻¹ * y').2
  refine ⟨hGk, ?_⟩
  set x := mR y with hxdef
  set x' := mR y' with hx'def
  set k := mR (y⁻¹ * y') with hkdef
  have hkxx : k = x⁻¹ * x' := mR_inv_mul y y'
  have hxu : IsUnit x := isUnit_mR y
  have hxdet : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hxu
  have hu1 : (u1 x).det ≠ 0 := (detU1 n y).1
  have hu1' : (u1 x').det ≠ 0 := (detU1 n y').1
  have hu1u : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 hu1
  have hu1u' : IsUnit (u1 x').det := isUnit_iff_ne_zero.2 hu1'
  set c := (u1 x)⁻¹ * u1 x' with hc

  have h21 : (x' * Cm n).toBlocks₂₁ = (x * Cm n).toBlocks₂₁ * c := by
    rw [mul_cm₂₁, mul_cm₂₁, hc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1u, Matrix.one_mul]
  have h11 : (x' * Cm n).toBlocks₁₁ = (x * Cm n).toBlocks₁₁ * c := by
    rw [mul_cm₁₁, mul_cm₁₁]
    have hz' : (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹ =
        (Complex.I • x'.toBlocks₁₁ + x'.toBlocks₁₂) * (u1 x')⁻¹ := hz
    have := congrArg (· * u1 x') hz'
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1u', Matrix.mul_one] at this
    rw [hc]; exact this.symm

  set D := Cmi n * k * Cm n with hD
  have hDE : D * fromBlocks 1 0 0 0 = fromBlocks c 0 0 0 := by
    have e1 : x' * Cm n * fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 0 =
        x * Cm n * fromBlocks c 0 0 0 := by
      conv_lhs => rw [← fromBlocks_toBlocks (x' * Cm n), fromBlocks_multiply]
      conv_rhs => rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_multiply]
      rw [h11, h21]; simp
    calc D * fromBlocks 1 0 0 0 = Cmi n * x⁻¹ * (x' * Cm n * fromBlocks 1 0 0 0) := by
          rw [hD, hkxx]; simp only [Matrix.mul_assoc]
      _ = Cmi n * x⁻¹ * (x * Cm n * fromBlocks c 0 0 0) := by rw [e1]
      _ = Cmi n * (x⁻¹ * x) * Cm n * fromBlocks c 0 0 0 := by simp only [Matrix.mul_assoc]
      _ = fromBlocks c 0 0 0 := by
          rw [Matrix.nonsing_inv_mul _ hxdet, Matrix.mul_one, cmi_mul_cm, Matrix.one_mul]
  have hD0 : D = fromBlocks c D.toBlocks₁₂ 0 D.toBlocks₂₂ := by
    have := hDE
    conv_lhs at this => rw [← fromBlocks_toBlocks D, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at this
    obtain ⟨e11, -, e21, -⟩ := Matrix.fromBlocks_inj.1 this
    conv_lhs => rw [← fromBlocks_toBlocks D]
    rw [e11, e21]

  have hk : kᴴ * JJ n * k = JJ n := hGk
  have hS : Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D = (Cm n)ᴴ * JJ n * Cm n := by
    have hcc : (Cmi n)ᴴ * (Cm n)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, cm_mul_cmi, Matrix.conjTranspose_one]
    calc Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D
        = (Cm n)ᴴ * kᴴ * ((Cmi n)ᴴ * (Cm n)ᴴ) * JJ n * (Cm n * Cmi n) * k * Cm n := by
          rw [hD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * (kᴴ * JJ n * k) * Cm n := by
          rw [hcc, cm_mul_cmi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * JJ n * Cm n := by rw [hk]
  rw [cmS, hD0] at hS
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hS
  obtain ⟨s11, s12, -, s22⟩ := Matrix.fromBlocks_inj.1 hS
  have hI : (-2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hI' : (2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hcc : cᴴ * c = 1 := by
    have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s11
    simpa [smul_smul, inv_mul_cancel₀ hI] using this
  have hcc' : c * cᴴ = 1 := mul_eq_one_comm.1 hcc
  have hB : D.toBlocks₁₂ = 0 := by
    have h1 : cᴴ * D.toBlocks₁₂ = 0 := by
      have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s12
      simpa [smul_smul, inv_mul_cancel₀ hI] using this
    calc D.toBlocks₁₂ = c * cᴴ * D.toBlocks₁₂ := by rw [hcc', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have hc' : (D.toBlocks₂₂)ᴴ * D.toBlocks₂₂ = 1 := by
    rw [hB] at s22
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, smul_zero] at s22
    have := congrArg (fun M => (2 * Complex.I)⁻¹ • M) s22
    simpa [smul_smul, inv_mul_cancel₀ hI'] using this
  have hDD : Dᴴ * D = 1 := by
    rw [hD0, hB, fromBlocks_conjTranspose, fromBlocks_multiply, hcc, hc', ← fromBlocks_one]
    simp

  have hkD : k = Cm n * D * Cmi n := by
    rw [hD]; simp only [← Matrix.mul_assoc]
    rw [cm_mul_cmi, Matrix.one_mul, Matrix.mul_assoc, cm_mul_cmi, Matrix.mul_one]
  have hcm2 : (Cm n)ᴴ * Cm n = (2 : ℂ) • (1 : M2 n) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [Cm, fromBlocks_conjTranspose, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  calc kᴴ * k = (Cmi n)ᴴ * (Dᴴ * ((Cm n)ᴴ * Cm n) * D) * Cmi n := by
        rw [hkD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (2 : ℂ) • ((Cmi n)ᴴ * Cmi n) := by
        rw [hcm2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDD, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]
    _ = 1 := by rw [cmiH_cmi, smul_smul]; norm_num

end PositivityTheory.Rg.Sw.HSt
