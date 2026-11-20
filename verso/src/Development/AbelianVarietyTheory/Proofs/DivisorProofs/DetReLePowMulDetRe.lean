import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitianStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
namespace GlobalTheory.HSAmp

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec_single, dotProduct_single]`.
-/
theorem star_mulVec_single_dot (ι : Type) [Fintype ι] [DecidableEq ι]
    (T M : Matrix ι ι ℂ) (i : ι) :
    star (T *ᵥ Pi.single i 1) ⬝ᵥ M *ᵥ (T *ᵥ Pi.single i 1) = (Tᴴ * M * T) i i := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_single, dotProduct_single]

/- English proof (translation)
Take `⟨T, d, hT, hTB, hTA⟩` from `GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι B A hB hA.isHermitian`. Establish `hTu : IsUnit T` using `(Matrix.isUnit_iff_isUnit_det T).2 hT`. Establish `hinj : Function.Injective T.mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 hTu`. Establish `hcol : ∀ i, T *ᵥ Pi.single i 1 ≠ 0`. Introduce `i h`.

Establish `: Pi.single i (1 : ℂ) = 0` using `hinj (by rw [h, Matrix.mulVec_zero])`. Simplify using `using congrFun this i`. Establish `hBi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ B *ᵥ (T *ᵥ Pi.single i 1) = 1`. Introduce `i`. Rewrite using `[star_mulVec_single_dot, hTB]`.

Simplify using the standard rewrite rules. Establish `hAi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ A *ᵥ (T *ᵥ Pi.single i 1) = (d i : ℂ)`. Introduce `i`. Rewrite using `[star_mulVec_single_dot, hTA]`. Simplify using the standard rewrite rules.

Establish `hdpos : ∀ i, 0 < d i`. Introduce `i`. Establish `h` using `hA.dotProduct_mulVec_pos (hcol i)`. Rewrite `h` using `[hAi]`. Conclude with `h` after adjusting the coercions.

Establish `hdle : ∀ i, d i ≤ κ`. Introduce `i`. Establish `h` using `hle (T *ᵥ Pi.single i 1)`. Rewrite `h` using `[hAi, hBi]`. Simplify using `using h`.

Use `set t := T.det`. Establish `hn : (Complex.normSq t : ℂ) = star t * t` using `Complex.normSq_eq_conj_mul_self`. Establish `hdetB : (Complex.normSq t : ℂ) * B.det = 1`. Use `congrArg Matrix.det hTB` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]`.

Rewrite using `[hn, ← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdetA : (Complex.normSq t : ℂ) * A.det = ((∏ i, d i : ℝ) : ℂ)`. Use `congrArg Matrix.det hTA` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]`.

Rewrite using `[hn, Complex.ofReal_prod, ← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < Complex.normSq t` using `Complex.normSq_pos.2 hT.ne_zero`. Establish `hBre : Complex.normSq t * B.det.re = 1`. Use `congrArg Complex.re hdetB` as an intermediate fact.

Simplify `this` using `[Complex.re_ofReal_mul]`. Establish `hAre : Complex.normSq t * A.det.re = ∏ i, d i`. Use `congrArg Complex.re hdetA` as an intermediate fact. Rewrite `this` using `[Complex.re_ofReal_mul, Complex.ofReal_re]`. Then use the resulting hypothesis. Establish `hprod : ∏ i, d i ≤ κ ^ Fintype.card ι`.

Combine the equalities or inequalities in the displayed calculation. Use `le_of_mul_le_mul_left ?_ hpos` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_left_comm, hBre, mul_one]`.
-/
theorem det_re_le_pow_mul_det_re (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (κ : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hle : ∀ c : ι → ℂ, (star c ⬝ᵥ A *ᵥ c).re ≤ κ * (star c ⬝ᵥ B *ᵥ c).re) :
    A.det.re ≤ κ ^ Fintype.card ι * B.det.re := by
  obtain ⟨T, d, hT, hTB, hTA⟩ := GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι B A hB hA.isHermitian
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 hT
  have hinj : Function.Injective T.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hTu

  have hcol : ∀ i, T *ᵥ Pi.single i 1 ≠ 0 := by
    intro i h
    have : Pi.single i (1 : ℂ) = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    simpa using congrFun this i
  have hBi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ B *ᵥ (T *ᵥ Pi.single i 1) = 1 := by
    intro i; rw [star_mulVec_single_dot, hTB]; simp
  have hAi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ A *ᵥ (T *ᵥ Pi.single i 1) = (d i : ℂ) := by
    intro i; rw [star_mulVec_single_dot, hTA]; simp
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have h := hA.dotProduct_mulVec_pos (hcol i)
    rw [hAi] at h
    exact_mod_cast h
  have hdle : ∀ i, d i ≤ κ := by
    intro i
    have h := hle (T *ᵥ Pi.single i 1)
    rw [hAi, hBi] at h
    simpa using h

  set t := T.det
  have hn : (Complex.normSq t : ℂ) = star t * t := Complex.normSq_eq_conj_mul_self
  have hdetB : (Complex.normSq t : ℂ) * B.det = 1 := by
    have := congrArg Matrix.det hTB
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    rw [hn, ← this]; ring
  have hdetA : (Complex.normSq t : ℂ) * A.det = ((∏ i, d i : ℝ) : ℂ) := by
    have := congrArg Matrix.det hTA
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal] at this
    rw [hn, Complex.ofReal_prod, ← this]; ring
  have hpos : 0 < Complex.normSq t := Complex.normSq_pos.2 hT.ne_zero
  have hBre : Complex.normSq t * B.det.re = 1 := by
    have := congrArg Complex.re hdetB
    simpa [Complex.re_ofReal_mul] using this
  have hAre : Complex.normSq t * A.det.re = ∏ i, d i := by
    have := congrArg Complex.re hdetA
    rwa [Complex.re_ofReal_mul, Complex.ofReal_re] at this
  have hprod : ∏ i, d i ≤ κ ^ Fintype.card ι := by
    calc ∏ i, d i ≤ ∏ _i : ι, κ :=
          Finset.prod_le_prod (fun i _ => (hdpos i).le) (fun i _ => hdle i)
      _ = κ ^ Fintype.card ι := by simp
  refine le_of_mul_le_mul_left ?_ hpos
  calc Complex.normSq t * A.det.re = ∏ i, d i := hAre
    _ ≤ κ ^ Fintype.card ι := hprod
    _ = Complex.normSq t * (κ ^ Fintype.card ι * B.det.re) := by
        rw [mul_left_comm, hBre, mul_one]

end GlobalTheory.HSAmp
