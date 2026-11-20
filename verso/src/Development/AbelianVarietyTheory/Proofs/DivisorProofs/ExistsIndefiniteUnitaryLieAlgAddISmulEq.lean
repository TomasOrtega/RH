import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

/- English proof (translation)
Unfold `Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq`. Rewrite using `[Matrix.fromBlocks_conjTranspose]`. Simplify using the standard rewrite rules.
-/
theorem jm_conjTranspose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᴴ = Formalism.BasicNotions.TH.Jm p q := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/- English proof (translation)
Unfold `Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using `[Matrix.fromBlocks_one]`.
-/
theorem jm_mul_self (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q * Formalism.BasicNotions.TH.Jm p q = 1 := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/- English proof (translation)
Take `⟨J, hJ⟩ : ∃ J, J = Formalism.BasicNotions.TH.Jm p q` from `⟨_, rfl⟩`. Establish `hJh : Jᴴ = J` using `hJ ▸ jm_conjTranspose p q`. Establish `hJJ : J * J = 1` using `hJ ▸ jm_mul_self p q`. Use `⟨(1/2 : ℂ) • (Z - J * Zᴴ * J), ?_, (-(Complex.I / 2)) • (Z + J * Zᴴ * J), ?_, ?_⟩` and prove the remaining obligations. Use `show _ = _`.

Rewrite using `[← hJ]`. Simplify using `only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp [star_div₀]`. Rewrite using `[this]`.

Use `module`. Use `show _ = _`. Rewrite using `[← hJ]`. Simplify using `only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]`.

Establish `: star (-(Complex.I / 2)) = Complex.I / 2` using `by simp [star_div₀]; ring`. Rewrite using `[this]`. Use `module`. Rewrite using `[smul_smul]`. Establish `: Complex.I * -(Complex.I / 2) = 1 / 2`.

Rewrite using `[mul_neg, mul_div_assoc', Complex.I_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `module`.
-/
theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Formalism.BasicNotions.TH.Jm p q := ⟨_, rfl⟩
  have hJh : Jᴴ = J := hJ ▸ jm_conjTranspose p q
  have hJJ : J * J = 1 := hJ ▸ jm_mul_self p q
  refine ⟨(1/2 : ℂ) • (Z - J * Zᴴ * J), ?_, (-(Complex.I / 2)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp [star_div₀]
    rw [this]
    module
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [star_div₀]; ring
    rw [this]
    module
  · rw [smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; ring
    rw [this]
    module

end GlobalTheory.HoweD
