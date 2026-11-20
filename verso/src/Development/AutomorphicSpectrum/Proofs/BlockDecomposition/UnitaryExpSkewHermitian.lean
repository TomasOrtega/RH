import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JBConjTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiag

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.UnitaryExp

/- English proof (translation)
Use `set A : Matrix (Fin n) (Fin n) ℂ := K + Kᴴ with hA`. Use `set B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (K - Kᴴ) with hB`. Establish `hAh : Aᴴ = A`. Simplify using `[hA, Matrix.conjTranspose_add, add_comm]`. Establish `hBh : Bᴴ = B`.

Simplify using `[hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hAB : A * B = B * A`. Establish `e : (K + Kᴴ) * (K - Kᴴ) = (K - Kᴴ) * (K + Kᴴ)`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, h1, h2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hA, hB, Matrix.mul_smul, Matrix.smul_mul, e]`. Take `⟨V, hV, hD⟩` from `GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ)) (by`. Introduce and unpack `X (rfl | rfl)`. Conclude with `hAh`.

Conclude with `hBh)`. Use the proof step `(by`. Introduce and unpack `X (rfl | rfl) Y (rfl | rfl)`. Both sides reduce to the same expression. Conclude with `hAB`.

Conclude with `hAB.symm`. Use the proof step `rfl)`. Establish `hV1 : Vᴴ * V = 1` using `Matrix.mem_unitaryGroup_iff'.1 hV`. Establish `hV2 : V * Vᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hV`. Establish `hKAB : K = (1 / 2 : ℂ) • (A - Complex.I • B)`.

Simplify using `only [hA, hB, smul_smul, Complex.I_mul_I]`. Use `module`. Establish `hDd : (Vᴴ * K * V).IsDiag`. Establish `e : Vᴴ * K * V = (1 / 2 : ℂ) • (Vᴴ * A * V - Complex.I • (Vᴴ * B * V))` using `by conv_lhs => rw [hKAB]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]`.

Rewrite using `[e]`. Conclude with `((hD A (by simp)).sub ((hD B (by simp)).smul _)).smul _`. Use `⟨V, Matrix.diag (Vᴴ * K * V), hV1, hV2, hDd.diagonal_diag.symm, fun a => ?_⟩` and prove the remaining obligations. Use `set D := Vᴴ * K * V with hDdef`. Establish `hDD : Dᴴ * D = 1`.

Establish `e : Dᴴ = Vᴴ * Kᴴ * V`. Simplify using `[hDdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e, hDdef]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Vᴴ * (Kᴴ * K) * V := by`. Rewrite using `[hV2]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1, Matrix.mul_one, hV1]`. Establish `hent : star (D a a) * D a a = 1`.

Establish `h` using `congrFun (congrFun hDD a) a`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Simplify `h` using `[Matrix.conjTranspose_apply]`. Introduce `b _ hb`. Establish `: D b a = 0` using `hDd hb`.

Simplify using `[this]`. Simplify using the standard rewrite rules. Establish `hn : ‖D a a‖ ^ 2 = 1`. Establish `h3 : ((‖D a a‖ ^ 2 : ℝ) : ℂ) = 1`. Use `Complex.conj_mul' (D a a)` as an intermediate fact.

Use `push_cast`. Rewrite using `[← this]`. Simplify using `using hent`. Conclude with `h3` after adjusting the coercions. Establish `h0 : 0 ≤ ‖D a a‖` using `norm_nonneg _`.

Use `show ‖D a a‖ = 1`. Use polynomial arithmetic with `[sq_nonneg (‖D a a‖ - 1), sq_nonneg (‖D a a‖ + 1)]`.
-/
theorem exists_unitary_diag {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (h1 : Kᴴ * K = 1) (h2 : K * Kᴴ = 1) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Vᴴ * K * V = Matrix.diagonal z ∧ ∀ a, ‖z a‖ = 1 := by
  classical
  set A : Matrix (Fin n) (Fin n) ℂ := K + Kᴴ with hA
  set B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (K - Kᴴ) with hB
  have hAh : Aᴴ = A := by
    simp [hA, Matrix.conjTranspose_add, add_comm]
  have hBh : Bᴴ = B := by
    simp [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub]
    abel
  have hAB : A * B = B * A := by
    have e : (K + Kᴴ) * (K - Kᴴ) = (K - Kᴴ) * (K + Kᴴ) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
      abel
    rw [hA, hB, Matrix.mul_smul, Matrix.smul_mul, e]
  obtain ⟨V, hV, hD⟩ := GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ))
    (by
      rintro X (rfl | rfl)
      · exact hAh
      · exact hBh)
    (by
      rintro X (rfl | rfl) Y (rfl | rfl)
      · rfl
      · exact hAB
      · exact hAB.symm
      · rfl)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hKAB : K = (1 / 2 : ℂ) • (A - Complex.I • B) := by
    simp only [hA, hB, smul_smul, Complex.I_mul_I]
    module
  have hDd : (Vᴴ * K * V).IsDiag := by
    have e : Vᴴ * K * V = (1 / 2 : ℂ) • (Vᴴ * A * V - Complex.I • (Vᴴ * B * V)) := by
      conv_lhs => rw [hKAB]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact ((hD A (by simp)).sub ((hD B (by simp)).smul _)).smul _
  refine ⟨V, Matrix.diag (Vᴴ * K * V), hV1, hV2, hDd.diagonal_diag.symm, fun a => ?_⟩
  set D := Vᴴ * K * V with hDdef
  have hDD : Dᴴ * D = 1 := by
    have e : Dᴴ = Vᴴ * Kᴴ * V := by
      simp [hDdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hDdef]
    calc Vᴴ * Kᴴ * V * (Vᴴ * K * V) = Vᴴ * Kᴴ * (V * Vᴴ) * K * V := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (Kᴴ * K) * V := by
          rw [hV2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV1]
  have hent : star (D a a) * D a a = 1 := by
    have h := congrFun (congrFun hDD a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · simpa [Matrix.conjTranspose_apply] using h
    · intro b _ hb
      have : D b a = 0 := hDd hb
      simp [this]
    · simp
  have hn : ‖D a a‖ ^ 2 = 1 := by
    have h3 : ((‖D a a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := Complex.conj_mul' (D a a)
      push_cast
      rw [← this]
      simpa using hent
    exact_mod_cast h3
  have h0 : 0 ≤ ‖D a a‖ := norm_nonneg _
  show ‖D a a‖ = 1
  nlinarith [sq_nonneg (‖D a a‖ - 1), sq_nonneg (‖D a a‖ + 1)]

/- English proof (translation)
Establish `h1 : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (k : Matrix (Fin n) (Fin n) ℂ) = 1` using `Matrix.mem_unitaryGroup_iff'.1 k.2`. Establish `h2 : (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 k.2`. Take `⟨V, z, hV1, hV2, hD, hz⟩` from `exists_unitary_diag _ h1 h2`. Use `set w : Fin n → ℂ := fun a => (Complex.arg (z a) : ℂ) * Complex.I with hw`. Establish `hexp : ∀ a, NormedSpace.exp (w a) = z a`.

Introduce `a`. Use `Complex.norm_mul_exp_arg_mul_I (z a)` as an intermediate fact. Rewrite `this` using `[hz a]`. Simplify `this` using `[hw, Complex.exp_eq_exp_ℂ]`. Establish `hk : (k : Matrix (Fin n) (Fin n) ℂ) = V * Matrix.diagonal z * Vᴴ`.

Rewrite using `[← hD]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hV2]`. Simplify using the standard rewrite rules. Use `_ = V * (Vᴴ * (k : Matrix (Fin n) (Fin n) ℂ) * V) * Vᴴ := by`.

Simplify using `only [Matrix.mul_assoc]`. Use `⟨V * Matrix.diagonal w * Vᴴ, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : star w = -w`. Use function extensionality and compare the values at `a`. Simplify using `[hw]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]`. Establish `hn : Matrix.diagonal (-w) = -Matrix.diagonal w` using `(Matrix.diagonal_neg w).symm`. Rewrite using `[hn, Matrix.neg_mul, Matrix.mul_neg]`. Use `Units.ext ?_` and prove the remaining obligations. Set `Vu : (Matrix (Fin n) (Fin n) ℂ)ˣ` to `⟨V, Vᴴ, hV2, hV1⟩`.

Establish `e` using `Matrix.exp_units_conj Vu (Matrix.diagonal w)`. Establish `e2 : NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal z`. Rewrite using `[Matrix.exp_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Rewrite using `[Pi.exp_def]`. Conclude with `hexp a`. Rewrite `e` using `[e2]`. Establish `e3 : ((expG (V * Matrix.diagonal w * Vᴴ) 1 : G n) : Mat n) = NormedSpace.exp (V * Matrix.diagonal w * Vᴴ)`. Simplify using the standard rewrite rules.

Rewrite using `[e3]`. Conclude with `hk.trans e.symm`.
-/
theorem exists_skew_exp_eq (n : ℕ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ X : Mat n, Xᴴ = -X ∧ uG k = expG X 1 := by
  classical
  have h1 : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  obtain ⟨V, z, hV1, hV2, hD, hz⟩ := exists_unitary_diag _ h1 h2
  set w : Fin n → ℂ := fun a => (Complex.arg (z a) : ℂ) * Complex.I with hw
  have hexp : ∀ a, NormedSpace.exp (w a) = z a := by
    intro a
    have := Complex.norm_mul_exp_arg_mul_I (z a)
    rw [hz a] at this
    simpa [hw, Complex.exp_eq_exp_ℂ] using this
  have hk : (k : Matrix (Fin n) (Fin n) ℂ) = V * Matrix.diagonal z * Vᴴ := by
    rw [← hD]
    calc (k : Matrix (Fin n) (Fin n) ℂ)
        = (V * Vᴴ) * (k : Matrix (Fin n) (Fin n) ℂ) * (V * Vᴴ) := by
          rw [hV2]; simp
      _ = V * (Vᴴ * (k : Matrix (Fin n) (Fin n) ℂ) * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
  refine ⟨V * Matrix.diagonal w * Vᴴ, ?_, ?_⟩
  · have hs : star w = -w := by
      funext a
      simp [hw]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
    have hn : Matrix.diagonal (-w) = -Matrix.diagonal w := (Matrix.diagonal_neg w).symm
    rw [hn, Matrix.neg_mul, Matrix.mul_neg]
  · refine Units.ext ?_
    let Vu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, hV2, hV1⟩
    have e := Matrix.exp_units_conj Vu (Matrix.diagonal w)
    have e2 : NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal z := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext a
      rw [Pi.exp_def]
      exact hexp a
    rw [e2] at e
    have e3 : ((expG (V * Matrix.diagonal w * Vᴴ) 1 : G n) : Mat n) =
        NormedSpace.exp (V * Matrix.diagonal w * Vᴴ) := by
      simp
    rw [e3]
    exact hk.trans e.symm

end GlobalTheory.CompanionTheory.UnitaryExp
