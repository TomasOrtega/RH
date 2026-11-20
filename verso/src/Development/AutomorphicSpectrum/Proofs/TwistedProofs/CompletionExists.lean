import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl

namespace GlobalTheory.CompanionTheory.InertDoubling

/- English proof (translation)
Establish `e : (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) = J * U * (J * J) * J * u * J + J * U * (J * J) * A * S + s * a * (J * J) * u * J + s * (a * J * A) * S - J * V * (J * J) * J * v * J + J * V * (J * J) * B * S + s * b * (J * J …` using `by noncomm_ring`. Rewrite using `[e, hJ, h3]`. Establish `e2 : J * U * 1 * J * u * J + J * U * 1 * A * S + s * a * 1 * u * J + s * (b * J * B) * S - J * V * 1 * J * v * J + J * V * 1 * B * S + s * b * 1 * v * J - s * (b * J * B) * S = J * (U * J * u - V * J * v) * J + J * (U * A + V * B) * S + s * (a * u + b * v) * J` using `by noncomm_ring`. Rewrite using `[e2, h1, h2]`. Use `noncomm_ring`.
-/
theorem ring_gram {R : Type} [Ring R] (J A B U V a b u v S s : R) (hJ : J * J = 1) (h1 : U * A + V * B = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * (U * J * u - V * J * v) * J + J * S + s * J := by
  have e : (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * U * (J * J) * J * u * J + J * U * (J * J) * A * S + s * a * (J * J) * u * J + s * (a * J * A) * S
      - J * V * (J * J) * J * v * J + J * V * (J * J) * B * S + s * b * (J * J) * v * J - s * (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : J * U * 1 * J * u * J + J * U * 1 * A * S + s * a * 1 * u * J + s * (b * J * B) * S
      - J * V * 1 * J * v * J + J * V * 1 * B * S + s * b * 1 * v * J - s * (b * J * B) * S =
      J * (U * J * u - V * J * v) * J + J * (U * A + V * B) * S + s * (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h1, h2]
  noncomm_ring

/- English proof (translation)
Establish `e : a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) = (a * (J * J) * u + b * (J * J) * v) * J + (a * J * A) * S - (b * J * B) * S` using `by noncomm_ring`. Rewrite using `[e, hJ, h3]`. Establish `e2 : (a * 1 * u + b * 1 * v) * J + (b * J * B) * S - (b * J * B) * S = (a * u + b * v) * J` using `by noncomm_ring`. Rewrite using `[e2, h2, one_mul]`.
-/
theorem ring_pair {R : Type} [Ring R] (J A B U V a b u v S : R) (hJ : J * J = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) = J := by
  have e : a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) =
      (a * (J * J) * u + b * (J * J) * v) * J + (a * J * A) * S - (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : (a * 1 * u + b * 1 * v) * J + (b * J * B) * S - (b * J * B) * S = (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h2, one_mul]

section Cong

variable {L : Type} [Field L] {σ : L →+* L} {m p : Type}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_add' (M N : Matrix m p L) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_sub' (M N : Matrix m p L) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_neg' (M : Matrix m p L) : cT σ (-M) = -cT σ M := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_smul' (c : L) (M : Matrix m p L) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, h]`.
-/
theorem cT_cT' (h : ∀ x, σ (σ x) = x) (M : Matrix m p L) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, h]

/- English proof (translation)
Apply the tactic sequence `ext (i | i) (j | j) <;> simp [cT]`.
-/
theorem cT_fromBlocks {m₁ m₂ p₁ p₂ : Type} (A : Matrix m₁ p₁ L) (B : Matrix m₁ p₂ L) (C : Matrix m₂ p₁ L)
    (D : Matrix m₂ p₂ L) : cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext (i | i) (j | j) <;> simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_submatrix {ι : Type} (e : m ≃ ι) (M : Matrix m m L) :
    cT σ (M.submatrix e.symm e.symm) = (cT σ M).submatrix e.symm e.symm := by
  ext i j; simp [cT]

end Cong

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Introduce and unpack `(i | i) (j | j)`. Conclude with `hA i j`. Conclude with `hB i j`. Conclude with `hC i j`. Conclude with `hD i j`.
-/
theorem isInt_fromBlocks {m₁ m₂ p₁ p₂ : Type} {A : Matrix m₁ p₁ L} {B : Matrix m₁ p₂ L} {C : Matrix m₂ p₁ L}
    {D : Matrix m₂ p₂ L} (hA : IsInt A) (hB : IsInt B) (hC : IsInt C) (hD : IsInt D) : IsInt (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

/- English proof (translation)
Introduce `i j` and use `neg_mem (h i j)`.
-/
theorem isInt_neg' {m p : Type} {A : Matrix m p L} (h : IsInt A) : IsInt (-A) := fun i j => neg_mem (h i j)

/- English proof (translation)
Introduce `i j` and use `sub_mem (h i j) (h' i j)`.
-/
theorem isInt_sub' {m p : Type} {A B : Matrix m p L} (h : IsInt A) (h' : IsInt B) : IsInt (A - B) :=
  fun i j => sub_mem (h i j) (h' i j)

/- English proof (translation)
Introduce `i j` and use `mul_mem hc (h i j)`.
-/
theorem isInt_smul' {m p : Type} {A : Matrix m p L} {c : L} (hc : c ∈ intL L) (h : IsInt A) : IsInt (c • A) :=
  fun i j => mul_mem hc (h i j)

/- English proof (translation)
Introduce `i j` and use `by have := h j i rw [GlobalTheory.UnitarySwap.mem_int] at this ⊢ simpa [cT, hσ] using this`.
-/
theorem isInt_cT' {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {m p : Type} {A : Matrix m p L} (h : IsInt A) :
    IsInt (cT σ A) := fun i j => by
  have := h j i
  rw [GlobalTheory.UnitarySwap.mem_int] at this ⊢
  simpa [cT, hσ] using this

/- English proof (translation)
Introduce `i j` and use `by unfold antiJ split_ifs · exact one_mem _ · exact zero_mem _`.
-/
theorem isInt_antiJ (n : ℕ) : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end Int

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, antiJ, transpose_apply, map_apply]`. Distinguish the cases in `h : i.val + j.val + 1 = n`. Establish `: j.val + i.val + 1 = n` using `by omega`. Simplify using `[h, this]`.

Establish `: ¬ (j.val + i.val + 1 = n)` using `by omega`. Simplify using `[h, this]`.
-/
theorem cT_antiJ {L : Type} [Field L] (σ : L →+* L) (n : ℕ) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, antiJ, transpose_apply, map_apply]
  by_cases h : i.val + j.val + 1 = n
  · have : j.val + i.val + 1 = n := by omega
    simp [h, this]
  · have : ¬ (j.val + i.val + 1 = n) := by omega
    simp [h, this]

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Take `⟨J, hJdef⟩ : ∃ J, J = antiJ L n` from `⟨_, rfl⟩`. Rewrite `hAB`, the goal using `[← hJdef]`. Establish `hJ : J * J = 1` using `hJdef ▸ GlobalTheory.UnitarySwap.antiJ_mul_self`. Establish `hJc : cT σ J = J` using `hJdef ▸ cT_antiJ σ n`. Establish `hJi : IsInt J` using `hJdef ▸ isInt_antiJ n`.

Establish `hτ' : σ τ ∈ intL L` using `by rw [GlobalTheory.UnitarySwap.mem_int, hσv]; exact hτ`. Take `⟨R, hR⟩ : ∃ R, R = U * J * cT σ U - V * J * cT σ V` from `⟨_, rfl⟩`. Establish `hRc : cT σ R = R`. Rewrite using `[hR]`. Simplify using `only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]`.

Establish `hRi : IsInt R` using `hR ▸ isInt_sub' ((hU.mul hJi).mul (isInt_cT' hσv hU)) ((hV.mul hJi).mul (isInt_cT' hσv hV))`. Take `⟨S, hS⟩ : ∃ S, S = -(τ • (R * J))` from `⟨_, rfl⟩`. Establish `hSc : cT σ S = -(σ τ • (J * R))` using `by rw [hS, cT_neg', cT_smul', cT_mul, hRc, hJc]`. Establish `hSi : IsInt S` using `hS ▸ isInt_neg' (isInt_smul' hτ (hRi.mul hJi))`. Take `⟨Ψ₁, hΨ₁⟩ : ∃ Ψ, Ψ = J * cT σ U * J + A * S` from `⟨_, rfl⟩`.

Take `⟨Ψ₂, hΨ₂⟩ : ∃ Ψ, Ψ = -(J * cT σ V * J) + B * S` from `⟨_, rfl⟩`. Establish `hΨ₁i : IsInt Ψ₁` using `hΨ₁ ▸ ((hJi.mul (isInt_cT' hσv hU)).mul hJi).add (hA.mul hSi)`. Establish `hΨ₂i : IsInt Ψ₂` using `hΨ₂ ▸ (isInt_neg' ((hJi.mul (isInt_cT' hσv hV)).mul hJi)).add (hB.mul hSi)`. Establish `h2 : cT σ A * cT σ U + cT σ B * cT σ V = 1`. Use `congrArg (cT σ) hUV` as an intermediate fact.

Rewrite `this` using `[cT_add', cT_mul, cT_mul, cT_one]`. Then use the resulting hypothesis. Establish `g12 : cT σ A * J * Ψ₁ - cT σ B * J * Ψ₂ = J`. Rewrite using `[hΨ₁, hΨ₂]`. Conclude with `ring_pair J A B U V _ _ _ _ S hJ h2 hAB`. Establish `g21 : cT σ Ψ₁ * J * A - cT σ Ψ₂ * J * B = J`.

Use `congrArg (cT σ) g12` as an intermediate fact. Simplify `this` using `only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]`. Establish `cΨ₁ : cT σ Ψ₁ = J * U * J + cT σ S * cT σ A`. Rewrite using `[hΨ₁]`. Simplify using `only [cT_add', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]`.

Establish `cΨ₂ : cT σ Ψ₂ = -(J * V * J) + cT σ S * cT σ B`. Rewrite using `[hΨ₂]`. Simplify using `only [cT_add', cT_neg', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]`. Establish `g22 : cT σ Ψ₁ * J * Ψ₁ - cT σ Ψ₂ * J * Ψ₂ = 0`. Rewrite using `[cΨ₁, cΨ₂, hΨ₁, hΨ₂, ring_gram J A B U V _ _ _ _ S _ hJ hUV h2 hAB, ← hR, hSc, hS]`.

Establish `e : J * R * J + J * -(τ • (R * J)) + -(σ τ • (J * R)) * J = (1 - τ - σ τ) • (J * R * J)`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, show 1 - τ - σ τ = 0 by linear_combination -hτ1, zero_smul]`. Establish `e1 : σ τ • (1 : Matrix (Fin n) (Fin n) L) + τ • 1 = 1` using `by rw [← add_smul, add_comm, hτ1, one_smul]`.

Establish `e2 : σ τ • J + τ • J = J` using `by rw [← add_smul, add_comm, hτ1, one_smul]`. Take `⟨Jd, hJd⟩ : ∃ Jd : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, Jd = fromBlocks J 0 0 (-J)` from `⟨_, rfl⟩`. Take `⟨H, hH⟩ : ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, H = fromBlocks 0 J J 0` from `⟨_, rfl⟩`. Take `⟨D, hD⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks 1 (τ • 1) 1 (-(σ τ • 1))` from `⟨_, rfl⟩`. Take `⟨Di, hDi⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks (σ τ • 1) (τ • 1) 1 (-1)` from `⟨_, rfl⟩`.

Take `⟨P, hP⟩ : ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, P = fromBlocks A Ψ₁ B Ψ₂` from `⟨_, rfl⟩`. Establish `hDDi : D * Di = 1`. Rewrite using `[hD, hDi, fromBlocks_multiply, ← fromBlocks_one]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg]`. Rewrite using `[fromBlocks_inj]`.

Use `⟨e1, by simp, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `e1`. Establish `hHH : H * H = 1`. Rewrite using `[hH, fromBlocks_multiply, ← fromBlocks_one]`.

Simplify using `[hJ]`. Establish `hDg : cT σ D * Jd * D = H`. Rewrite using `[hD, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [cT_neg', cT_smul', cT_one, hσσ, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_neg]`. Rewrite using `[fromBlocks_inj]`.

Use `⟨by simp, by rw [add_comm]; exact e2, e2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm, add_neg_cancel]`. Establish `hPg : cT σ P * Jd * P = H`. Rewrite using `[hP, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg]`.

Simplify using `only [← sub_eq_add_neg]`. Rewrite using `[fromBlocks_inj]`. Conclude with `⟨sub_eq_zero.2 hAB, g12, g21, g22⟩`. Establish `hDi' : IsInt Di` using `hDi ▸ isInt_fromBlocks (isInt_smul' hτ' isInt_one) (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' isInt_one)`. Establish `hDint : IsInt D` using `hD ▸ isInt_fromBlocks isInt_one (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' (isInt_smul' hτ' isInt_one))`.

Establish `hPi : IsInt P` using `hP ▸ isInt_fromBlocks hA hΨ₁i hB hΨ₂i`. Establish `hHi : IsInt H` using `hH ▸ isInt_fromBlocks isInt_zero hJi hJi isInt_zero`. Establish `hJdi : IsInt Jd` using `hJd ▸ isInt_fromBlocks hJi isInt_zero isInt_zero (isInt_neg' hJi)`. Use `⟨P * Di, D * H * cT σ P * Jd, hPi.mul hDi', ((hDint.mul hHi).mul (isInt_cT' hσv hPi)).mul hJdi, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hJd]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT σ Di * (cT σ D * Jd * D) * Di := by rw [hPg, hDg]`.

Use `_ = cT σ (D * Di) * Jd * (D * Di) := by rw [cT_mul]; simp only [Matrix.mul_assoc]`. Use `_ = Jd := by rw [hDDi, cT_one, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]`. Simplify using `only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]`. Rewrite using `[show σ τ • A + Ψ₁ + (τ • A + -Ψ₁) = (τ + σ τ) • A by rw [add_smul]; abel, hτ1, one_smul]`.

Rewrite using `[hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]`. Simplify using `only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]`. Rewrite using `[show σ τ • B + Ψ₂ + (τ • B + -Ψ₂) = (τ + σ τ) • B by rw [add_smul]; abel, hτ1, one_smul]`.
-/
theorem exists_block (hσσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {A B U V : Matrix (Fin n) (Fin n) L} (hA : IsInt A) (hB : IsInt B) (hU : IsInt U) (hV : IsInt V)
    (hAB : cT σ A * antiJ L n * A = cT σ B * antiJ L n * B) (hUV : U * A + V * B = 1) :
    ∃ k₀ k₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt k₀ ∧ IsInt k₁ ∧ k₁ * k₀ = 1 ∧
      cT σ k₀ * fromBlocks (antiJ L n) 0 0 (-antiJ L n) * k₀ = fromBlocks (antiJ L n) 0 0 (-antiJ L n) ∧
      k₀.toBlocks₁₁ + k₀.toBlocks₁₂ = A ∧ k₀.toBlocks₂₁ + k₀.toBlocks₂₂ = B := by
  obtain ⟨J, hJdef⟩ : ∃ J, J = antiJ L n := ⟨_, rfl⟩
  rw [← hJdef] at hAB ⊢
  have hJ : J * J = 1 := hJdef ▸ GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJc : cT σ J = J := hJdef ▸ cT_antiJ σ n
  have hJi : IsInt J := hJdef ▸ isInt_antiJ n
  have hτ' : σ τ ∈ intL L := by rw [GlobalTheory.UnitarySwap.mem_int, hσv]; exact hτ
  obtain ⟨R, hR⟩ : ∃ R, R = U * J * cT σ U - V * J * cT σ V := ⟨_, rfl⟩
  have hRc : cT σ R = R := by
    rw [hR]; simp only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have hRi : IsInt R := hR ▸ isInt_sub' ((hU.mul hJi).mul (isInt_cT' hσv hU)) ((hV.mul hJi).mul (isInt_cT' hσv hV))
  obtain ⟨S, hS⟩ : ∃ S, S = -(τ • (R * J)) := ⟨_, rfl⟩
  have hSc : cT σ S = -(σ τ • (J * R)) := by rw [hS, cT_neg', cT_smul', cT_mul, hRc, hJc]
  have hSi : IsInt S := hS ▸ isInt_neg' (isInt_smul' hτ (hRi.mul hJi))
  obtain ⟨Ψ₁, hΨ₁⟩ : ∃ Ψ, Ψ = J * cT σ U * J + A * S := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂⟩ : ∃ Ψ, Ψ = -(J * cT σ V * J) + B * S := ⟨_, rfl⟩
  have hΨ₁i : IsInt Ψ₁ := hΨ₁ ▸ ((hJi.mul (isInt_cT' hσv hU)).mul hJi).add (hA.mul hSi)
  have hΨ₂i : IsInt Ψ₂ := hΨ₂ ▸ (isInt_neg' ((hJi.mul (isInt_cT' hσv hV)).mul hJi)).add (hB.mul hSi)
  have h2 : cT σ A * cT σ U + cT σ B * cT σ V = 1 := by
    have := congrArg (cT σ) hUV
    rwa [cT_add', cT_mul, cT_mul, cT_one] at this
  have g12 : cT σ A * J * Ψ₁ - cT σ B * J * Ψ₂ = J := by
    rw [hΨ₁, hΨ₂]; exact ring_pair J A B U V _ _ _ _ S hJ h2 hAB
  have g21 : cT σ Ψ₁ * J * A - cT σ Ψ₂ * J * B = J := by
    have := congrArg (cT σ) g12
    simpa only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc] using this
  have cΨ₁ : cT σ Ψ₁ = J * U * J + cT σ S * cT σ A := by
    rw [hΨ₁]; simp only [cT_add', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have cΨ₂ : cT σ Ψ₂ = -(J * V * J) + cT σ S * cT σ B := by
    rw [hΨ₂]; simp only [cT_add', cT_neg', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have g22 : cT σ Ψ₁ * J * Ψ₁ - cT σ Ψ₂ * J * Ψ₂ = 0 := by
    rw [cΨ₁, cΨ₂, hΨ₁, hΨ₂, ring_gram J A B U V _ _ _ _ S _ hJ hUV h2 hAB, ← hR, hSc, hS]
    have e : J * R * J + J * -(τ • (R * J)) + -(σ τ • (J * R)) * J = (1 - τ - σ τ) • (J * R * J) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_smul, one_smul]
      abel
    rw [e, show 1 - τ - σ τ = 0 by linear_combination -hτ1, zero_smul]
  have e1 : σ τ • (1 : Matrix (Fin n) (Fin n) L) + τ • 1 = 1 := by rw [← add_smul, add_comm, hτ1, one_smul]
  have e2 : σ τ • J + τ • J = J := by rw [← add_smul, add_comm, hτ1, one_smul]
  obtain ⟨Jd, hJd⟩ : ∃ Jd : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, Jd = fromBlocks J 0 0 (-J) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, H = fromBlocks 0 J J 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks 1 (τ • 1) 1 (-(σ τ • 1)) := ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks (σ τ • 1) (τ • 1) 1 (-1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, P = fromBlocks A Ψ₁ B Ψ₂ := ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨e1, by simp, by simp, ?_⟩
    rw [add_comm]; exact e1
  have hHH : H * H = 1 := by
    rw [hH, fromBlocks_multiply, ← fromBlocks_one]
    simp [hJ]
  have hDg : cT σ D * Jd * D = H := by
    rw [hD, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [cT_neg', cT_smul', cT_one, hσσ, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨by simp, by rw [add_comm]; exact e2, e2, ?_⟩
    rw [smul_comm, add_neg_cancel]
  have hPg : cT σ P * Jd * P = H := by
    rw [hP, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg]
    simp only [← sub_eq_add_neg]
    rw [fromBlocks_inj]
    exact ⟨sub_eq_zero.2 hAB, g12, g21, g22⟩
  have hDi' : IsInt Di := hDi ▸ isInt_fromBlocks (isInt_smul' hτ' isInt_one) (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' isInt_one)
  have hDint : IsInt D := hD ▸ isInt_fromBlocks isInt_one (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' (isInt_smul' hτ' isInt_one))
  have hPi : IsInt P := hP ▸ isInt_fromBlocks hA hΨ₁i hB hΨ₂i
  have hHi : IsInt H := hH ▸ isInt_fromBlocks isInt_zero hJi hJi isInt_zero
  have hJdi : IsInt Jd := hJd ▸ isInt_fromBlocks hJi isInt_zero isInt_zero (isInt_neg' hJi)
  refine ⟨P * Di, D * H * cT σ P * Jd, hPi.mul hDi', ((hDint.mul hHi).mul (isInt_cT' hσv hPi)).mul hJdi, ?_, ?_, ?_, ?_⟩
  · calc D * H * cT σ P * Jd * (P * Di) = D * H * (cT σ P * Jd * P) * Di := by simp only [Matrix.mul_assoc]
      _ = D * (H * H) * Di := by rw [hPg]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, hDDi]
  · rw [← hJd]
    calc cT σ (P * Di) * Jd * (P * Di) = cT σ Di * (cT σ P * Jd * P) * Di := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ Di * (cT σ D * Jd * D) * Di := by rw [hPg, hDg]
      _ = cT σ (D * Di) * Jd * (D * Di) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Jd := by rw [hDDi, cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • A + Ψ₁ + (τ • A + -Ψ₁) = (τ + σ τ) • A by rw [add_smul]; abel, hτ1, one_smul]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • B + Ψ₂ + (τ • B + -Ψ₂) = (τ + σ τ) • B by rw [add_smul]; abel, hτ1, one_smul]

/- English proof (translation)
Introduce `L _ _ ϖ σ q n hU g U V C hF`. Take `⟨τ, hτ, hτ1⟩` from `exists_trace_one hU`. Establish `hσσ` using `hU.1`. Establish `hσv` using `hU.2.1`. Take `⟨hUi, hVi, hC, hgC, hone⟩` from `hF`.

Establish `hg : cT σ (mat g) * antiJ L n * mat g = antiJ L n` using `g.2`. Establish `hAB : cT σ C * antiJ L n * C = cT σ (mat g * C) * antiJ L n * (mat g * C)`. Rewrite using `[cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hUV : U * C + V * (mat g * C) = 1`.

Rewrite using `[← hone]`. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc]`. Take `⟨k₀, k₁, h0, h1, h10, hu, hx, hy⟩` from `exists_block hσσ hσv hτ hτ1 hC hgC hUi hVi hAB hUV`. Establish `hmul : k₀.submatrix finSumFinEquiv.symm finSumFinEquiv.symm * k₁.submatrix (finSumFinEquiv (m` using `n) (n := n)).symm finSumFinEquiv.symm = 1 := by`. Rewrite using `[submatrix_mul_equiv, mul_eq_one_comm.1 h10, submatrix_one_equiv]`.

Take `⟨k, hki, hke⟩` from `P.cartan_exists_glint (intL L) _ _ hmul (fun i j => h0 _ _) (fun i j => h1 _ _)`. Use `⟨k, ?_, hki, fun x => ?_⟩` and prove the remaining obligations. Use `show cT σ (k : Matrix _ _ L) * dblGram finSumFinEquiv (antiJ L n) * (k : Matrix _ _ L) = _`. Rewrite using `[hke, cT_submatrix, dblGram, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, hu]`. Rewrite using `[hke, mulVec_pairVec]`.

Establish `e : (k₀.submatrix (finSumFinEquiv (m` using `n) (n := n)).symm finSumFinEquiv.symm).submatrix finSumFinEquiv finSumFinEquiv = k₀ := by ext i j; simp`. Rewrite using `[e, ← add_mulVec, ← add_mulVec, hx, hy]`.
-/
theorem completion : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hF
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  have hσσ := hU.1
  have hσv := hU.2.1
  obtain ⟨hUi, hVi, hC, hgC, hone⟩ := hF
  have hg : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have hAB : cT σ C * antiJ L n * C = cT σ (mat g * C) * antiJ L n * (mat g * C) := by
    rw [cT_mul]
    calc cT σ C * antiJ L n * C = cT σ C * (cT σ (mat g) * antiJ L n * mat g) * C := by rw [hg]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hUV : U * C + V * (mat g * C) = 1 := by
    rw [← hone]; simp only [Matrix.add_mul, Matrix.mul_assoc]
  obtain ⟨k₀, k₁, h0, h1, h10, hu, hx, hy⟩ := exists_block hσσ hσv hτ hτ1 hC hgC hUi hVi hAB hUV
  have hmul : k₀.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      k₁.submatrix (finSumFinEquiv (m := n) (n := n)).symm finSumFinEquiv.symm = 1 := by
    rw [submatrix_mul_equiv, mul_eq_one_comm.1 h10, submatrix_one_equiv]
  obtain ⟨k, hki, hke⟩ := P.cartan_exists_glint (intL L) _ _ hmul (fun i j => h0 _ _) (fun i j => h1 _ _)
  refine ⟨k, ?_, hki, fun x => ?_⟩
  · show cT σ (k : Matrix _ _ L) * dblGram finSumFinEquiv (antiJ L n) * (k : Matrix _ _ L) = _
    rw [hke, cT_submatrix, dblGram, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, hu]
  · rw [hke, mulVec_pairVec]
    have e : (k₀.submatrix (finSumFinEquiv (m := n) (n := n)).symm finSumFinEquiv.symm).submatrix finSumFinEquiv
        finSumFinEquiv = k₀ := by ext i j; simp
    rw [e, ← add_mulVec, ← add_mulVec, hx, hy]

end Main

end GlobalTheory.CompanionTheory.InertDoubling
