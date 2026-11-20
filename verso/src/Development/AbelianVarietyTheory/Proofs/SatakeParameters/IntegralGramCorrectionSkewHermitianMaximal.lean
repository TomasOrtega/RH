import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem ringHomConjTranspose_mul_rev (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use `show Valued.v (σ (A j i)) ≤ 1`. Rewrite using `[hv]`. Conclude with `hA j i`.
-/
theorem sigmaConjTranspose_integral_gramSeparation (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  show Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact hA j i

/- English proof (translation)
Use `show Valued.v (x * (y ^ k)⁻¹) ≤ 1`. Establish `h0 : Valued.v ϖ ^ k ≠ 0` using `pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hϖ0)`. Establish `h1 : Valued.v x ≤ Valued.v ϖ ^ k` using `hx.trans (pow_le_pow_right_of_le_one' hϖ hkm)`. Rewrite using `[map_mul, map_inv₀, map_pow, hy]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_div_pow_le_one {ϖ x y : L} {k m : ℕ} (hϖ : Valued.v ϖ ≤ 1) (hy : Valued.v y = Valued.v ϖ) (hϖ0 : ϖ ≠ 0)
    (hx : Valued.v x ≤ Valued.v ϖ ^ m) (hkm : k ≤ m) : x * (y ^ k)⁻¹ ∈ Formalism.UG.intL L := by
  show Valued.v (x * (y ^ k)⁻¹) ≤ 1
  have h0 : Valued.v ϖ ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hϖ0)
  have h1 : Valued.v x ≤ Valued.v ϖ ^ k := hx.trans (pow_le_pow_right_of_le_one' hϖ hkm)
  rw [map_mul, map_inv₀, map_pow, hy]
  calc Valued.v x * (Valued.v ϖ ^ k)⁻¹ ≤ Valued.v ϖ ^ k * (Valued.v ϖ ^ k)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ h0

end GlobalTheory.Hk3.GramSep

namespace GlobalTheory.Hk3.GramSep

/- English proof (translation)
Introduce `L _ _ ϖ σ hvϖ hv n r JS a M e Γ hJS hSD he hM haM hΓ`. Establish `hΓv : ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j)` using `hΓ.2`. Establish `hϖlt : Valued.v ϖ < 1`. Rewrite using `[hvϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]`. Evaluate the decidable proposition.

Establish `hϖ1 : Valued.v ϖ ≤ 1` using `hϖlt.le`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hvϖ` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hvϖ`.

Establish `hσϖ0 : σ ϖ ≠ 0` using `(map_ne_zero σ).mpr hϖ0`. Use `set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai`. Use `set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA`. Use `set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJ`. Use `set D : Matrix (Fin r) (Fin r) L := diagonal fun k => ϖ ^ e k with hD`.

Use `set Di : Matrix (Fin r) (Fin r) L := diagonal fun k => (ϖ ^ e k)⁻¹ with hDi`. Use `set Ds : Matrix (Fin r) (Fin r) L := diagonal fun k => σ ϖ ^ e k with hDs`. Use `set Dsi : Matrix (Fin r) (Fin r) L := diagonal fun k => (σ ϖ ^ e k)⁻¹ with hDsi`. Establish `hDDi : D * Di = 1`. Rewrite using `[hD, hDi, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ hϖ0)`. Establish `hDsiDs : Dsi * Ds = 1`. Rewrite using `[hDs, hDsi, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `inv_mul_cancel₀ (pow_ne_zero _ hσϖ0)`. Establish `hcTD : Formalism.UG.cT σ D = Ds`. Rewrite using `[hD, hDs]`.

Unfold `Formalism.UG.cT`. Rewrite using `[diagonal_map (map_zero σ), diagonal_transpose]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Establish `haia : ai * A = 1` using `by rw [hai, hA]; exact a.inv_mul`. Establish `hcTa : Formalism.UG.cT σ ai * Formalism.UG.cT σ A = 1`. Establish `haai : A * ai = 1` using `by rw [hai, hA]; exact a.mul_inv`. Rewrite using `[← ringHomConjTranspose_mul_rev, haai]`. Unfold `Formalism.UG.cT`.

Rewrite using `[Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]`. Use `set P : Matrix (Fin n) (Fin r) L := ai * M * D with hP`. Establish `hPi : ∀ i k, P i k ∈ Formalism.UG.intL L`. Introduce `i k`. Rewrite using `[hP, hD, mul_diagonal]`.

Conclude with `haM i k`. Use `set G1 : Matrix (Fin r) (Fin r) L := Di * Γ with hG1`. Establish `hG1i : ∀ k j, G1 k j ∈ Formalism.UG.intL L`. Introduce `k j`. Rewrite using `[hG1, hDi, diagonal_mul, mul_comm]`.

Conclude with `val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) (le_max_left _ _)`. Use `set G2 : Matrix (Fin r) (Fin r) L := Γ * Dsi with hG2`. Establish `hG2i : ∀ k j, G2 k j ∈ Formalism.UG.intL L`. Introduce `k j`. Rewrite using `[hG2, hDsi, mul_diagonal]`.

Conclude with `val_div_pow_le_one hϖ1 (hv ϖ) hϖ0 (hΓv k j) (le_max_right _ _)`. Establish `hcTM` using `sigmaConjTranspose_integral_gramSeparation σ hv hM`. Establish `hSDa : ∀ i j, (Formalism.UG.cT σ A * J * A) i j ∈ Formalism.UG.intL L` using `hSD.1`. Use `⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `e1 : ai * (M * Γ * Formalism.UG.cT σ M * J) = P * G1 * (Formalism.UG.cT σ M * J)`.

Rewrite using `[hP, hG1]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]`. Rewrite using `[e1]`. Conclude with `matMul_int (matMul_int hPi hG1i) (matMul_int hcTM hJS) i j`.

Establish `e2 : M * Γ * Formalism.UG.cT σ M * J * A = M * G2 * (Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A))`. Rewrite using `[hP, hG2, ringHomConjTranspose_mul_rev, ringHomConjTranspose_mul_rev, hcTD]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Dsi Ds, hDsiDs, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.cT σ ai) (Formalism.UG.cT σ A), hcTa, Matrix.one_mul]`. Rewrite using `[e2]`.

Conclude with `matMul_int (matMul_int hM hG2i) (matMul_int (sigmaConjTranspose_integral_gramSeparation σ hv hPi) hSDa) i j`. Use `set G3 : Matrix (Fin r) (Fin r) L := Matrix.of fun k j => Γ k j * (ϖ ^ 1)⁻¹ with hG3`. Establish `hG3i : ∀ k j, G3 k j ∈ Formalism.UG.intL L`. Introduce `k j`. Conclude with `val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) ((he k).trans (le_max_left _ _))`.

Establish `hΓ3 : Γ = ϖ • G3`. Use extensionality with `k j`. Rewrite using `[hG3]`. Simplify using `only [Matrix.smul_apply, of_apply, smul_eq_mul, pow_one]`. Clear the denominators using the available nonvanishing facts.

Establish `e3 : M * Γ * Formalism.UG.cT σ M * J = ϖ • (M * G3 * Formalism.UG.cT σ M * J)`. Rewrite using `[hΓ3, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]`. Rewrite using `[e3, Matrix.smul_apply, smul_eq_mul, map_mul]`. Establish `hint : Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ 1` using `matMul_int (matMul_int (matMul_int hM hG3i) hcTM) hJS i j`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eint : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  intro L _ _ ϖ σ hvϖ hv n r JS a M e Γ hJS hSD he hM haM hΓ
  classical
  have hΓv : ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j) := hΓ.2
  have hϖlt : Valued.v ϖ < 1 := by
    rw [hvϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]; decide
  have hϖ1 : Valued.v ϖ ≤ 1 := hϖlt.le
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hσϖ0 : σ ϖ ≠ 0 := (map_ne_zero σ).mpr hϖ0
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJ
  set D : Matrix (Fin r) (Fin r) L := diagonal fun k => ϖ ^ e k with hD
  set Di : Matrix (Fin r) (Fin r) L := diagonal fun k => (ϖ ^ e k)⁻¹ with hDi
  set Ds : Matrix (Fin r) (Fin r) L := diagonal fun k => σ ϖ ^ e k with hDs
  set Dsi : Matrix (Fin r) (Fin r) L := diagonal fun k => (σ ϖ ^ e k)⁻¹ with hDsi
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
  have hDsiDs : Dsi * Ds = 1 := by
    rw [hDs, hDsi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact inv_mul_cancel₀ (pow_ne_zero _ hσϖ0)
  have hcTD : Formalism.UG.cT σ D = Ds := by
    rw [hD, hDs]; unfold Formalism.UG.cT
    rw [diagonal_map (map_zero σ), diagonal_transpose]
    congr 1; funext k; simp
  have haia : ai * A = 1 := by rw [hai, hA]; exact a.inv_mul
  have hcTa : Formalism.UG.cT σ ai * Formalism.UG.cT σ A = 1 := by
    have haai : A * ai = 1 := by rw [hai, hA]; exact a.mul_inv
    rw [← ringHomConjTranspose_mul_rev, haai]
    unfold Formalism.UG.cT; rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

  set P : Matrix (Fin n) (Fin r) L := ai * M * D with hP
  have hPi : ∀ i k, P i k ∈ Formalism.UG.intL L := by
    intro i k; rw [hP, hD, mul_diagonal]; exact haM i k
  set G1 : Matrix (Fin r) (Fin r) L := Di * Γ with hG1
  have hG1i : ∀ k j, G1 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG1, hDi, diagonal_mul, mul_comm]
    exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) (le_max_left _ _)
  set G2 : Matrix (Fin r) (Fin r) L := Γ * Dsi with hG2
  have hG2i : ∀ k j, G2 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG2, hDsi, mul_diagonal]
    exact val_div_pow_le_one hϖ1 (hv ϖ) hϖ0 (hΓv k j) (le_max_right _ _)
  have hcTM := sigmaConjTranspose_integral_gramSeparation σ hv hM
  have hSDa : ∀ i j, (Formalism.UG.cT σ A * J * A) i j ∈ Formalism.UG.intL L := hSD.1
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have e1 : ai * (M * Γ * Formalism.UG.cT σ M * J) = P * G1 * (Formalism.UG.cT σ M * J) := by
      rw [hP, hG1]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]
    rw [e1]
    exact matMul_int (matMul_int hPi hG1i) (matMul_int hcTM hJS) i j
  · have e2 : M * Γ * Formalism.UG.cT σ M * J * A = M * G2 * (Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A)) := by
      rw [hP, hG2, ringHomConjTranspose_mul_rev, ringHomConjTranspose_mul_rev, hcTD]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Dsi Ds, hDsiDs, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.cT σ ai) (Formalism.UG.cT σ A), hcTa,
        Matrix.one_mul]
    rw [e2]
    exact matMul_int (matMul_int hM hG2i) (matMul_int (sigmaConjTranspose_integral_gramSeparation σ hv hPi) hSDa) i j
  · set G3 : Matrix (Fin r) (Fin r) L := Matrix.of fun k j => Γ k j * (ϖ ^ 1)⁻¹ with hG3
    have hG3i : ∀ k j, G3 k j ∈ Formalism.UG.intL L := by
      intro k j
      exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) ((he k).trans (le_max_left _ _))
    have hΓ3 : Γ = ϖ • G3 := by
      ext k j; rw [hG3]; simp only [Matrix.smul_apply, of_apply, smul_eq_mul, pow_one]
      field_simp
    have e3 : M * Γ * Formalism.UG.cT σ M * J = ϖ • (M * G3 * Formalism.UG.cT σ M * J) := by
      rw [hΓ3, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    rw [e3, Matrix.smul_apply, smul_eq_mul, map_mul]
    have hint : Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ 1 :=
      matMul_int (matMul_int (matMul_int hM hG3i) hcTM) hJS i j
    calc Valued.v ϖ * Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hϖlt

end GlobalTheory.Hk3.GramSep
