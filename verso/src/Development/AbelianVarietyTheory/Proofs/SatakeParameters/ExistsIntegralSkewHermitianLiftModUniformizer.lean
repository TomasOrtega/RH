import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SkewLift

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hσ]`.
-/
theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]`.
-/
theorem cT_mul_rect (σ : L →+* L) {a b c : Type} [Fintype b] (M : Matrix a b L) (N : Matrix b c L) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]

/- English proof (translation)
Introduce `i j` and use `sub_mem (hM i j) (hN i j)`.
-/
theorem isIntM_sub' [Valued L (WithZero (Multiplicative ℤ))] {a b : Type} {M N : Matrix a b L} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong`. Establish `h2 : Valued.v (2 : L) = 1` using `GlobalTheory.Hk3.Inh.v_two hU hq`. Establish `hσσ` using `hU.1`. Establish `hσv` using `hU.2.1`. Establish `hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L` using `by show Valued.v ((2 : L)⁻¹) ≤ 1`.

Rewrite using `[map_inv₀, h2, inv_one]`. Establish `hσhalf : σ ((2 : L)⁻¹) = 2⁻¹` using `by rw [map_inv₀, map_ofNat]`. Use `set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef`. Establish `hJI : IsIntM J` using `GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT`. Establish `hcJ : Formalism.UG.cT σ J = J` using `cT_herm σ herm`.

Set `B : Matrix (Fin n') ι L` to `fun r i => (J *ᵥ w i) r`. Set `Z : Matrix (Fin n') ι L` to `fun r j => z j r`. Set `A : Matrix ι (Fin n') L` to `fun i r => a i r`. Set `P : Matrix ι ι L` to `Formalism.UG.cT σ B * Z`. Set `C : Matrix (Fin n') (Fin n') L` to `B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)`.

Establish `hAZ : A * Z = 1`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `hdual i j`. Establish `hAI : IsIntM A` using `fun i r => ha i r`.

Establish `hZI : IsIntM Z` using `fun r j => hz j r`. Establish `hBI : IsIntM B` using `fun r i => by show (J *ᵥ w i) r ∈ Formalism.UG.intL L`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `sum_mem fun s _ => mul_mem (hJI r s) (hw i s)`. Establish `hPI : IsIntM P` using `isIntM_mul (isIntM_cT hσv hBI) hZI`.

Establish `hcC : Formalism.UG.cT σ C = -C`. Simplify using `only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]`. Use `⟨C, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r s`.

Use `congrFun (congrFun hcC s) r` as an intermediate fact. Simplify `this` using `[Formalism.UG.cT]`. Conclude with `isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI)))) (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))`. Establish `hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i)`. Introduce `k i`.

Use `show ∑ r, σ (B r k) * z i r = _`. Simplify using `only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring` and prove the remaining obligations. Establish `hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x`.

Introduce `x y`. Simplify using `only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring` and prove the remaining obligations. Establish `hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i)`.

Introduce `k i`. Establish `e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i)` using `by show P k i + σ (P i k) = _`. Rewrite using `[hP, hP, hσh, add_comm]`. Rewrite using `[e]`. Conclude with `hcong k i`.

Establish `hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P))`. Establish `e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z))`. Simplify using `only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]`. Rewrite using `[e1, hAZ, Matrix.mul_one, Matrix.mul_one]`. Establish `e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P)`.

Rewrite using `[← add_smul]`. Establish `: (2⁻¹ + 2⁻¹ : L) = 1`. Establish `h2ne : (2 : L) ≠ 0` using `fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions.

Rewrite using `[this, one_smul]`. Rewrite using `[e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]`. Normalize the expressions using the abelian group laws. Introduce `i r`. Establish `e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i` using `rfl`.

Rewrite using `[e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]`. Use `dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))`.
-/
theorem skew_lift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v ((2 : L)⁻¹) ≤ 1
    rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJI : IsIntM J := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hcJ : Formalism.UG.cT σ J = J := cT_herm σ herm
  let B : Matrix (Fin n') ι L := fun r i => (J *ᵥ w i) r
  let Z : Matrix (Fin n') ι L := fun r j => z j r
  let A : Matrix ι (Fin n') L := fun i r => a i r
  let P : Matrix ι ι L := Formalism.UG.cT σ B * Z
  let C : Matrix (Fin n') (Fin n') L :=
    B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)
  have hAZ : A * Z = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact hdual i j
  have hAI : IsIntM A := fun i r => ha i r
  have hZI : IsIntM Z := fun r j => hz j r
  have hBI : IsIntM B := fun r i => by
    show (J *ᵥ w i) r ∈ Formalism.UG.intL L
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun s _ => mul_mem (hJI r s) (hw i s)
  have hPI : IsIntM P := isIntM_mul (isIntM_cT hσv hBI) hZI
  have hcC : Formalism.UG.cT σ C = -C := by
    simp only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro r s
    have := congrFun (congrFun hcC s) r
    simpa [Formalism.UG.cT] using this
  · exact isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI))))
      (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))
  · have hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i) := by
      intro k i
      show ∑ r, σ (B r k) * z i r = _
      simp only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x := by
      intro x y
      simp only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i) := by
      intro k i
      have e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i) := by
        show P k i + σ (P i k) = _
        rw [hP, hP, hσh, add_comm]
      rw [e]; exact hcong k i
    have hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P)) := by
      have e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z)) := by
        simp only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e1, hAZ, Matrix.mul_one, Matrix.mul_one]
      have e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P) := by
        rw [← add_smul]
        have : (2⁻¹ + 2⁻¹ : L) = 1 := by
          have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
          field_simp; norm_num
        rw [this, one_smul]
      rw [e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
      abel
    intro i r
    have e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i := rfl
    rw [e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)
    rw [← mul_assoc]
    exact dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))

end GlobalTheory.Hk3.SkewLift
