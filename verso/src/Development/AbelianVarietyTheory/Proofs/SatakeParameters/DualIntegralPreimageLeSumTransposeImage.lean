import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationFieldStatement
open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

/- English proof (translation)
Introduce `i` and use `by simp only [Matrix.mulVec, dotProduct] exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)`.
-/
theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

/- English proof (translation)
Distinguish the cases in `he : e ∈ Formalism.UG.intL L`. Use `⟨z, 0, ?_, Subring.zero_mem _, by simp⟩` and prove the remaining obligations. Simplify `he)` using `using h 1 (Subring.one_mem _) (by simpa`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`.

Conclude with `he (Subring.zero_mem _)`. Establish `hlt : 1 < Valued.v e` using `not_le.mp ((mem_int_iff e).not.mp he)`. Establish `hinv : e⁻¹ ∈ Formalism.UG.intL L`. Rewrite using `[mem_int_iff, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ hlt.le`.

Use `⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_cancel₀ he0]`. Conclude with `Subring.one_mem _`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

/- English proof (translation)
Establish `key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b`. Introduce `k`. Apply `one_dim` to reduce the goal to its premises. Introduce `c hc hec`. Use `h (Pi.single k c) ?_ ?_` as an intermediate fact.

Simplify `this` using `[Pi.single_apply]`. Introduce `i`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Simplify using `using hc`.

Simplify using `[hi]`. Introduce `j`. Rewrite using `[Matrix.mulVec_single]`. Distinguish the cases in `hj : (k : ℕ) = (j : ℕ)`. Establish `hk : (k : ℕ) < m` using `hj ▸ j.2`.

Establish `: (⟨k, hk⟩ : Fin m) = j` using `Fin.ext hj`. Rewrite `hec` using `[dif_pos hk, this]`. Simplify `hec` using `[hj]`. Simplify using `[hj]`. Use `choose a b ha hb hz using key`.

Use `⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩` and prove the remaining obligations. Introduce `j dsimp only split_ifs`. Conclude with `hb _`. Conclude with `Subring.zero_mem _`. Use function extensionality and compare the values at `k`.

Rewrite using `[hz k, Pi.add_apply]`. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]`. Distinguish the cases in `hk : (k : ℕ) < m`. Rewrite using `[dif_pos hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Establish `: (k : ℕ) ≠ (j : ℕ)` using `fun e => hj (Fin.ext e.symm)`. Simplify using `[this]`. Simplify using the standard rewrite rules.

Rewrite using `[dif_neg hk, zero_mul]`. Use `symm`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `: (k : ℕ) ≠ (j : ℕ)` using `fun e => hk (e ▸ j.2)`. Simplify using `[this]`.
-/
theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dif_pos hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dif_pos hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dif_neg hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

/- English proof (translation)
Introduce `L _ _ m n x z h`. Take `⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩` from `GlobalTheory.T.smithNormalForm_discreteValuationField L m n x`. Use `set D : Matrix (Fin m) (Fin n) L := Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD`. Establish `hPP' : P' * P = 1` using `mul_eq_one_comm.mp hPP`. Establish `hQQ' : Q' * Q = 1` using `mul_eq_one_comm.mp hQQ`.

Take `⟨l, w, hl, hw, hz⟩` from `diag_case d (Q'ᵀ *ᵥ z) (by`. Introduce `s hs hDs`. Establish `h1` using `h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by`. Establish `: x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s)`. Rewrite using `[hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]`.

Rewrite using `[this]`. Conclude with `mulVec_int _ _ hP hDs)`. Establish `h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i`. Express the relevant statement in the definitionally equal form `s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z`. Rewrite using `[Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.

Rewrite using `[h2]`. Conclude with `h1)`. Use `⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl, mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩` and prove the remaining obligations. Establish `h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z)`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]`.

Establish `h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]`. Rewrite using `[h4, ← Matrix.mulVec_add, ← hz]`. Conclude with `h3`.
-/
theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := GlobalTheory.T.smithNormalForm_discreteValuationField L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
