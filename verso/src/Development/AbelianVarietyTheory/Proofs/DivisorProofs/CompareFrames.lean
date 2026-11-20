import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue.Lattice

variable {K : Type} [Field K]

/- English proof (translation)
Establish `key : ∀ a b : K, w a ≤ w b → w (a + b) ≤ w b`. Introduce `a b hab`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Simplify using `using hab`.

Establish `hb' : 0 < w b` using `w.pos hb`. Establish `h1 : a / b ∈ O`. Rewrite using `[hO, map_div₀]`. Conclude with `(div_le_one hb').2 hab`. Establish `h2 : a / b + 1 ∈ O` using `O.add_mem _ _ h1 O.one_mem`.

Rewrite `h2` using `[hO]`. Establish `h3 : a + b = (a / b + 1) * b` using `by field_simp`. Rewrite using `[h3, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Break down `le_total (w x) (w y) with h | h` into its components or cases.

Conclude with `(key x y h).trans (le_max_right _ _)`. Rewrite using `[add_comm]`. Conclude with `(key y x h).trans (le_max_left _ _)`.
-/
theorem add_le_max (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (x y : K) :
    w (x + y) ≤ max (w x) (w y) := by
  have key : ∀ a b : K, w a ≤ w b → w (a + b) ≤ w b := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simpa using hab
    · have hb' : 0 < w b := w.pos hb
      have h1 : a / b ∈ O := by
        rw [hO, map_div₀]
        exact (div_le_one hb').2 hab
      have h2 : a / b + 1 ∈ O := O.add_mem _ _ h1 O.one_mem
      rw [hO] at h2
      have h3 : a + b = (a / b + 1) * b := by field_simp
      rw [h3, map_mul]
      calc w (a / b + 1) * w b ≤ 1 * w b := by gcongr
        _ = w b := one_mul _
  rcases le_total (w x) (w y) with h | h
  · exact (key x y h).trans (le_max_right _ _)
  · rw [add_comm]
    exact (key y x h).trans (le_max_left _ _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Use `(add_le_max w O hO _ _).trans_lt (max_lt (hf a (Finset.mem_insert_self _ _)) (ih ?_))` and prove the remaining obligations.

Introduce `i hi`. Conclude with `hf i (Finset.mem_insert_of_mem hi)`.
-/
theorem sum_lt_one (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) {ι : Type}
    (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, w (f i) < 1) : w (∑ i ∈ s, f i) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (add_le_max w O hO _ _).trans_lt (max_lt (hf a (Finset.mem_insert_self _ _)) (ih ?_))
    intro i hi
    exact hf i (Finset.mem_insert_of_mem hi)

/- English proof (translation)
Set `M' : Matrix (Fin n) (Fin n) O` to `Matrix.of fun i j => ⟨M i j, (hO _).2 (hM i j)⟩`. Establish `hM' : O.subtype.mapMatrix M' = M`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hadj : M.adjugate r c = (M'.adjugate r c : K)`.

Rewrite using `[← hM', ← RingHom.map_adjugate]`. Both sides reduce to the same expression. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd, inv_one, one_mul, hadj]`. Conclude with `(hO _).1 (M'.adjugate r c).2`.
-/
theorem inv_le_one (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ r c, w (M r c) ≤ 1) (hd : w M.det = 1) (r c : Fin n) :
    w (M⁻¹ r c) ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨M i j, (hO _).2 (hM i j)⟩
  have hM' : O.subtype.mapMatrix M' = M := by
    ext i j
    rfl
  have hadj : M.adjugate r c = (M'.adjugate r c : K) := by
    rw [← hM', ← RingHom.map_adjugate]
    rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd, inv_one, one_mul,
    hadj]
  exact (hO _).1 (M'.adjugate r c).2

/- English proof (translation)
Introduce `K _ w O hO g Ha Hb βa βb τa τb Ma hta htb hda _ _ hB _ _ _ h2 hMa hdet hcol k i`. Establish `hdetβ : IsUnit βa.det`. Rewrite using `[Matrix.det_of_upperTriangular hta, isUnit_iff_ne_zero]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => hda j`. Establish `hdetM : IsUnit Ma.det`.

Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h`. Rewrite `hdet` using `[h]`. Simplify using `at hdet`. Use `letI : Invertible βa := βa.invertibleOfIsUnitDet hdetβ`.

Use `set Q : Matrix (Fin g) (Fin g) K := βa⁻¹ * βb with hQ`. Establish `hQt : Q.BlockTriangular id` using `(Matrix.blockTriangular_inv_of_blockTriangular hta).mul htb`. Establish `hβQ : βa * Q = βb`. Rewrite using `[hQ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetβ, Matrix.one_mul]`. Establish `hQd : Q k k = βb k k / βa k k`.

Rewrite using `[eq_div_iff (hda k), ← hβQ, Matrix.mul_apply, Finset.sum_eq_single k, mul_comm]`. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hta (show id j < id k from h), zero_mul]`. Rewrite using `[hQt (show id k < id j from h), mul_zero]`.

Simplify using the standard rewrite rules. Set `E : Matrix (Fin (g + g)) (Fin g) K` to `Matrix.of fun r j => if r = Fin.castAdd g j then 1 else 0`. Establish `hME : Ma * E = Ha * βa`. Use extensionality with `r j`. Rewrite using `[← hcol, Matrix.mul_apply]`.

Simplify using `[E]`. Establish `hC : Ma⁻¹ * (Ha * βb) = E * Q`. Rewrite using `[← hβQ, ← Matrix.mul_assoc Ha, ← hME, Matrix.mul_assoc Ma E Q, ← Matrix.mul_assoc Ma⁻¹ Ma, Matrix.nonsing_inv_mul _ hdetM, Matrix.one_mul]`. Establish `hD : ∀ r, w ((Hb * βb - Ha * βb) r k) < 1`. Introduce `r`.

Establish `h` using `h2 (fun j => βb j k) (fun r' => hB r' k) r`. Rewrite `h` using `[w.map_sub]`. Conclude with `h`. Establish `hdiff : ∀ r, w ((Ma⁻¹ * (Hb * βb)) r k - (E * Q) r k) < 1`. Introduce `r`.

Rewrite using `[← hC, ← Matrix.sub_apply, ← Matrix.mul_sub, Matrix.mul_apply]`. Use `sum_lt_one w O hO _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (inv_le_one w O hO Ma hMa hdet r j) (w.nonneg _) (hD j)`. Use `⟨fun hki => ?_, ?_⟩` and prove the remaining obligations.

Establish `h0 : (E * Q) i k = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = Fin.castAdd g j`. Substitute `hij` using the available equality.

Rewrite using `[hQt (show id k < id j from hki), mul_zero]`. Simplify using `[E, hij]`. Establish `h` using `hdiff i`. Rewrite `h` using `[h0, sub_zero]`. Then use the resulting hypothesis. Establish `h0 : (E * Q) (Fin.castAdd g k) k = βb k k / βa k k`.

Rewrite using `[← hQd, Matrix.mul_apply, Finset.sum_eq_single k]`. Simplify using `[E]`. Introduce `j _ hj`. Establish `: Fin.castAdd g k ≠ Fin.castAdd g j` using `fun h => hj (Fin.castAdd_injective _ _ h).symm`. Simplify using `[E, this]`.

Simplify using the standard rewrite rules. Establish `h` using `hdiff (Fin.castAdd g k)`. Rewrite `h` using `[h0]`. Then use the resulting hypothesis.
-/
theorem compare_frames : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) → ∀ {g : ℕ} (Ha Hb : Matrix (Fin (g + g)) (Fin g) K) (βa βb : Matrix (Fin g) (Fin g) K) (τa τb : Fin g → Fin (g + g)) (Ma : Matrix (Fin (g + g)) (Fin (g + g)) K), βa.BlockTriangular id → βb.BlockTriangular id → (∀ k, βa k k ≠ 0) → (∀ k, βb k k ≠ 0) → (∀ r k, w ((Ha * βa) r k) ≤ 1) → (∀ r k, w ((Hb * βb) r k) ≤ 1) → w (rowSel τa * (Ha * βa)).det = 1 → w (rowSel τb * (Hb * βb)).det = 1 → (∀ u, (∀ r, w ((Ha *ᵥ u) r) ≤ 1) → ∀ r, w ((Hb *ᵥ u) r - (Ha *ᵥ u) r) < 1) → (∀ u, (∀ r, w ((Hb *ᵥ u) r) ≤ 1) → ∀ r, w ((Ha *ᵥ u) r - (Hb *ᵥ u) r) < 1) → (∀ r c, w (Ma r c) ≤ 1) → w Ma.det = 1 → (∀ r (k : Fin g), Ma r (Fin.castAdd g k) = (Ha * βa) r k) → ∀ (k : Fin g) (i : Fin (g + g)), ((k : ℕ) < i → w ((Ma⁻¹ * (Hb * βb)) i k) < 1) ∧ w ((Ma⁻¹ * (Hb * βb)) (Fin.castAdd g k) k - βb k k / βa k k) < 1 := by
  intro K _ w O hO g Ha Hb βa βb τa τb Ma hta htb hda _ _ hB _ _ _ h2 hMa hdet hcol k i
  have hdetβ : IsUnit βa.det := by
    rw [Matrix.det_of_upperTriangular hta, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hda j
  have hdetM : IsUnit Ma.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    rw [h] at hdet
    simp at hdet
  letI : Invertible βa := βa.invertibleOfIsUnitDet hdetβ
  set Q : Matrix (Fin g) (Fin g) K := βa⁻¹ * βb with hQ
  have hQt : Q.BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hta).mul htb
  have hβQ : βa * Q = βb := by
    rw [hQ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetβ, Matrix.one_mul]
  have hQd : Q k k = βb k k / βa k k := by
    rw [eq_div_iff (hda k), ← hβQ, Matrix.mul_apply, Finset.sum_eq_single k, mul_comm]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hta (show id j < id k from h), zero_mul]
      · rw [hQt (show id k < id j from h), mul_zero]
    · simp
  let E : Matrix (Fin (g + g)) (Fin g) K := Matrix.of fun r j => if r = Fin.castAdd g j then 1 else 0
  have hME : Ma * E = Ha * βa := by
    ext r j
    rw [← hcol, Matrix.mul_apply]
    simp [E]
  have hC : Ma⁻¹ * (Ha * βb) = E * Q := by
    rw [← hβQ, ← Matrix.mul_assoc Ha, ← hME, Matrix.mul_assoc Ma E Q, ← Matrix.mul_assoc Ma⁻¹ Ma,
      Matrix.nonsing_inv_mul _ hdetM, Matrix.one_mul]
  have hD : ∀ r, w ((Hb * βb - Ha * βb) r k) < 1 := by
    intro r
    have h := h2 (fun j => βb j k) (fun r' => hB r' k) r
    rw [w.map_sub] at h
    exact h
  have hdiff : ∀ r, w ((Ma⁻¹ * (Hb * βb)) r k - (E * Q) r k) < 1 := by
    intro r
    rw [← hC, ← Matrix.sub_apply, ← Matrix.mul_sub, Matrix.mul_apply]
    refine sum_lt_one w O hO _ _ fun j _ => ?_
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (inv_le_one w O hO Ma hMa hdet r j) (w.nonneg _) (hD j)
  refine ⟨fun hki => ?_, ?_⟩
  · have h0 : (E * Q) i k = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hij : i = Fin.castAdd g j
      · subst hij
        rw [hQt (show id k < id j from hki), mul_zero]
      · simp [E, hij]
    have h := hdiff i
    rwa [h0, sub_zero] at h
  · have h0 : (E * Q) (Fin.castAdd g k) k = βb k k / βa k k := by
      rw [← hQd, Matrix.mul_apply, Finset.sum_eq_single k]
      · simp [E]
      · intro j _ hj
        have : Fin.castAdd g k ≠ Fin.castAdd g j := fun h => hj (Fin.castAdd_injective _ _ h).symm
        simp [E, this]
      · simp
    have h := hdiff (Fin.castAdd g k)
    rwa [h0] at h

end GlobalTheory.WholeFlag.Glue.Lattice
