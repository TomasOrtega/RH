import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]`. Establish `hs : ∑ k ∈ Finset.univ.erase m, q i k * rowM m ξ k j = if j = m then 0 else q i j`. Establish `hk1 : ∀ k ∈ Finset.univ.erase m, q i k * rowM m ξ k j = q i k * (1 : Matrix (Fin n) (Fin n) R) k j`. Introduce `k hk`. Establish `hkm : k ≠ m` using `Finset.ne_of_mem_erase hk`.

Simplify using `[rowM, hkm]`. Rewrite using `[Finset.sum_congr rfl hk1]`. Use `split_ifs with hjm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k hk`.

Rewrite using `[Matrix.one_apply_ne (by rw [hjm]; exact Finset.ne_of_mem_erase hk), mul_zero]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Matrix.one_apply_ne hb, mul_zero]`.

Introduce `hj`. Conclude with `absurd (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩) hj`. Rewrite using `[hs, add_comm]`. Use `congr 1`. Distinguish the cases in `hjm : j ≤ m`.

Simplify using `[rowM, hjm]`. Establish `hmj : m ≠ j` using `fun h => hjm (le_of_eq h.symm)`. Simplify using `[rowM, hjm, Matrix.one_apply_ne hmj]`.
-/
private theorem mul_rowM_apply {R : Type} [CommRing R] {n : ℕ} (m : Fin n) (ξ : Fin n → R)
    (q : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (q * rowM m ξ) i j
      = (if j = m then 0 else q i j) + q i m * (if j ≤ m then ξ j else 0) := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
  have hs : ∑ k ∈ Finset.univ.erase m, q i k * rowM m ξ k j = if j = m then 0 else q i j := by
    have hk1 : ∀ k ∈ Finset.univ.erase m,
        q i k * rowM m ξ k j = q i k * (1 : Matrix (Fin n) (Fin n) R) k j := by
      intro k hk
      have hkm : k ≠ m := Finset.ne_of_mem_erase hk
      simp [rowM, hkm]
    rw [Finset.sum_congr rfl hk1]
    split_ifs with hjm
    · apply Finset.sum_eq_zero
      intro k hk
      rw [Matrix.one_apply_ne (by rw [hjm]; exact Finset.ne_of_mem_erase hk), mul_zero]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply_ne hb, mul_zero]
      · intro hj
        exact absurd (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩) hj
  rw [hs, add_comm]
  congr 1
  by_cases hjm : j ≤ m
  · simp [rowM, hjm]
  · have hmj : m ≠ j := fun h => hjm (le_of_eq h.symm)
    simp [rowM, hjm, Matrix.one_apply_ne hmj]

/- English proof (translation)
Unfold `UpperTheory.V.Af.Smo.RowStep IsY`. Introduce `R _ n m p s hp hs`. Establish `key : ∀ i j, (p : Matrix (Fin n) (Fin n) R) i j = (if j = m then 0 else ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) + ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i m * (if j ≤ m then (p : Matrix (Fin n) (Fin n) R) m j else 0)`. Introduce `i j`. Establish `h` using `mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m) ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j`.

Rewrite `h` using `[← hs, ← Units.val_mul, inv_mul_cancel_right]`. Conclude with `h`. Establish `hu : ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m * (p : Matrix (Fin n) (Fin n) R) m m = 1`. Establish `h` using `mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m) ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m`. Rewrite `h` using `[← hs, ← Units.val_mul, inv_mul_cancel]`.

Simplify using `using h.symm`. Generalize the expression as in `((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m = t at hu`. Generalize the expression as in `((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Q at key ⊢`. Generalize the expression as in `(p : Matrix (Fin n) (Fin n) R) = P at key hu hp`. Introduce `i hi`.

Break down `eq_or_lt_of_le hi with h | h` into its components or cases. Establish `him : i = m` using `Fin.ext h.symm`. Rewrite using `[him]`. Establish `k` using `key m m`. Rewrite `k` using `[if_pos rfl, if_pos le_rfl, zero_add]`.

Establish `hQ : Q m m = 1` using `by linear_combination (-t) * k + (1 - Q m m) * hu`. Use `⟨hQ, fun j hj => ?_⟩` and prove the remaining obligations. Establish `k2` using `key m j`. Rewrite `k2` using `[if_neg (ne_of_lt hj), if_pos (le_of_lt hj), hQ, one_mul]`. Take the linear combination `-k2`.

Establish `hi1 : (m : ℕ) + 1 ≤ (i : ℕ)` using `h`. Take `⟨hpi, hpj⟩` from `hp i hi1`. Establish `hmi : m < i` using `h`. Establish `k` using `key i m`. Rewrite `k` using `[if_pos rfl, if_pos le_rfl, zero_add, hpj m hmi]`.

Establish `hQm : Q i m = 0` using `by linear_combination (-Q i m) * hu - t * k`. Prove the components needed by the constructor for the conclusion. Establish `k2` using `key i i`. Rewrite `k2` using `[if_neg (ne_of_gt hmi), if_neg (not_le.mpr hmi), mul_zero, add_zero, hpi]`. Conclude with `k2.symm`.

Introduce `j hj`. Establish `k2` using `key i j`. Rewrite `k2` using `[hpj j hj]`. Distinguish the cases in `hjm : j = m`. Rewrite using `[hjm]`.

Conclude with `hQm`. Rewrite `k2` using `[if_neg hjm, hQm, zero_mul, add_zero]`. Conclude with `k2.symm`.
-/
theorem UpperTheory.V.Af.Smo.rowStep :
    UpperTheory.V.Af.Smo.RowStep := by
  unfold UpperTheory.V.Af.Smo.RowStep IsY
  intro R _ n m p s hp hs
  have key : ∀ i j, (p : Matrix (Fin n) (Fin n) R) i j
      = (if j = m then 0 else ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j)
        + ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i m
          * (if j ≤ m then (p : Matrix (Fin n) (Fin n) R) m j else 0) := by
    intro i j
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
    rw [← hs, ← Units.val_mul, inv_mul_cancel_right] at h
    exact h
  have hu : ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
      * (p : Matrix (Fin n) (Fin n) R) m m = 1 := by
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
    rw [← hs, ← Units.val_mul, inv_mul_cancel] at h
    simpa using h.symm
  generalize ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m = t at hu
  generalize ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Q at key ⊢
  generalize (p : Matrix (Fin n) (Fin n) R) = P at key hu hp
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · have him : i = m := Fin.ext h.symm
    rw [him]
    have k := key m m
    rw [if_pos rfl, if_pos le_rfl, zero_add] at k
    have hQ : Q m m = 1 := by linear_combination (-t) * k + (1 - Q m m) * hu
    refine ⟨hQ, fun j hj => ?_⟩
    have k2 := key m j
    rw [if_neg (ne_of_lt hj), if_pos (le_of_lt hj), hQ, one_mul] at k2
    linear_combination -k2
  · have hi1 : (m : ℕ) + 1 ≤ (i : ℕ) := h
    obtain ⟨hpi, hpj⟩ := hp i hi1
    have hmi : m < i := h
    have k := key i m
    rw [if_pos rfl, if_pos le_rfl, zero_add, hpj m hmi] at k
    have hQm : Q i m = 0 := by linear_combination (-Q i m) * hu - t * k
    constructor
    · have k2 := key i i
      rw [if_neg (ne_of_gt hmi), if_neg (not_le.mpr hmi), mul_zero, add_zero, hpi] at k2
      exact k2.symm
    · intro j hj
      have k2 := key i j
      rw [hpj j hj] at k2
      by_cases hjm : j = m
      · rw [hjm]
        exact hQm
      · rw [if_neg hjm, hQm, zero_mul, add_zero] at k2
        exact k2.symm
