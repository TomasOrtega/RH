import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConvAlg

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hu.2 _`. Conclude with `hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) h)`.
-/
theorem ut_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (j : Fin (r + 1)) :
    u (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  split_ifs with h
  · subst h; exact hu.2 _
  · exact hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) h)

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hij => hu.1 i j hij)]`. Simplify using `[hu.2]`.
-/
theorem ut_det {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) : u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, ut_last hu, Matrix.one_apply]`. Distinguish the cases in `h : j = Fin.last r`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem ut_sub_one_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (x : Fin (r + 1) → ℂ) : ((u - 1) *ᵥ x) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sub_apply, ut_last hu, Matrix.one_apply]
  by_cases h : j = Fin.last r
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Break down `lt_or_eq_of_le h with h | h` into its components or cases. Rewrite using `[Matrix.sub_apply, hu.1 d c h, Matrix.one_apply_ne (by intro e; subst e; omega), sub_self]`. Establish `: c = d` using `Fin.ext h`. Substitute `this` using the available equality. Rewrite using `[Matrix.sub_apply, hu.2, Matrix.one_apply_eq, sub_self]`.
-/
theorem ut_sub_one_col {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (c d : Fin (r + 1)) (h : c.val ≤ d.val) : (u - 1) d c = 0 := by
  rcases lt_or_eq_of_le h with h | h
  · rw [Matrix.sub_apply, hu.1 d c h, Matrix.one_apply_ne (by intro e; subst e; omega), sub_self]
  · have : c = d := Fin.ext h
    subst this; rw [Matrix.sub_apply, hu.2, Matrix.one_apply_eq, sub_self]

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[ut_last hu]`. Distinguish the cases in `ha : a = Fin.last r`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [ha, if_false, star_zero, zero_mul]`. Conclude with `(hv a (lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun e => ha (Fin.ext e)))).symm`. Introduce `b _ hb`.

Rewrite using `[hv b (lt_of_le_of_ne (Nat.lt_succ_iff.mp b.isLt) (fun e => hb (Fin.ext e))), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem ut_conj_fix {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (v : Fin (r + 1) → ℂ) (hv : ∀ a : Fin (r + 1), a.val < r → v a = 0) : uᴴ *ᵥ v = v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu]
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · simp only [ha, if_false, star_zero, zero_mul]
      exact (hv a (lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun e => ha (Fin.ext e)))).symm
  · intro b _ hb
    rw [hv b (lt_of_le_of_ne (Nat.lt_succ_iff.mp b.isLt) (fun e => hb (Fin.ext e))), mul_zero]
  · simp

/- English proof (translation)
Establish `hA : IsUnit (uᴴ * Z).det`. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose, ut_det hu, star_one, one_mul]`. Conclude with `hZ`. Establish `h0 : (uᴴ * Z) *ᵥ ((u' - 1) *ᵥ c) = 0`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hp, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ut_conj_fix hu _ hc, sub_self]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]`. Use `_ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]`.
-/
theorem cancel_of_pair {r : ℕ} {u u' Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (hZ : IsUnit Z.det) (hp : uᴴ * Z * u' = Z) (c : Fin (r + 1) → ℂ)
    (hc : ∀ a : Fin (r + 1), a.val < r → (Z *ᵥ c) a = 0) : (u' - 1) *ᵥ c = 0 := by
  have hA : IsUnit (uᴴ * Z).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, ut_det hu, star_one, one_mul]; exact hZ
  have h0 : (uᴴ * Z) *ᵥ ((u' - 1) *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hp, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ut_conj_fix hu _ hc, sub_self]
  calc (u' - 1) *ᵥ c = ((uᴴ * Z)⁻¹ * (uᴴ * Z)) *ᵥ ((u' - 1) *ᵥ c) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Adiag, Matrix.mul_apply]`. Repeatedly rewrite using `[Matrix.mul_diagonal, Matrix.conjTranspose_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[ut_last hu a, ut_last hu b, Matrix.diagonal_apply]`.

Apply the tactic sequence `by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r`. Substitute `ha` using the available equality. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Substitute `ha` using the available equality.

Simplify using `[hb, Ne.symm hb]`. Substitute `hb` using the available equality. Simplify using `[ha]`. Simplify using `[ha, hb]`. Introduce `c _ hc`.

Simplify using `[hc]`. Simplify using the standard rewrite rules.
-/
theorem ut_adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hu : u ∈ UTset (r + 1)) : uᴴ * Adiag k r z * u = Adiag k r z := by
  ext a b
  rw [Adiag, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu a, ut_last hu b, Matrix.diagonal_apply]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
    · subst ha; subst hb; simp
    · subst ha; simp [hb, Ne.symm hb]
    · subst hb; simp [ha]
    · simp [ha, hb]
  · intro c _ hc; simp [hc]
  · simp

/- English proof (translation)
Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : a ≤ c.val`. Simplify using `[hx c hc]`. Establish `hcr : c.val < r` using `by omega`.

Establish `hne : i ≠ eI k r ⟨c.val, hcr⟩`. Introduce `e`. Rewrite `e` using `[Fin.ext_iff]`. Simplify using `[eI] at e`. Use linear arithmetic over natural numbers and integers.

Simplify using `[fvec, hcr, bvec, Pi.single_apply, hne]`.
-/
theorem lowSupp (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : ℕ) (ha : a ≤ r) (x : Fin (r + 1) → ℂ)
    (hx : ∀ c : Fin (r + 1), a ≤ c.val → x c = 0) (i : Fin (2 * r + k + 1)) (hi : a ≤ i.val) :
    (∑ c, x c • fvec k r z c) i = 0 := by
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : a ≤ c.val
  · simp [hx c hc]
  · have hcr : c.val < r := by omega
    have hne : i ≠ eI k r ⟨c.val, hcr⟩ := by
      intro e; rw [Fin.ext_iff] at e; simp [eI] at e; omega
    simp [fvec, hcr, bvec, Pi.single_apply, hne]

end PI.StabPairs.Conv
