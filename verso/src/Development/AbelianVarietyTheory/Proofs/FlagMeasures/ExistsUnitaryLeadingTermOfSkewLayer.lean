import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

/- English proof (translation)
Establish `hu : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `cL : ∀ B : Matrix (Fin n) (Fin n) K, J * (J⁻¹ * B) = B` using `fun B => Matrix.mul_nonsing_inv_cancel_left J B hu`. Establish `cL' : ∀ B : Matrix (Fin n) (Fin n) K, J⁻¹ * (J * B) = B` using `fun B => Matrix.nonsing_inv_mul_cancel_left J B hu`. Establish `cR : J * J⁻¹ = 1` using `Matrix.mul_nonsing_inv J hu`. Establish `cR' : J⁻¹ * J = 1` using `Matrix.nonsing_inv_mul J hu`.

Establish `hJi : (J⁻¹)ᴴ = J⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hJ]`. Establish `hanti : Antitone A` using `antitone_nat_of_succ_le hA`. Establish `to0 : ∀ {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → M ∈ A 0` using `fun h => hanti (Nat.zero_le _) h`. Establish `smem : ∀ (r : R) {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → algebraMap R K r • M ∈ A d`. Introduce `r d M h`.

Rewrite using `[algebraMap_smul]`. Conclude with `(A d).smul_mem r h`. Use `set β : K := algebraMap R K w with hβ`. Establish `hst : star β = 1 - β` using `by rw [← hw]; ring`. Establish `key : ∀ k : ℕ, ∃ Y ∈ A (c + 1), J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A (c + 1 + k)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Use `⟨0, (A (c + 1)).zero_mem, ?_⟩` and prove the remaining obligations. Establish `hX' : Xᴴ = -(J * (X * J⁻¹))`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, cR, mul_one, cL]`. Use `_ = -(J * (X * J⁻¹)) := by rw [hskew]; simp only [neg_mul, mul_neg]`. Establish `h0 : J⁻¹ * (1 + X + 0)ᴴ * J * (1 + X + 0) - 1 = -(X * X)`. Simplify using `only [add_zero, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX']`.

Simplify using `only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, cL', cR']`. Normalize the expressions using the abelian group laws. Rewrite using `[h0, Nat.add_zero]`. Conclude with `(A (c + 1)).neg_mem (hmul c X hX X (to0 hX)).1`. Consider the case `succ k ih`.

Take `⟨Y, hY, hE⟩` from `ih`. Use `set g := 1 + X + Y with hg`. Use `set E := J⁻¹ * gᴴ * J * g - 1 with hEdef`. Establish `hEE : E * E ∈ A (c + 1 + (k + 1))` using `(hmul (c + 1 + k) E hE E (to0 hE)).1`. Establish `hEEE : E * (E * E) ∈ A (c + 1 + (k + 1))` using `(hmul (c + 1 + k) E hE (E * E) (to0 hEE)).1`.

Use `⟨Y - β • (g * E), ?_, ?_⟩` and prove the remaining obligations. Establish `hEc : E ∈ A (c + 1)` using `hanti (by omega) hE`. Establish `hgE : g * E ∈ A (c + 1)`. Rewrite using `[hg, add_mul, add_mul, one_mul]`. Conclude with `add_mem (add_mem hEc (hmul c X hX E (to0 hE)).1) (hanti (by omega) (hmul (c + 1) Y hY E (to0 hE)).1)`.

Conclude with `sub_mem hY (smem w hgE)`. Establish `hgeq : 1 + X + (Y - β • (g * E)) = g - β • (g * E)` using `by rw [hg]; abel`. Rewrite using `[hgeq]`. Establish `hEH : J⁻¹ * Eᴴ * J = E`. Rewrite using `[hEdef]`.

Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJi, hJ, sub_mul, mul_sub, mul_one, mul_assoc, cR']`. Establish `h1 : J⁻¹ * (Eᴴ * (gᴴ * J)) = E * (J⁻¹ * (gᴴ * J))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, cL]`. Use `_ = E * (J⁻¹ * (gᴴ * J)) := by rw [hEH]`.

Establish `hP' : J⁻¹ * (g - β • (g * E))ᴴ * J = J⁻¹ * (gᴴ * J) - star β • (E * (J⁻¹ * (gᴴ * J)))`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, h1]`. Establish `hPg0 : J⁻¹ * (gᴴ * (J * g)) = 1 + E`. Rewrite using `[hEdef]`. Simplify using `only [mul_assoc]`.

Normalize the expressions using the abelian group laws. Establish `hPg : ∀ M, J⁻¹ * (gᴴ * (J * (g * M))) = M + E * M`. Introduce `M`. Rewrite using `[hEdef]`. Simplify using `only [sub_mul, one_mul, mul_assoc]`.

Normalize the expressions using the abelian group laws. Establish `hid : J⁻¹ * (g - β • (g * E))ᴴ * J * (g - β • (g * E)) - 1 = (β - β * β - 1) • (E * E) + (β - β * β) • (E * (E * E))`. Rewrite using `[hP']`. Simplify using `only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, hPg, hPg0, mul_add, mul_one, smul_add, hst]`. Use `module`.

Establish `s1 : β - β * β - 1 = algebraMap R K (w - w * w - 1)` using `by simp [hβ]`. Establish `s2 : β - β * β = algebraMap R K (w - w * w)` using `by simp [hβ]`. Rewrite using `[hid, s1, s2]`. Conclude with `add_mem (smem _ hEE) (smem _ hEEE)`. Take `⟨Y, hY, hEm⟩` from `key m`.

Use `⟨Y, hY, ?_⟩` and prove the remaining obligations. Establish `hz : J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A m` using `hanti (by omega) hEm`. Rewrite `hz` using `[hm, Submodule.mem_bot, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_unitary_of_skew_layer (R K : Type) [CommRing R] [Field K] [StarRing K]
    [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R)
    (hJ : Jᴴ = J) (hdet : J.det ≠ 0)
    (hw : algebraMap R K w + star (algebraMap R K w) = 1)
    (hA : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (_hadj : ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c)
    (c : ℕ) (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ A c) (hskew : J⁻¹ * Xᴴ * J = -X) :
    ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  classical
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have cL : ∀ B : Matrix (Fin n) (Fin n) K, J * (J⁻¹ * B) = B :=
    fun B => Matrix.mul_nonsing_inv_cancel_left J B hu
  have cL' : ∀ B : Matrix (Fin n) (Fin n) K, J⁻¹ * (J * B) = B :=
    fun B => Matrix.nonsing_inv_mul_cancel_left J B hu
  have cR : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have cR' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJi : (J⁻¹)ᴴ = J⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hJ]
  have hanti : Antitone A := antitone_nat_of_succ_le hA
  have to0 : ∀ {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → M ∈ A 0 :=
    fun h => hanti (Nat.zero_le _) h
  have smem : ∀ (r : R) {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d →
      algebraMap R K r • M ∈ A d := by
    intro r d M h
    rw [algebraMap_smul]
    exact (A d).smul_mem r h
  set β : K := algebraMap R K w with hβ
  have hst : star β = 1 - β := by rw [← hw]; ring

  have key : ∀ k : ℕ, ∃ Y ∈ A (c + 1),
      J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A (c + 1 + k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, (A (c + 1)).zero_mem, ?_⟩
      have hX' : Xᴴ = -(J * (X * J⁻¹)) := by
        calc Xᴴ = J * ((J⁻¹ * Xᴴ * J) * J⁻¹) := by
              simp only [mul_assoc, cR, mul_one, cL]
          _ = -(J * (X * J⁻¹)) := by rw [hskew]; simp only [neg_mul, mul_neg]
      have h0 : J⁻¹ * (1 + X + 0)ᴴ * J * (1 + X + 0) - 1 = -(X * X) := by
        simp only [add_zero, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX']
        simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, cL', cR']
        abel
      rw [h0, Nat.add_zero]
      exact (A (c + 1)).neg_mem (hmul c X hX X (to0 hX)).1
    | succ k ih =>
      obtain ⟨Y, hY, hE⟩ := ih
      set g := 1 + X + Y with hg
      set E := J⁻¹ * gᴴ * J * g - 1 with hEdef
      have hEE : E * E ∈ A (c + 1 + (k + 1)) := (hmul (c + 1 + k) E hE E (to0 hE)).1
      have hEEE : E * (E * E) ∈ A (c + 1 + (k + 1)) :=
        (hmul (c + 1 + k) E hE (E * E) (to0 hEE)).1
      refine ⟨Y - β • (g * E), ?_, ?_⟩
      · have hEc : E ∈ A (c + 1) := hanti (by omega) hE
        have hgE : g * E ∈ A (c + 1) := by
          rw [hg, add_mul, add_mul, one_mul]
          exact add_mem (add_mem hEc (hmul c X hX E (to0 hE)).1)
            (hanti (by omega) (hmul (c + 1) Y hY E (to0 hE)).1)
        exact sub_mem hY (smem w hgE)
      · have hgeq : 1 + X + (Y - β • (g * E)) = g - β • (g * E) := by rw [hg]; abel
        rw [hgeq]

        have hEH : J⁻¹ * Eᴴ * J = E := by
          rw [hEdef]
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hJi, hJ, sub_mul, mul_sub, mul_one, mul_assoc, cR']
        have h1 : J⁻¹ * (Eᴴ * (gᴴ * J)) = E * (J⁻¹ * (gᴴ * J)) := by
          calc J⁻¹ * (Eᴴ * (gᴴ * J)) = (J⁻¹ * Eᴴ * J) * (J⁻¹ * (gᴴ * J)) := by
                simp only [mul_assoc, cL]
            _ = E * (J⁻¹ * (gᴴ * J)) := by rw [hEH]
        have hP' : J⁻¹ * (g - β • (g * E))ᴴ * J
            = J⁻¹ * (gᴴ * J) - star β • (E * (J⁻¹ * (gᴴ * J))) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
            mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, h1]
        have hPg0 : J⁻¹ * (gᴴ * (J * g)) = 1 + E := by
          rw [hEdef]; simp only [mul_assoc]; abel
        have hPg : ∀ M, J⁻¹ * (gᴴ * (J * (g * M))) = M + E * M := by
          intro M
          rw [hEdef]; simp only [sub_mul, one_mul, mul_assoc]; abel
        have hid : J⁻¹ * (g - β • (g * E))ᴴ * J * (g - β • (g * E)) - 1
            = (β - β * β - 1) • (E * E) + (β - β * β) • (E * (E * E)) := by
          rw [hP']
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, hPg, hPg0,
            mul_add, mul_one, smul_add, hst]
          module
        have s1 : β - β * β - 1 = algebraMap R K (w - w * w - 1) := by simp [hβ]
        have s2 : β - β * β = algebraMap R K (w - w * w) := by simp [hβ]
        rw [hid, s1, s2]
        exact add_mem (smem _ hEE) (smem _ hEEE)
  obtain ⟨Y, hY, hEm⟩ := key m
  refine ⟨Y, hY, ?_⟩
  have hz : J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A m := hanti (by omega) hEm
  rw [hm, Submodule.mem_bot, sub_eq_zero] at hz
  calc (1 + X + Y)ᴴ * J * (1 + X + Y)
      = J * (J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y)) := by simp only [mul_assoc, cL]
    _ = J := by rw [hz, mul_one]

end GlobalTheory.RadCov
