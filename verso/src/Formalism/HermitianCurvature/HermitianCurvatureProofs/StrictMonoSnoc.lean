import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [Matrix.updateRow_self])`. Consider the case `@insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]`.
-/
theorem det_row_sum {n : ℕ} {ι : Type} (s : Finset ι) (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (c : ι → ℂ)
    (v : ι → Fin n → ℂ) :
    (M.updateRow i (∑ w ∈ s, c w • v w)).det = ∑ w ∈ s, c w * (M.updateRow i (v w)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [Matrix.updateRow_self])
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.det_updateRow_add,
      Matrix.det_updateRow_smul, ih]

/- English proof (translation)
Establish `h1 : Matrix.of X = (Matrix.of X).updateRow i (∑ w, η w • v w)`. Use extensionality with `a l`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality. Simplify using `[Matrix.updateRow_self, hrow, Finset.sum_apply]`.

Simplify using `[Matrix.updateRow_ne h]`. Establish `h2 : ∀ w, (Matrix.of fun a l => if a = i then v w l else X a l) = (Matrix.of X).updateRow i (v w)`. Introduce `w`. Use extensionality with `a l`. Distinguish the cases in `h : a = i`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Matrix.updateRow_ne h]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem det_row_lin {n : ℕ} {ι : Type} [Fintype ι] (X : Fin n → Fin n → ℂ) (i : Fin n) (η : ι → ℂ)
    (v : ι → Fin n → ℂ) (hrow : ∀ l, X i l = ∑ w, η w * v w l) :
    (Matrix.of X).det = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det := by
  have h1 : Matrix.of X = (Matrix.of X).updateRow i (∑ w, η w • v w) := by
    ext a l
    by_cases h : a = i
    · subst h
      simp [Matrix.updateRow_self, hrow, Finset.sum_apply]
    · simp [Matrix.updateRow_ne h]
  have h2 : ∀ w, (Matrix.of fun a l => if a = i then v w l else X a l) =
      (Matrix.of X).updateRow i (v w) := by
    intro w
    ext a l
    by_cases h : a = i
    · subst h
      simp
    · simp [h, Matrix.updateRow_ne h]
  calc (Matrix.of X).det = ((Matrix.of X).updateRow i (∑ w ∈ Finset.univ, η w • v w)).det :=
        congrArg Matrix.det h1
    _ = ∑ w ∈ Finset.univ, η w * ((Matrix.of X).updateRow i (v w)).det := det_row_sum _ _ _ _ _
    _ = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det :=
        Finset.sum_congr rfl (fun w _ => by rw [h2 w])

/- English proof (translation)
Repeatedly rewrite using `[Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Use `split_ifs with hP`. Rewrite using `[det_row_lin (fun a l => X a (c l)) i η (fun w l => v w (c l)) (fun l => hrow (c l)), Finset.sum_smul]`.

Conclude with `Finset.sum_congr rfl (fun w _ => mul_smul _ _ _)`. Simplify using the standard rewrite rules.
-/
theorem sum_lin {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} {ι : Type} [Fintype ι]
    (P : (Fin m → Fin N) → Prop) [DecidablePred P] (X : Fin m → Fin N → ℂ) (i : Fin m) (η : ι → ℂ)
    (v : ι → Fin N → ℂ) (hrow : ∀ p, X i p = ∑ w, η w * v w p) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      ∑ w, η w • ∑ c : Fin m → Fin N,
        if P c then (Matrix.of fun a l => (if a = i then v w (c l) else X a (c l))).det • F c else 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hP
  · rw [det_row_lin (fun a l => X a (c l)) i η (fun w l => v w (c l)) (fun l => hrow (c l)),
      Finset.sum_smul]
    exact Finset.sum_congr rfl (fun w _ => mul_smul _ _ _)
  · simp

/- English proof (translation)
Introduce `a b hab`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact absurd hab (lt_irrefl _)`.

Consider the case `cast a`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`. Conclude with `hx a`. Consider the case `cast b`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)`. Consider the case `cast a`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `hf (Fin.castSucc_lt_castSucc_iff.1 hab)`.
-/
theorem strictMono_snoc {α : Type} [Preorder α] {m : ℕ} (f : Fin m → α) (hf : StrictMono f) (x : α)
    (hx : ∀ l, f l < x) : StrictMono (Fin.snoc (α := fun _ => α) f x : Fin (m + 1) → α) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast a =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)
    | cast a =>
      simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hab)

/- English proof (translation)
Unfold `Hpk`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_zero_alt (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hq : r ≤ q.val ∧ q.val ≤ r + k)
    (hp : ¬ (r ≤ p.val ∧ p.val ≤ r + k)) : Hpk k r q p = 0 := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `inWb at hyb`. Unfold `herm bvec wI`. Distinguish the cases in `hp : r ≤ (p : ℕ) ∧ (p : ℕ) ≤ r + k`. Rewrite using `[Finset.sum_eq_single (⟨(p : ℕ) - r, by omega⟩ : Fin (k + 1))]`. Use `split_ifs with h`.

Rewrite using `[mul_one, ← h]`. Conclude with `absurd (Fin.ext (by simp only [Fin.val_mk]; omega)) h`. Introduce `b _ hb split_ifs with h`. Conclude with `absurd (Fin.ext (by simp only [Fin.ext_iff, Fin.val_mk] at h ⊢; omega)) hb`. Conclude with `mul_zero _`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hL : star yb ⬝ᵥ Hpk k r *ᵥ Pi.single p 1 = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`.

Distinguish the cases in `hi : r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k`. Establish `h0 : (Hpk k r *ᵥ Pi.single p 1) i = 0`. Simplify using `[Matrix.mulVec, hpk_zero_alt k r p i hi hp]`. Rewrite using `[h0, mul_zero]`. Establish `h0 : yb i = 0` using `hyb i (by omega)`.

Simplify using `[h0]`. Rewrite using `[hL]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `w _`.

Use `split_ifs with h`. Establish `hw` using `w.isLt`. Rewrite `h` using `[Fin.ext_iff]`. Simplify using `only [Fin.val_mk] at h`. Conclude with `absurd ⟨by omega, by omega⟩ hp`.

Conclude with `mul_zero _`.
-/
theorem herm_bvec_sum (k r : ℕ) (yb : Fin (2 * r + k + 1) → ℂ) (hyb : inWb k r yb) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec p) yb =
      ∑ w : Fin (k + 1), herm (Hpk k r) (bvec (wI k r w)) yb * (if p = wI k r w then 1 else 0) := by
  unfold inWb at hyb
  unfold herm bvec wI
  by_cases hp : r ≤ (p : ℕ) ∧ (p : ℕ) ≤ r + k
  · rw [Finset.sum_eq_single (⟨(p : ℕ) - r, by omega⟩ : Fin (k + 1))]
    · split_ifs with h
      · rw [mul_one, ← h]
      · exact absurd (Fin.ext (by simp only [Fin.val_mk]; omega)) h
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (by simp only [Fin.ext_iff, Fin.val_mk] at h ⊢; omega)) hb
      · exact mul_zero _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hL : star yb ⬝ᵥ Hpk k r *ᵥ Pi.single p 1 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k
      · have h0 : (Hpk k r *ᵥ Pi.single p 1) i = 0 := by
          simp [Matrix.mulVec, hpk_zero_alt k r p i hi hp]
        rw [h0, mul_zero]
      · have h0 : yb i = 0 := hyb i (by omega)
        simp [h0]
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro w _
    split_ifs with h
    · have hw := w.isLt
      rw [Fin.ext_iff] at h
      simp only [Fin.val_mk] at h
      exact absurd ⟨by omega, by omega⟩ hp
    · exact mul_zero _

/- English proof (translation)
Unfold `Hpk`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hpk_real (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r p q := by
  unfold Hpk
  split_ifs <;> simp

/- English proof (translation)
Unfold `Hpk`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_symm (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Hpk k r p q = Hpk k r q p := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[hpk_real, hpk_symm]`.
-/
theorem hpk_star (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r q p := by
  rw [hpk_real, hpk_symm]

/- English proof (translation)
Unfold `herm`. Establish `hH : (Hpk k r)ᴴ = Hpk k r`. Use extensionality with `p q`. Rewrite using `[conjTranspose_apply, hpk_star]`. Rewrite using `[star_dotProduct v (Hpk k r *ᵥ w), star_star, star_mulVec, hH, dotProduct_mulVec]`.
-/
theorem herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext p q
    rw [conjTranspose_apply, hpk_star]
  rw [star_dotProduct v (Hpk k r *ᵥ w), star_star, star_mulVec, hH, dotProduct_mulVec]

end Formalism.FourierDecayAlt.P.SignAntidiagonal
