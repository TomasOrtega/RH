import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/- English proof (translation)
Rewrite using `[frobenius_norm_def, gN, Real.sqrt_eq_rpow]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_norm_sq, Real.rpow_two]`.
-/
theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  rw [frobenius_norm_def, gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

/- English proof (translation)
Rewrite using `[gN_eq_frob, gN_eq_frob, gN_eq_frob]`. Conclude with `frobenius_norm_mul A B`.
-/
theorem gN_mul_le {k r : ℕ} (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

/- English proof (translation)
Rewrite using `[gN_eq_frob, gN_eq_frob, frobenius_norm_conjTranspose]`.
-/
theorem gN_conjTranspose {k r : ℕ} (A : Mat k r) : gN Aᴴ = gN A := by
  rw [gN_eq_frob, gN_eq_frob, frobenius_norm_conjTranspose]

end frob

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem gN_nonneg {k r : ℕ} (A : Mat k r) : 0 ≤ gN A := Real.sqrt_nonneg _

section hpk
variable (k r : ℕ)

/- English proof (translation)
Break down `i with ⟨i, hi⟩` into its components or cases. Break down `j with ⟨j, hj⟩` into its components or cases. Simplify using `only [Hpk, Fin.mk.injEq] at h ⊢`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Break down `i with ⟨i, hi⟩` into its components or cases. Break down `j with ⟨j, hj⟩` into its components or cases. Simplify using `only [Hpk, Fin.mk.injEq] at h ⊢`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h1]`. Simplify using `only [Hpk_out k r h1]`. Rewrite using `[Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg (fun h => hb (Fin.ext h))]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h1]`. Simplify using `only [Hpk_mid k r h1]`. Rewrite using `[Finset.sum_eq_single i]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`. Introduce `b _ hb`.

Rewrite using `[if_neg (fun h => hb (Fin.ext h))]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Hpk_mulVec]`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h1, Hpk_mulVec]`. Establish `e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val` using `rfl`.

Rewrite using `[if_pos (by rw [e1]; omega)]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Apply the tactic sequence `rw [if_neg h1, Hpk_mulVec, if_neg h1] split_ifs <;> simp`.
-/
theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify `congrFun (h (Pi.single j 1)) i` using `[Matrix.mulVec_single_one]`.
-/
theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

/- English proof (translation)
The claim follows from `mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]`.
-/
theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hx' : xᴴ * Hpk k r * x = Hpk k r` using `hx`. Use `show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GV_mul {g x : Mat k r} (hg : g ∈ GV k r) (hx : x ∈ GV k r) : g * x ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

end hpk

/- English proof (translation)
Establish `hx : x = Hpk k r * gᴴ * Hpk k r * (g * x)`. Rewrite using `[← Matrix.mul_assoc, UH_left_inv k r hg, Matrix.one_mul]`. Establish `h0` using `gN_nonneg (Hpk k r)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `gN_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by ring`.
-/
theorem gN_le_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) (x : Mat k r) :
    gN x ≤ gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by
  have hx : x = Hpk k r * gᴴ * Hpk k r * (g * x) := by
    rw [← Matrix.mul_assoc, UH_left_inv k r hg, Matrix.one_mul]
  have h0 := gN_nonneg (Hpk k r)
  calc gN x = gN (Hpk k r * gᴴ * Hpk k r * (g * x)) := by rw [← hx]
    _ ≤ gN (Hpk k r * gᴴ * Hpk k r) * gN (g * x) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN g * gN (Hpk k r) * gN (g * x) := by
        gcongr
        · exact gN_nonneg _
        · calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
            _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) := by gcongr; exact gN_mul_le _ _
            _ = gN (Hpk k r) * gN g * gN (Hpk k r) := by rw [gN_conjTranspose]
    _ = gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by ring

/- English proof (translation)
Establish `hA0 : 0 < A` using `by linarith`. Establish `hB0 : 0 < B` using `by linarith`. Establish `hP : 0 < B * A` using `mul_pos hB0 hA0`. Establish `e1 : A ^ (-a) * B ^ (-a) = (B * A) ^ (-(a - b)) * (B * A) ^ (-b)`. Rewrite using `[← Real.rpow_add hP, Real.mul_rpow hB0.le hA0.le, mul_comm]`.

Put the polynomial expressions in normal form. Rewrite using `[e1]`. Establish `hXc : 0 < X * c⁻¹` using `mul_pos hX (inv_pos.2 hc)`. Establish `h1 : (B * A) ^ (-(a - b)) ≤ (X * c⁻¹) ^ (-(a - b))`. Use `Real.rpow_le_rpow_of_nonpos hXc ?_ (by linarith)` and prove the remaining obligations.

Rewrite using `[mul_inv_le_iff₀ hc]`. Combine the linear relations using `[hXle]`. Establish `h2 : (B * A) ^ (-b) ≤ B ^ (-b)` using `Real.rpow_le_rpow_of_nonpos hB0 (by nlinarith) (by linarith)`. Conclude with `mul_le_mul h1 h2 (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hXc.le _)`.
-/
theorem real_key {A B X c a b : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hX : 0 < X) (hc : 0 < c) (hb : 0 ≤ b)
    (hab : b ≤ a) (hXle : X ≤ c * (B * A)) :
    A ^ (-a) * B ^ (-a) ≤ (X * c⁻¹) ^ (-(a - b)) * B ^ (-b) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP : 0 < B * A := mul_pos hB0 hA0
  have e1 : A ^ (-a) * B ^ (-a) = (B * A) ^ (-(a - b)) * (B * A) ^ (-b) := by
    rw [← Real.rpow_add hP, Real.mul_rpow hB0.le hA0.le, mul_comm]; ring_nf
  rw [e1]
  have hXc : 0 < X * c⁻¹ := mul_pos hX (inv_pos.2 hc)
  have h1 : (B * A) ^ (-(a - b)) ≤ (X * c⁻¹) ^ (-(a - b)) := by
    refine Real.rpow_le_rpow_of_nonpos hXc ?_ (by linarith)
    rw [mul_inv_le_iff₀ hc]; linarith [hXle]
  have h2 : (B * A) ^ (-b) ≤ B ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hB0 (by nlinarith) (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hXc.le _)

/- English proof (translation)
Simplify using `only [AB, AG, nR]`. Use `push_cast`. Use polynomial arithmetic with `[sq_nonneg ((k : ℝ) + r - (r + 1)), (Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]`.
-/
theorem AB_le_AG (k r : ℕ) : AB k r ≤ AG k r + 1 := by
  simp only [AB, AG, nR]
  push_cast
  nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1)), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities
