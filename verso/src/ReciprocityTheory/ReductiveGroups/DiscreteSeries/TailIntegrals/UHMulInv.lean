import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem herm_add_l (u v w : ι → ℂ) : herm H (u + v) w = herm H u w + herm H v w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[herm, add_dotProduct]`.
-/
theorem herm_add_r (u v w : ι → ℂ) : herm H u (v + w) = herm H u v + herm H u w := by
  simp [herm, add_dotProduct]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_sub, dotProduct_sub]`.
-/
theorem herm_sub_l (u v w : ι → ℂ) : herm H (u - v) w = herm H u w - herm H v w := by
  simp [herm, Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Simplify using `[herm, sub_dotProduct]`.
-/
theorem herm_sub_r (u v w : ι → ℂ) : herm H u (v - w) = herm H u v - herm H u w := by
  simp [herm, sub_dotProduct]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_smul, dotProduct_smul]`.
-/
theorem herm_smul_l (a : ℂ) (u w : ι → ℂ) : herm H (a • u) w = a * herm H u w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[herm, star_smul, smul_dotProduct]`.
-/
theorem herm_smul_r (a : ℂ) (u w : ι → ℂ) : herm H u (a • w) = star a * herm H u w := by
  simp [herm, star_smul, smul_dotProduct]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_l (w : ι → ℂ) : herm H 0 w = 0 := by simp [herm]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_r (u : ι → ℂ) : herm H u 0 = 0 := by simp [herm]

/- English proof (translation)
Establish `hg' : gᴴ * H * g = H` using `hg`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']`.
-/
theorem herm_UH [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

/- English proof (translation)
Use extensionality with `i j`. Simplify `congrFun (h (Pi.single j 1)) i` using `[Matrix.mulVec_single_one]`.
-/
theorem mat_eq_of_mulVec [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

end herm

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
The claim follows from `mat_eq_of_mulVec fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]`.
-/
theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Use extensionality with `i j`. Break down `i with ⟨i, hi⟩` into its components or cases. Break down `j with ⟨j, hj⟩` into its components or cases. Simplify using `only [conjTranspose_apply, Hpk, Fin.mk.injEq]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`.
-/
theorem Hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [conjTranspose_apply, Hpk, Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (UH_left_inv k r hg)`.
-/
theorem UH_inv {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (UH_left_inv k r hg)

/- English proof (translation)
Rewrite using `[UH_inv k r hg, UH_left_inv k r hg]`.
-/
theorem UH_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  rw [UH_inv k r hg, UH_left_inv k r hg]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.mp (UH_inv_mul k r hg)`.
-/
theorem UH_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  mul_eq_one_comm.mp (UH_inv_mul k r hg)

end hpk

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
