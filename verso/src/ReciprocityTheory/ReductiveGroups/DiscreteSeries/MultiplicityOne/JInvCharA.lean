import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h]`. Simplify using `only [mulVec, dotProduct, Hpk_out k r h]`. Establish `e : ∀ j : Fin (2 * r + k + 1), (if j.val = 2 * r + k - i.val then (1 : ℂ) else 0) * v j = if j = ⟨2 * r + k - i.val, by omega⟩ then v j else 0`. Introduce `j`.

Distinguish the cases in `hj : j.val = 2 * r + k - i.val`. Rewrite using `[if_pos hj, if_pos (Fin.ext hj), one_mul]`. Rewrite using `[if_neg hj, if_neg (fun e => hj (congrArg Fin.val e)), zero_mul]`. Simplify using `only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]`. Rewrite using `[if_neg h]`.

Simplify using `only [mulVec, dotProduct, Hpk_mid k r h]`. Establish `e : ∀ j : Fin (2 * r + k + 1), (if j.val = i.val then (if i.val = r + k then (-1 : ℂ) else 1) else 0) * v j = if j = i then (if i.val = r + k then (-1 : ℂ) else 1) * v j else 0`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun e => hj (Fin.ext e)), if_neg hj, zero_mul]`. Simplify using `only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [mulVec, dotProduct, Hpk_out k r h]
    have e : ∀ j : Fin (2 * r + k + 1), (if j.val = 2 * r + k - i.val then (1 : ℂ) else 0) * v j =
        if j = ⟨2 * r + k - i.val, by omega⟩ then v j else 0 := by
      intro j
      by_cases hj : j.val = 2 * r + k - i.val
      · rw [if_pos hj, if_pos (Fin.ext hj), one_mul]
      · rw [if_neg hj, if_neg (fun e => hj (congrArg Fin.val e)), zero_mul]
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · rw [if_neg h]
    simp only [mulVec, dotProduct, Hpk_mid k r h]
    have e : ∀ j : Fin (2 * r + k + 1),
        (if j.val = i.val then (if i.val = r + k then (-1 : ℂ) else 1) else 0) * v j =
        if j = i then (if i.val = r + k then (-1 : ℂ) else 1) * v j else 0 := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [if_neg (fun e => hj (Fin.ext e)), if_neg hj, zero_mul]
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hi` using `i.isLt`. Rewrite using `[Hpk_mulVec]`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Apply the tactic sequence `rw [if_pos h, Hpk_mulVec] split_ifs with h3 h4 all_goals first`.

Consider the case `(congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Use `show 2 * r + k - (2 * r + k - i.val) = i.val`. Use the proof step `omega)`. Consider the case `(exfalso`.

Establish `h3' : ¬(2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val)` using `h3`. Use the proof step `omega)`. Apply the tactic sequence `rw [if_neg h, Hpk_mulVec, if_neg h] split_ifs <;> simp`.
-/
theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [Hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Hpk_mulVec]
    split_ifs with h3 h4
    all_goals first
      | (congr 1
         apply Fin.ext
         show 2 * r + k - (2 * r + k - i.val) = i.val
         omega)
      | (exfalso
         have h3' : ¬(2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := h3
         omega)
  · rw [if_neg h, Hpk_mulVec, if_neg h]
    split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Establish `e` using `congrFun (h (Pi.single j 1)) i`. Simplify using `only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e`. Conclude with `e`.
-/
theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at e
  exact e

/- English proof (translation)
Conclude with `mat_eq_of_mulVec' k r (fun v => by rw [← mulVec_mulVec, Hpk_mulVec_mulVec, one_mulVec])`.
-/
theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  exact mat_eq_of_mulVec' k r (fun v => by rw [← mulVec_mulVec, Hpk_mulVec_mulVec, one_mulVec])

end hpk

section wb
variable {k r : ℕ}

def wbE (k r : ℕ) (v : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then v ⟨i.val - r, by omega⟩ else 0

end wb

section cc
variable {k r : ℕ}

def isW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

section cc

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

def cc (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  embWb k r γ *ᵥ (fun i => conj (((embWb k r γ)⁻¹ *ᵥ v) i))

variable {γ}
variable (hE : IsUnit (embWb k r γ).det)
include hE

/- English proof (translation)
Unfold `gbar`. Establish `h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1` using `nonsing_inv_mul _ hE`. Establish `h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1` using `mul_nonsing_inv _ hE`. Establish `h1' : ∀ X : Mat k r, (embWb k r γ)⁻¹ * (embWb k r γ * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Establish `h2' : ∀ X : Mat k r, embWb k r γ * ((embWb k r γ)⁻¹ * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`. Establish `hB : (embWb k r γ)⁻¹ * (g * g') * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * g' * embWb k r γ)`. Simplify using `only [Matrix.mul_assoc, h2']`. Rewrite using `[hB, Matrix.map_mul]`.

Simplify using `only [Matrix.mul_assoc, h1']`.
-/
theorem gbar_mul (g g' : Mat k r) : gbar k r γ (g * g') = gbar k r γ g * gbar k r γ g' := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1 := nonsing_inv_mul _ hE
  have h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1 := mul_nonsing_inv _ hE
  have h1' : ∀ X : Mat k r, (embWb k r γ)⁻¹ * (embWb k r γ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2' : ∀ X : Mat k r, embWb k r γ * ((embWb k r γ)⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hB : (embWb k r γ)⁻¹ * (g * g') * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * g' * embWb k r γ) := by
    simp only [Matrix.mul_assoc, h2']
  rw [hB, Matrix.map_mul]
  simp only [Matrix.mul_assoc, h1']

/- English proof (translation)
Unfold `gbar`. Establish `h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1` using `nonsing_inv_mul _ hE`. Establish `h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1` using `mul_nonsing_inv _ hE`. Establish `hm1 : (1 : Mat k r).map (starRingEnd ℂ) = 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Simplify using `only [Matrix.mul_one, h1, hm1, h2]`.
-/
theorem gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1 := nonsing_inv_mul _ hE
  have h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1 := mul_nonsing_inv _ hE
  have hm1 : (1 : Mat k r).map (starRingEnd ℂ) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [Matrix.mul_one, h1, hm1, h2]

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← gbar_mul hE, Matrix.mul_nonsing_inv _ hA, gbar_one hE]`.
-/
theorem gbar_inv (A : Mat k r) (hA : IsUnit A.det) : gbar k r γ A⁻¹ = (gbar k r γ A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← gbar_mul hE, Matrix.mul_nonsing_inv _ hA, gbar_one hE]

end cc

end cc

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr
