import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ}

def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Unfold `piI`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
lemma piI_val (i : Fin (2 * r + k + 1)) :
    (piI k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold piI
  split_ifs <;> rfl

/- English proof (translation)
Establish `hi` using `i.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[piI_val, piI_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
lemma piI_piI (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [piI_val, piI_val]
  split_ifs <;> omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Unfold `epsI`. Rewrite using `[piI_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
lemma epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have hi := i.isLt
  unfold epsI
  rw [piI_val]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Unfold `epsI`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma epsI_mul_self (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by
  unfold epsI
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `epsI`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma star_epsI (i : Fin (2 * r + k + 1)) : star (epsI k r i) = epsI k r i := by
  unfold epsI
  split_ifs <;> simp

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, epsI, Fin.ext_iff, piI_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, epsI, Fin.ext_iff, piI_val]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Hpk_apply, ite_mul]`.
-/
lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = epsI k r i * X (piI k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply, ite_mul]

/- English proof (translation)
Establish `hc : ∀ l, (j = piI k r l) ↔ (l = piI k r j)` using `fun l => ⟨fun h => by rw [h, piI_piI], fun h => by rw [h, piI_piI]⟩`. Simplify using `only [Matrix.mul_apply, Hpk_apply, hc, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, epsI_piI]`.
-/
lemma mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  have hc : ∀ l, (j = piI k r l) ↔ (l = piI k r j) :=
    fun l => ⟨fun h => by rw [h, piI_piI], fun h => by rw [h, piI_piI]⟩
  simp only [Matrix.mul_apply, Hpk_apply, hc, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, epsI_piI]

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Hpk_apply, ite_mul]`.
-/
lemma Hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp [Matrix.mulVec, dotProduct, Hpk_apply, ite_mul]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[epsI_mul_self]`.

Simplify using `[h, Ne.symm h]`.
-/
lemma Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [epsI_mul_self]
  · simp [h, Ne.symm h]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]`. Distinguish the cases in `h : j = piI k r i`. Establish `h' : i = piI k r j` using `by rw [h, piI_piI]`. Rewrite using `[if_pos h', if_pos h, star_epsI, h, epsI_piI]`.

Establish `h' : ¬ i = piI k r j` using `fun h' => h (by rw [h', piI_piI])`. Rewrite using `[if_neg h', if_neg h, star_zero]`.
-/
lemma Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · have h' : i = piI k r j := by rw [h, piI_piI]
    rw [if_pos h', if_pos h, star_epsI, h, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Rewrite using `[show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by`. Simplify using `only [Matrix.mul_assoc], hg', Hpk_mul_self]`.
-/
lemma inv_mul_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by
    simp only [Matrix.mul_assoc], hg', Hpk_mul_self]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (inv_mul_UH hg)`.
-/
lemma inv_eq_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (inv_mul_UH hg)

/- English proof (translation)
Rewrite using `[inv_eq_UH hg]`. Conclude with `mul_eq_one_comm.mp (inv_mul_UH hg)`.
-/
lemma mul_inv_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := by
  rw [inv_eq_UH hg]
  exact mul_eq_one_comm.mp (inv_mul_UH hg)

/- English proof (translation)
Rewrite using `[inv_eq_UH hg]`. Conclude with `inv_mul_UH hg`.
-/
lemma inv_mul_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := by
  rw [inv_eq_UH hg]
  exact inv_mul_UH hg

/- English proof (translation)
Use `show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r`. Simplify using the standard rewrite rules.
-/
lemma one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [ha', hb']`.
-/
lemma mul_mem_UH {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `h1 : a * a⁻¹ = 1` using `mul_inv_UH ha`. Establish `h2 : (a⁻¹)ᴴ * aᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`. Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma inv_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : a * a⁻¹ = 1 := mul_inv_UH ha
  have h2 : (a⁻¹)ᴴ * aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[mul_Hpk_apply, Hpk_mul_apply]`.
-/
lemma Hpk_mul_mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X * Hpk k r) i j = epsI k r i * X (piI k r i) (piI k r j) * epsI k r j := by
  rw [mul_Hpk_apply, Hpk_mul_apply]

end PI.QuotSetU.UnitaryGroupMassFormula.SW
