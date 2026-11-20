import Formalism.PeriodIntegrals.IsLowUnitH

open Matrix

noncomputable section

namespace PI.HwUniqW

open PI.UpqRep

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
Apply `Fin.ext` to reduce the goal to its premises. Use `i.isLt` as an intermediate fact. Simplify using `only [piI_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
lemma piI_piI (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [piI_val]
  split_ifs <;> omega

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Simplify using `only [epsI, piI_val]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
lemma epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have := i.isLt
  simp only [epsI, piI_val]
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
Establish `hj : j = piI k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val)`. Rewrite using `[Fin.ext_iff, piI_val]`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact. Unfold `Hpk epsI`.

Simplify using `only [hj, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | norm_num`.
-/
lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hj : j = piI k r i ↔
      j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [Fin.ext_iff, piI_val]
  have := i.isLt
  have := j.isLt
  unfold Hpk epsI
  simp only [hj, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | norm_num

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single (piI k r i)]`. Rewrite using `[Hpk_apply, if_pos rfl]`. Introduce `l hl`. Rewrite using `[Hpk_apply, if_neg hl, zero_mul]`.
-/
lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = epsI k r i * X (piI k r i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (piI k r i)]
  · rw [Hpk_apply, if_pos rfl]
  · intro l hl
    rw [Hpk_apply, if_neg hl, zero_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_single (piI k r j)]`. Rewrite using `[Hpk_apply, if_pos (piI_piI j).symm, epsI_piI]`. Introduce `l hl`. Rewrite using `[Hpk_apply, if_neg, mul_zero]`. Introduce `h`.

Apply `hl` to reduce the goal to its premises. Rewrite using `[h, piI_piI]`.
-/
lemma mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (piI k r j)]
  · rw [Hpk_apply, if_pos (piI_piI j).symm, epsI_piI]
  · intro l hl
    rw [Hpk_apply, if_neg, mul_zero]
    intro h
    apply hl
    rw [h, piI_piI]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Fintype.sum_eq_single (piI k r i)]`. Rewrite using `[Hpk_apply, if_pos rfl]`. Introduce `l hl`. Rewrite using `[Hpk_apply, if_neg hl, zero_mul]`.
-/
lemma Hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (piI k r i)]
  · rw [Hpk_apply, if_pos rfl]
  · intro l hl
    rw [Hpk_apply, if_neg hl, zero_mul]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[epsI_mul_self]`.

Simplify using `[h, Ne.symm h]`.
-/
lemma Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [epsI_mul_self]
  · simp [h, Ne.symm h]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]`. Distinguish the cases in `h : j = piI k r i`. Substitute `h` using the available equality. Rewrite using `[piI_piI, if_pos rfl, if_pos rfl, star_epsI, epsI_piI]`.

Establish `h' : ¬ i = piI k r j` using `fun h' => h (by rw [h', piI_piI])`. Rewrite using `[if_neg h', if_neg h, star_zero]`.
-/
lemma Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · subst h
    rw [piI_piI, if_pos rfl, if_pos rfl, star_epsI, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]

/- English proof (translation)
Establish `h : gᴴ * (Hpk k r * g) = Hpk k r`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `hg`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h, Hpk_mul_self]`.
-/
lemma inv_mul_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have h : gᴴ * (Hpk k r * g) = Hpk k r := by
    rw [← Matrix.mul_assoc]
    exact hg
  simp only [Matrix.mul_assoc]
  rw [h, Hpk_mul_self]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (inv_mul_UH hg)`.
-/
lemma inv_eq_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (inv_mul_UH hg)

/- English proof (translation)
Conclude with `Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_UH hg))`.
-/
lemma mul_inv_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_UH hg))

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
Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [ha', hb']`.
-/
lemma mul_mem_UH {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Establish `hh : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Hpk k r * (Hpk k r * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, Hpk_mul_self, Matrix.one_mul]`. Establish `h1 : a * (Hpk k r * aᴴ * Hpk k r) = 1`. Rewrite using `[← inv_eq_UH ha]`.

Conclude with `mul_inv_UH ha`. Establish `h2 : a * Hpk k r * aᴴ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Hpk_mul_self, Matrix.mul_one]`. Use `_ = Hpk k r := by rw [h1, Matrix.one_mul]`.

Establish `e : (a⁻¹)ᴴ = Hpk k r * a * Hpk k r`. Rewrite using `[inv_eq_UH ha]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[e, inv_eq_UH ha]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma inv_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  have hh : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Hpk_mul_self, Matrix.one_mul]
  have h1 : a * (Hpk k r * aᴴ * Hpk k r) = 1 := by
    rw [← inv_eq_UH ha]
    exact mul_inv_UH ha
  have h2 : a * Hpk k r * aᴴ = Hpk k r := by
    calc a * Hpk k r * aᴴ = a * (Hpk k r * aᴴ * Hpk k r) * Hpk k r := by
          simp only [Matrix.mul_assoc, Hpk_mul_self, Matrix.mul_one]
      _ = Hpk k r := by rw [h1, Matrix.one_mul]
  have e : (a⁻¹)ᴴ = Hpk k r * a * Hpk k r := by
    rw [inv_eq_UH ha]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose,
      Matrix.mul_assoc]
  rw [e, inv_eq_UH ha]
  calc Hpk k r * a * Hpk k r * Hpk k r * (Hpk k r * aᴴ * Hpk k r)
      = Hpk k r * (a * Hpk k r * aᴴ) * Hpk k r := by simp only [Matrix.mul_assoc, hh]
    _ = Hpk k r := by rw [h2, Hpk_mul_self, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[mul_Hpk_apply, Hpk_mul_apply]`.
-/
lemma Hpk_mul_mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X * Hpk k r) i j = epsI k r i * X (piI k r i) (piI k r j) * epsI k r j := by
  rw [mul_Hpk_apply, Hpk_mul_apply]

end PI.HwUniqW
