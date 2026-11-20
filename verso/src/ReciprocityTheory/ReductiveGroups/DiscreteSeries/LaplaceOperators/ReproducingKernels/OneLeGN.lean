import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecA

open Formalism.QuantumDeterminants

def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

/- English proof (translation)
Unfold `Hpk sg`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h1]`. Break down `h1 with h1 | h1` into its components or cases. Distinguish the cases in `h2 : i.val + j.val = 2 * r + k`.

Rewrite using `[if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]`. Rewrite using `[if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]`. Distinguish the cases in `h2 : i.val + j.val = 2 * r + k`. Rewrite using `[if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]`. Rewrite using `[if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]`.

Rewrite `h1` using `[if_neg h1] push Not`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Distinguish the cases in `h2 : i = j`. Substitute `h2` using the available equality. Rewrite using `[if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]`.

Rewrite using `[if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]`.
-/
theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  unfold Hpk sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i = j
    · subst h2; rw [if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]

/- English proof (translation)
Rewrite using `[hpk_apply, hpk_apply]`. Unfold `sg`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[conjTranspose_apply, hpk_symm, hpk_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hpk_conjT (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hpk_symm, hpk_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> omega`.
-/
theorem sg_lt {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i < 2 * r + k + 1 := by
  unfold sg; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> omega`.
-/
theorem sg_sg {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r (sg k r i) = i := by
  unfold sg; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> omega`.
-/
theorem sg_rk {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i = r + k ↔ i = r + k := by
  unfold sg; split_ifs <;> omega

/- English proof (translation)
The claim follows from `hpk_apply k r ⟨i, hi⟩ j`.
-/
theorem hpk_apply' (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]`. Rewrite using `[hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply, if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]`. Establish `hs` using `sg_rk (k := k) (r := r) i.2`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Distinguish the cases in `h : i.val = r + k`. Rewrite using `[if_pos h, if_pos (hs.2 h)]`. Evaluate the numerical expressions.

Rewrite using `[if_neg h, if_neg (fun h' => h (hs.1 h'))]`. Evaluate the numerical expressions. Rewrite using `[if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]`. Introduce `b _ hb`. Rewrite using `[hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hpk_mul (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]
  · rw [hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply,
      if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]
    have hs := sg_rk (k := k) (r := r) i.2
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      by_cases h : i.val = r + k
      · rw [if_pos h, if_pos (hs.2 h)]; norm_num
      · rw [if_neg h, if_neg (fun h' => h (hs.1 h'))]; norm_num
    · rw [if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]
  · intro b _ hb; rw [hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hx' : xᴴ * Hpk k r * x = Hpk k r` using `hx`. Use `show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hg', hx']`.
-/
theorem mul_mem {k r : ℕ} {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg', hx']

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_eq {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine Matrix.inv_eq_left_inv ?_
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_mul]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Rewrite using `[inv_eq hg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [inv_eq hg]
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_mul]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.mp (inv_mul hg)`.
-/
theorem mul_inv {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 :=
  mul_eq_one_comm.mp (inv_mul hg)

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h1 : g * g⁻¹ = 1` using `mul_inv hg`. Use `show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h1]; simp`.
-/
theorem inv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := mul_inv hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

/- English proof (translation)
Simplify using `only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gN_sq {k r : ℕ} (g : Mat k r) : (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.gN`. Rewrite using `[gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]`.
-/
theorem gN_left {k r : ℕ} {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) :
    Formalism.FourierDecayAlt.B.gN (κ * g) = Formalism.FourierDecayAlt.B.gN g := by
  unfold Formalism.FourierDecayAlt.B.gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

/- English proof (translation)
Establish `hκ' : κ * κᴴ = 1` using `mul_eq_one_comm.mp hκ`. Unfold `Formalism.FourierDecayAlt.B.gN`. Rewrite using `[gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]`.
-/
theorem gN_right {k r : ℕ} {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) :
    Formalism.FourierDecayAlt.B.gN (g * κ) = Formalism.FourierDecayAlt.B.gN g := by
  have hκ' : κ * κᴴ = 1 := mul_eq_one_comm.mp hκ
  unfold Formalism.FourierDecayAlt.B.gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hκ', Matrix.mul_one]

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.gN`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[conjTranspose_apply, Complex.star_def, Complex.normSq_conj]`.
-/
theorem gN_conjT {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN gᴴ = Formalism.FourierDecayAlt.B.gN g := by
  unfold Formalism.FourierDecayAlt.B.gN
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.normSq_conj]

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.gN`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (g i j)), ← Complex.normSq_eq_norm_sq]`. Use `Real.sqrt_le_sqrt ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gN_entry {k r : ℕ} (g : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ Formalism.FourierDecayAlt.B.gN g := by
  unfold Formalism.FourierDecayAlt.B.gN
  rw [← Real.sqrt_sq (norm_nonneg (g i j)), ← Complex.normSq_eq_norm_sq]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

section frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/- English proof (translation)
Rewrite using `[Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_norm_sq, Real.rpow_two]`.
-/
theorem gN_eq_norm {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

/- English proof (translation)
Rewrite using `[gN_eq_norm, gN_eq_norm, gN_eq_norm]`. Conclude with `Matrix.frobenius_norm_mul a b`.
-/
theorem gN_mul_le' {k r : ℕ} (a b : Mat k r) :
    Formalism.FourierDecayAlt.B.gN (a * b) ≤ Formalism.FourierDecayAlt.B.gN a * Formalism.FourierDecayAlt.B.gN b := by
  rw [gN_eq_norm, gN_eq_norm, gN_eq_norm]
  exact Matrix.frobenius_norm_mul a b

end frob

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ * Hpk k r = 1` using `by rw [hpk_conjT, hpk_mul]`. Rewrite using `[inv_eq hg, gN_right _ hH, gN_left _ hH, gN_conjT]`.
-/
theorem gN_inv' {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : Formalism.FourierDecayAlt.B.gN g⁻¹ = Formalism.FourierDecayAlt.B.gN g := by
  have hH : (Hpk k r)ᴴ * Hpk k r = 1 := by rw [hpk_conjT, hpk_mul]
  rw [inv_eq hg, gN_right _ hH, gN_left _ hH, gN_conjT]

/- English proof (translation)
Establish `h0 : (1 : ℝ) ≤ Formalism.FourierDecayAlt.B.gN (1 : Mat k r)`. Apply the tactic sequence `have := gN_entry (1 : Mat k r) ⟨0, by omega⟩ ⟨0, by omega⟩`. Simplify using `using this`. Establish `h1 : Formalism.FourierDecayAlt.B.gN (1 : Mat k r) ≤ Formalism.FourierDecayAlt.B.gN g * Formalism.FourierDecayAlt.B.gN g`. Use `gN_mul_le' g g⁻¹` as an intermediate fact.

Rewrite `this` using `[mul_inv hg, gN_inv' hg]`. Then use the resulting hypothesis. Use polynomial arithmetic with `[gN_nonneg g]`.
-/
theorem one_le_gN' {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g := by
  have h0 : (1 : ℝ) ≤ Formalism.FourierDecayAlt.B.gN (1 : Mat k r) := by
    have := gN_entry (1 : Mat k r) ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa using this
  have h1 : Formalism.FourierDecayAlt.B.gN (1 : Mat k r) ≤ Formalism.FourierDecayAlt.B.gN g * Formalism.FourierDecayAlt.B.gN g := by
    have := gN_mul_le' g g⁻¹
    rwa [mul_inv hg, gN_inv' hg] at this
  nlinarith [gN_nonneg g]

/- English proof (translation)
Use `gN_mul_le' (y * g) g⁻¹` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, mul_inv hg, Matrix.mul_one, gN_inv' hg]`. Then use the resulting hypothesis.
-/
theorem gN_le_mul {k r : ℕ} {y g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.gN y ≤ Formalism.FourierDecayAlt.B.gN (y * g) * Formalism.FourierDecayAlt.B.gN g := by
  have := gN_mul_le' (y * g) g⁻¹
  rwa [Matrix.mul_assoc, mul_inv hg, Matrix.mul_one, gN_inv' hg] at this

/- English proof (translation)
Establish `hB0 : 0 ≤ B` using `by linarith`. Establish `hA1 : A ^ (-a) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith)`. Establish `hBpos : 0 ≤ B ^ (-a)` using `Real.rpow_nonneg hB0 _`. Establish `hYBB : Y ≤ B ^ (2 : ℝ)`. Rewrite using `[Real.rpow_two]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : B ^ (-(a / 2)) ≤ Y ^ (-(a / 4))`. Use `Real.rpow_le_rpow_of_nonpos hY hYBB (show -(a / 4) ≤ 0 by linarith)` as an intermediate fact. Rewrite `this` using `[← Real.rpow_mul hB0, show (2 : ℝ) * -(a / 4) = -(a / 2) by ring]`. Then use the resulting hypothesis. Establish `h3 : B ^ (-a) = B ^ (-(a / 2)) * B ^ (-(a / 2))`.

Rewrite using `[← Real.rpow_add (by linarith)]; ring_nf`. Establish `hBh : 0 ≤ B ^ (-(a / 2))` using `Real.rpow_nonneg hB0 _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pb_real (a A B Y : ℝ) (ha : 0 ≤ a) (hA : 1 ≤ A) (hB : 1 ≤ B) (hY : 0 < Y) (hYB : Y ≤ B * A)
    (hAB : A ≤ B) : A ^ (-a) * B ^ (-a) ≤ Y ^ (-(a / 4)) * B ^ (-(a / 2)) := by
  have hB0 : 0 ≤ B := by linarith
  have hA1 : A ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith)
  have hBpos : 0 ≤ B ^ (-a) := Real.rpow_nonneg hB0 _
  have hYBB : Y ≤ B ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  have h2 : B ^ (-(a / 2)) ≤ Y ^ (-(a / 4)) := by
    have := Real.rpow_le_rpow_of_nonpos hY hYBB (show -(a / 4) ≤ 0 by linarith)
    rwa [← Real.rpow_mul hB0, show (2 : ℝ) * -(a / 4) = -(a / 2) by ring] at this
  have h3 : B ^ (-a) = B ^ (-(a / 2)) * B ^ (-(a / 2)) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hBh : 0 ≤ B ^ (-(a / 2)) := Real.rpow_nonneg hB0 _
  calc A ^ (-a) * B ^ (-a) ≤ 1 * B ^ (-a) := mul_le_mul_of_nonneg_right hA1 hBpos
    _ = B ^ (-(a / 2)) * B ^ (-(a / 2)) := by rw [one_mul, h3]
    _ ≤ Y ^ (-(a / 4)) * B ^ (-(a / 2)) := mul_le_mul_of_nonneg_right h2 hBh

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecA
