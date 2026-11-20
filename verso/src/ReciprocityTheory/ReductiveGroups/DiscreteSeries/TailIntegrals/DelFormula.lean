import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergDualBaseVectorFormula

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `only [bvec, Pi.star_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem star_bvec {n : ℕ} (p : Fin n) : star (bvec p) = bvec p := by
  funext q
  simp only [bvec, Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[bvec, dotProduct, Pi.single_apply]`.
-/
private theorem dotProduct_bvec {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : v ⬝ᵥ bvec p = v p := by
  simp [bvec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `[bvec, dotProduct, Pi.single_apply]`.
-/
private theorem bvec_dotProduct {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : bvec p ⬝ᵥ v = v p := by
  simp [bvec, dotProduct, Pi.single_apply]

/- English proof (translation)
Use `first`. Consider the case `(rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)`. Consider the case `simp [Complex.star_def]`. Consider the case `simp`.
-/
private theorem star_inv_sqrt_two' : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  first
    | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
    | simp [Complex.star_def]
    | simp

/- English proof (translation)
Establish `h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]`. Evaluate the numerical expressions. Establish `hne : (Real.sqrt 2 : ℂ) ≠ 0`. Introduce `h`.

Rewrite `h2` using `[h, zero_mul]`. Evaluate the numerical expressions using `at h2`. Rewrite using `[← h2]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    norm_num at h2
  rw [← h2]
  field_simp

/- English proof (translation)
Establish `hi` using `i.isLt`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]`. Establish `e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp`.

Rewrite using `[e, one_mul]`. Introduce `b _ hb`. Establish `hb' : b.val ≠ 2 * r + k - i.val` using `fun e => hb (Fin.ext e)`. Establish `hb2` using `b.isLt`. Establish `e : Hpk k r i b = 0`.

Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp`. Rewrite using `[e, zero_mul]`. Introduce `hm`. Conclude with `absurd (Finset.mem_univ _) hm`.
-/
private theorem Hpk_mulVec_apply_of_outer (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h : i.val < r ∨ r + k < i.val) : (Hpk k r *ᵥ y) i = y ⟨2 * r + k - i.val, by omega⟩ := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
  · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

/- English proof (translation)
Establish `hi` using `i.isLt`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Establish `e : Hpk k r i i = 1`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp`.

Rewrite using `[e, one_mul]`. Introduce `b _ hb`. Establish `hb' : b.val ≠ i.val` using `fun e => hb (Fin.ext e)`. Establish `hb2` using `b.isLt`. Establish `e : Hpk k r i b = 0`.

Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp`. Rewrite using `[e, zero_mul]`. Introduce `hm`. Conclude with `absurd (Finset.mem_univ _) hm`.
-/
private theorem Hpk_mulVec_apply_of_mem_middle (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val < r + k) : (Hpk k r *ᵥ y) i = y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · have e : Hpk k r i i = 1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

/- English proof (translation)
Establish `hi` using `i.isLt`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Establish `e : Hpk k r i i = -1`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp`.

Rewrite using `[e, neg_one_mul]`. Introduce `b _ hb`. Establish `hb' : b.val ≠ i.val` using `fun e => hb (Fin.ext e)`. Establish `hb2` using `b.isLt`. Establish `e : Hpk k r i b = 0`.

Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp`. Rewrite using `[e, zero_mul]`. Introduce `hm`. Conclude with `absurd (Finset.mem_univ _) hm`.
-/
private theorem Hpk_mulVec_apply_of_val_eq_add (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h : i.val = r + k) : (Hpk k r *ᵥ y) i = -y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · have e : Hpk k r i i = -1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, neg_one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Rewrite using `[Matrix.conjTranspose_apply]`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff] <;> (try split_ifs) <;> first | (exfalso; omega) | simp`.
-/
private theorem Hpk_conjTranspose_eq_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.conjTranspose_apply]
  simp only [Hpk, Fin.ext_iff] <;> (try split_ifs) <;> first | (exfalso; omega) | simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hi` using `i.isLt`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[Hpk_mulVec_apply_of_outer k r _ i h1, Hpk_mulVec_apply_of_outer k r y (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)) (by simp only [Fin.val_mk]; omega)]`. Use `congr 1`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h2 : i.val = r + k`. Rewrite using `[Hpk_mulVec_apply_of_val_eq_add k r _ i h2, Hpk_mulVec_apply_of_val_eq_add k r y i h2, neg_neg]`.

Rewrite using `[Hpk_mulVec_apply_of_mem_middle k r _ i (by omega) (by omega), Hpk_mulVec_apply_of_mem_middle k r y i (by omega) (by omega)]`.
-/
private theorem Hpk_mulVec_Hpk_mulVec (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ y) = y := by
  funext i
  have hi := i.isLt
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [Hpk_mulVec_apply_of_outer k r _ i h1, Hpk_mulVec_apply_of_outer k r y (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)) (by simp only [Fin.val_mk]; omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  · by_cases h2 : i.val = r + k
    · rw [Hpk_mulVec_apply_of_val_eq_add k r _ i h2, Hpk_mulVec_apply_of_val_eq_add k r y i h2, neg_neg]
    · rw [Hpk_mulVec_apply_of_mem_middle k r _ i (by omega) (by omega), Hpk_mulVec_apply_of_mem_middle k r y i (by omega) (by omega)]

/- English proof (translation)
Use `first`. Consider the case `simp [bvec, Pi.single_apply, Fin.ext_iff]`. Consider the case `(unfold bvec; rw [Pi.single_apply]; simp only [Fin.ext_iff])`. Consider the case `(by_cases h : q = p`. Substitute `h` using the available equality.

Simplify using `[bvec]`. Rewrite using `[if_neg (fun e => h (Fin.ext e))]`. Simplify using `[bvec, h])`.
-/
private theorem bvec_apply_eq_ite_val {n : ℕ} (p q : Fin n) : bvec p q = if q.val = p.val then 1 else 0 := by
  first
    | simp [bvec, Pi.single_apply, Fin.ext_iff]
    | (unfold bvec; rw [Pi.single_apply]; simp only [Fin.ext_iff])
    | (by_cases h : q = p
       · subst h; simp [bvec]
       · rw [if_neg (fun e => h (Fin.ext e))]; simp [bvec, h])

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem epsV_apply_eq (k r : ℕ) (q : Fin (2 * r + k + 1)) :
    epsV k r q = (Real.sqrt 2 : ℂ)⁻¹ * (bvec (wI k r 0) q + bvec (wI k r (Fin.last k)) q) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `hp` using `p.isLt`. Simplify using `only [phiV, liftVec, epsV_apply_eq, bvec_apply_eq_ite_val, esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> (try simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]) <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (simp_all; done) | omega`.
-/
theorem phiV_succ (k r' t : ℕ) (ht : t < r' + 1) (h : t + 1 < 1 + r' + 1) :
    phiV k (1 + r') ⟨t + 1, h⟩ = liftVec k 1 r' (phiV k r' ⟨t, ht⟩) := by
  funext p
  have hp := p.isLt
  simp only [phiV, liftVec, epsV_apply_eq, bvec_apply_eq_ite_val, esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]
  split_ifs <;> (try simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]) <;> (try split_ifs) <;>
    first | rfl | (exfalso; omega) | (simp_all; done) | omega

/- English proof (translation)
Unfold `phiV`. Apply the tactic sequence `by_cases hi : i.val < r <;> by_cases hj : j.val < r`. Rewrite using `[dif_pos hi, dif_pos hj, star_bvec, dotProduct_bvec]`. Simplify using `only [bvec_apply_eq_ite_val, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.

Rewrite using `[dif_pos hi, dif_neg hj, star_bvec, bvec_dotProduct, if_neg (fun (e : i = j) => hj (e ▸ hi))]`. Simplify using `only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`. Rewrite using `[dif_neg hi, dif_pos hj, dotProduct_bvec, if_neg (fun (e : i = j) => hi (e ▸ hj))]`. Simplify using `only [Pi.star_apply, epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]`.

Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`. Rewrite using `[dif_neg hi, dif_neg hj, if_pos (Fin.ext (by omega))]`. Establish `hv : (wI k r 0).val ≠ (wI k r (Fin.last k)).val`. Simplify using `only [wI, Fin.val_mk, Fin.val_zero, Fin.val_last]`. Use linear arithmetic over natural numbers and integers.

Unfold `epsV`. Rewrite using `[star_smul, star_add, star_bvec, star_bvec, star_inv_sqrt_two', smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, dotProduct_add]`. Simplify using `only [dotProduct_bvec, smul_eq_mul]`. Simplify using `only [bvec_apply_eq_ite_val, if_neg hv, if_neg (Ne.symm hv), eq_self_iff_true, if_true]`. Take the linear combination `inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one`.
-/
theorem ortho (k r : ℕ) (hk : 1 ≤ k) (i j : Fin (r + 1)) :
    star (phiV k r i) ⬝ᵥ phiV k r j = if i = j then 1 else 0 := by
  unfold phiV
  by_cases hi : i.val < r <;> by_cases hj : j.val < r
  · rw [dif_pos hi, dif_pos hj, star_bvec, dotProduct_bvec]
    simp only [bvec_apply_eq_ite_val, esI, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [dif_pos hi, dif_neg hj, star_bvec, bvec_dotProduct, if_neg (fun (e : i = j) => hj (e ▸ hi))]
    simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [dif_neg hi, dif_pos hj, dotProduct_bvec, if_neg (fun (e : i = j) => hi (e ▸ hj))]
    simp only [Pi.star_apply, epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [dif_neg hi, dif_neg hj, if_pos (Fin.ext (by omega))]
    have hv : (wI k r 0).val ≠ (wI k r (Fin.last k)).val := by
      simp only [wI, Fin.val_mk, Fin.val_zero, Fin.val_last]
      omega
    unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, star_inv_sqrt_two', smul_dotProduct, dotProduct_smul, add_dotProduct,
      dotProduct_add, dotProduct_add]
    simp only [dotProduct_bvec, smul_eq_mul]
    simp only [bvec_apply_eq_ite_val, if_neg hv, if_neg (Ne.symm hv), eq_self_iff_true, if_true]
    linear_combination inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one

/- English proof (translation)
Use `first`. Consider the case `exact star_dotProduct u v`. Consider the case `exact Matrix.star_dotProduct u v`. Consider the case `(simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _)`.
-/
theorem dot_swap {n : ℕ} (u v : Fin n → ℂ) : star u ⬝ᵥ v = star (star v ⬝ᵥ u) := by
  first
    | exact star_dotProduct u v
    | exact Matrix.star_dotProduct u v
    | (simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
       exact Finset.sum_congr rfl fun i _ => mul_comm _ _)

def AN (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : ℕ) : ℂ := if h : j < r' + 1 then aF k r' y ⟨j, h⟩ else 0

def AN' (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : ℕ) : ℂ := if h : j < r' + 1 then aF' k r' y ⟨j, h⟩ else 0

def Uu (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : ℂ :=
  ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i)))

/- English proof (translation)
Unfold `phiV aF'`. Use `split_ifs with ht`. Rewrite using `[star_bvec, bvec_dotProduct]`. Unfold `epsV`. Rewrite using `[star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two', smul_eq_mul]`.
-/
theorem phi_dot_y (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (t : Fin (r' + 1)) :
    star (phiV k r' t) ⬝ᵥ y = aF' k r' y t := by
  unfold phiV aF'
  split_ifs with ht
  · rw [star_bvec, bvec_dotProduct]
  · unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two',
      smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ a b : Fin (2 * r' + k + 1), a.val = b.val → star (y a) * y a = star (y b) * y b`. Introduce `a b h`. Rewrite using `[Fin.ext h]`. Use `set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * y ⟨n, h⟩ else 0 with hf`. Establish `hL : star y ⬝ᵥ y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n`.

Rewrite using `[← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]`. Simplify using `only [dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hf, Pi.star_apply]`. Rewrite using `[dif_pos i.isLt]`.

Establish `h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', star (AN k r' y j) * AN k r' y j`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range]`. Simplify using `only [hf, AN, aF, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [eI, Fin.val_mk])`.

Establish `h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) = ∑ j ∈ Finset.range r', star (AN' k r' y j) * AN' k r' y j`. Rewrite using `[← Finset.sum_range_reflect (fun j => star (AN' k r' y j) * AN' k r' y j) r']`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range]`. Simplify using `only [hf, AN', aF', Fin.val_mk]`.

Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [esI, Fin.val_mk]; omega)`. Establish `h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]`. Unfold `Uu`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hi` using `i.isLt`. Simplify using `only [hf]`. Rewrite using `[dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1)]`. Apply the tactic sequence `exact key _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])`. Establish `h4 : f r' + f (r' + 1 + (k - 1)) = star (AN k r' y r') * AN k r' y r' + star (AN' k r' y r') * AN' k r' y r'`.

Simplify using `only [hf, AN, AN', aF, aF', Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | skip`. Rewrite using `[show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]), show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from Fin.ext (by simp [wI]; omega)]`. Simplify using `only [cc, star_mul', star_sub, star_add, star_inv_sqrt_two']`. Take the linear combination `(-(star (y (wI k r' 0)) * y (wI k r' 0) + star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one`.

Rewrite using `[hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega, Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)), Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r', Finset.sum_rang …`. Take the linear combination `h4`.
-/
theorem pars1' (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    star y ⬝ᵥ y = ∑ j ∈ Finset.range (r' + 1), (star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) +
      Uu k r' y := by
  have key : ∀ a b : Fin (2 * r' + k + 1), a.val = b.val → star (y a) * y a = star (y b) * y b := by
    intro a b h
    rw [Fin.ext h]
  set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * y ⟨n, h⟩ else 0 with hf
  have hL : star y ⬝ᵥ y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n := by
    rw [← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf, Pi.star_apply]
    rw [dif_pos i.isLt]
  have h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', star (AN k r' y j) * AN k r' y j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hf, AN, aF, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [eI, Fin.val_mk])
  have h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) =
      ∑ j ∈ Finset.range r', star (AN' k r' y j) * AN' k r' y j := by
    rw [← Finset.sum_range_reflect (fun j => star (AN' k r' y j) * AN' k r' y j) r']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hf, AN', aF', Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [esI, Fin.val_mk]; omega)
  have h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]
    unfold Uu
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    simp only [hf]
    rw [dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1)]
    exact key _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
  have h4 : f r' + f (r' + 1 + (k - 1)) =
      star (AN k r' y r') * AN k r' y r' + star (AN' k r' y r') * AN' k r' y r' := by
    simp only [hf, AN, AN', aF, aF', Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | skip
    rw [show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]),
      show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from
        Fin.ext (by simp [wI]; omega)]
    simp only [cc, star_mul', star_sub, star_add, star_inv_sqrt_two']
    linear_combination (-(star (y (wI k r' 0)) * y (wI k r' 0) +
      star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
  rw [hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega,
    Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)),
    Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r',
    Finset.sum_range_succ (fun j => star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) r',
    Finset.sum_add_distrib, h1, h2, h3]
  linear_combination h4

/- English proof (translation)
Simplify using `only`. Use `set A := AN k r' x.1 with hAd`. Use `set A' := AN' k r' x.1 with hA'd`. Use `set b := hb k r' x.1 x.2 with hbd`. Establish `hY0 : ∀ c : Fin (1 + r' + 1), c.val = 0 → heis0 k r' x *ᵥ phiV k (1 + r') c = es0 k r' + liftVec k 1 r' x.1 + b • e0 k r'`.

Introduce `c hc; have hc' : c = ⟨0, by omega⟩ := Fin.ext hc; rw [hc', phiV_zero, heisenberg_dual_base_vector_formula]`. Establish `hYs : ∀ c : Fin (1 + r' + 1), ∀ j (hj : j < r' + 1), c.val = j + 1 → heis0 k r' x *ᵥ phiV k (1 + r') c = liftVec k 1 r' (phiV k r' ⟨j, hj⟩) - star (A j) • e0 k r'`. Introduce `c j hj hc; have hc' : c = ⟨j + 1, by omega⟩ := Fin.ext hc`. Rewrite using `[hc', phiV_succ k r' j hj, heis_lift k r' hk]`. Simplify using `only [A, AN, dif_pos hj]`.

Establish `hA : ∀ j (hj : j < r' + 1), A' j = aF' k r' x.1 ⟨j, hj⟩` using `fun j hj => by simp only [A', AN', dif_pos hj]`. Establish `hml : l.val ≤ r' + 1` using `by have := l.isLt; omega`. Unfold `Ga`. Rewrite using `[gram_det l.val _ (star x.1 ⬝ᵥ x.1 + b * star b) (fun j => A' j - b * A j) A]`. Use `congr 1`.

Rewrite using `[pars1' k r' hk]`. Conclude with `final_alg (r' + 1) l.val hml A A' (Uu k r' x.1) b`. Simplify using `only [Matrix.of_apply]; rw [hY0 _ (by simp)]`. Simplify using `[star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, lift_dot]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hY0 _ (by simp), hYs _ j.val (by omega) (by simp), hA j.val (by omega)]`. Simplify using `[star_add, star_smul, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, lift_dot, dot_swap (x.1), phi_dot_y]`. Apply the tactic sequence `try ring`.

Introduce `j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hYs _ j.val (by omega) (by simp), hY0 _ (by simp), hA j.val (by omega)]`. Simplify using `[star_add, star_smul, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, lift_dot, phi_dot_y]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hYs _ i.val (by omega) (by simp), hYs _ j.val (by omega) (by simp)]`. Simplify using `[star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, lift_dot, ortho k r' hk, Fin.ext_iff]`. Apply the tactic sequence `try ring`.
-/
theorem gram_Y (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (fun a => heis0 k r' x *ᵥ phiV k (1 + r') a) =
      (let A := AN k r' x.1; let A' := AN' k r' x.1; let b := hb k r' x.1 x.2
       (1 + ∑ j ∈ Finset.range l.val, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range (r' + 1), star (A j) * A j) +
          Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (A' j) * A' j else 0)) +
        (b + ∑ j ∈ Finset.range l.val, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range l.val, A' j * star (A j))).re := by
  dsimp only
  set A := AN k r' x.1 with hAd
  set A' := AN' k r' x.1 with hA'd
  set b := hb k r' x.1 x.2 with hbd
  have hY0 : ∀ c : Fin (1 + r' + 1), c.val = 0 →
      heis0 k r' x *ᵥ phiV k (1 + r') c = es0 k r' + liftVec k 1 r' x.1 + b • e0 k r' := by
    intro c hc; have hc' : c = ⟨0, by omega⟩ := Fin.ext hc; rw [hc', phiV_zero, heisenberg_dual_base_vector_formula]
  have hYs : ∀ c : Fin (1 + r' + 1), ∀ j (hj : j < r' + 1), c.val = j + 1 →
      heis0 k r' x *ᵥ phiV k (1 + r') c = liftVec k 1 r' (phiV k r' ⟨j, hj⟩) - star (A j) • e0 k r' := by
    intro c j hj hc; have hc' : c = ⟨j + 1, by omega⟩ := Fin.ext hc
    rw [hc', phiV_succ k r' j hj, heis_lift k r' hk]; simp only [A, AN, dif_pos hj]
  have hA : ∀ j (hj : j < r' + 1), A' j = aF' k r' x.1 ⟨j, hj⟩ := fun j hj => by simp only [A', AN', dif_pos hj]
  have hml : l.val ≤ r' + 1 := by have := l.isLt; omega
  unfold Ga
  rw [gram_det l.val _ (star x.1 ⬝ᵥ x.1 + b * star b) (fun j => A' j - b * A j) A]
  · congr 1
    rw [pars1' k r' hk]
    exact final_alg (r' + 1) l.val hml A A' (Uu k r' x.1) b
  · simp only [Matrix.of_apply]; rw [hY0 _ (by simp)]
    simp [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, lift_dot]; ring
  · intro j; simp only [Matrix.of_apply]
    rw [hY0 _ (by simp), hYs _ j.val (by omega) (by simp), hA j.val (by omega)]
    simp [star_add, star_smul, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, lift_dot, dot_swap (x.1), phi_dot_y]
    try ring
  · intro j; simp only [Matrix.of_apply]
    rw [hYs _ j.val (by omega) (by simp), hY0 _ (by simp), hA j.val (by omega)]
    simp [star_add, star_smul, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, lift_dot, phi_dot_y]; ring
  · intro i j; simp only [Matrix.of_apply]
    rw [hYs _ i.val (by omega) (by simp), hYs _ j.val (by omega) (by simp)]
    simp [star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, lift_dot,
      ortho k r' hk, Fin.ext_iff]
    try ring

/- English proof (translation)
Use `first`. Consider the case `(rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq])`. Consider the case `(rw [Complex.star_def, Complex.conj_mul']; push_cast; ring)`. Consider the case `simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]`.
-/
theorem nsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  first
    | (rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq])
    | (rw [Complex.star_def, Complex.conj_mul']; push_cast; ring)
    | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range g (1 + r'), Nat.add_comm]`.
-/
theorem fsum (r' : ℕ) (g : ℕ → ℂ) : ∑ j : Fin (1 + r'), g j.val = ∑ j ∈ Finset.range (r' + 1), g j := by
  rw [Fin.sum_univ_eq_sum_range g (1 + r'), Nat.add_comm]

/- English proof (translation)
Establish `hs` using `Fin.sum_univ_eq_sum_range (fun j => if j < m then g j else 0) (1 + r')`. Rewrite using `[hs, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h.2`. Introduce `h`. Conclude with `⟨by omega, h⟩`.
-/
theorem fsum_lt (r' m : ℕ) (hm : m ≤ r' + 1) (g : ℕ → ℂ) :
    ∑ j : Fin (1 + r'), (if j.val < m then g j.val else 0) = ∑ j ∈ Finset.range m, g j := by
  have hs := Fin.sum_univ_eq_sum_range (fun j => if j < m then g j else 0) (1 + r')
  rw [hs, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨by omega, h⟩

/- English proof (translation)
Establish `hj : j.val < r' + 1` using `by omega`. Use `show herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j)) = AN k r' x.1 j.val`. Unfold `AN herm`. Rewrite using `[dif_pos hj]`. Unfold `phiV aF`.

Apply the tactic sequence `try simp only [Fin.coe_cast, Fin.val_mk]`. Use `split_ifs with h`. Rewrite using `[star_bvec, bvec_dotProduct, Hpk_mulVec_apply_of_outer]`. Use `congrArg x.1 (Fin.ext ?_)` and prove the remaining obligations. Simplify using `only [esI, eI, Fin.val_mk]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [esI, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Unfold `epsV`. Rewrite using `[star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two', Hpk_mulVec_apply_of_mem_middle, Hpk_mulVec_apply_of_val_eq_add]`.

Apply the tactic sequence `all_goals first`. Consider the case `(simp only [smul_eq_mul, cc]; ring)`. Consider the case `(simp [wI]; done)`. Consider the case `(simp [wI]; omega)`. Consider the case `omega`.
-/
theorem hc1 (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (j : Fin (1 + r')) : (hcoord k r' x).1 j = AN k r' x.1 j.val := by
  have hj : j.val < r' + 1 := by omega
  show herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j)) = AN k r' x.1 j.val
  unfold AN herm
  rw [dif_pos hj]
  unfold phiV aF
  try simp only [Fin.coe_cast, Fin.val_mk]
  split_ifs with h
  · rw [star_bvec, bvec_dotProduct, Hpk_mulVec_apply_of_outer]
    · refine congrArg x.1 (Fin.ext ?_)
      simp only [esI, eI, Fin.val_mk]
      omega
    · simp only [esI, Fin.val_mk]
      omega
  · unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two',
      Hpk_mulVec_apply_of_mem_middle, Hpk_mulVec_apply_of_val_eq_add]
    all_goals first
      | (simp only [smul_eq_mul, cc]; ring)
      | (simp [wI]; done)
      | (simp [wI]; omega)
      | omega

/- English proof (translation)
Establish `hj : j.val < r' + 1` using `by omega`. Use `show herm (Hpk k r') x.1 (phiV' k r' (Fin.cast (by omega) j)) = AN' k r' x.1 j.val`. Unfold `herm phiV'`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Hpk_conjTranspose_eq_self, Hpk_mulVec_Hpk_mulVec, phi_dot_y]`. Unfold `AN'`.

Rewrite using `[dif_pos hj]`. Both sides reduce to the same expression.
-/
theorem hc2 (k r' : ℕ) (x : HPar k r') (j : Fin (1 + r')) : (hcoord k r' x).2.1 j = AN' k r' x.1 j.val := by
  have hj : j.val < r' + 1 := by omega
  show herm (Hpk k r') x.1 (phiV' k r' (Fin.cast (by omega) j)) = AN' k r' x.1 j.val
  unfold herm phiV'
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Hpk_conjTranspose_eq_self, Hpk_mulVec_Hpk_mulVec, phi_dot_y]
  unfold AN'
  rw [dif_pos hj]
  rfl

/- English proof (translation)
Unfold `Uu`. Rewrite using `[Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[nsq]`. Establish `e : (hcoord k r' x).2.2.1 i = x.1 (ix k r' (Sum.inr (Sum.inr i)))` using `by show x.1 (wI k r' ⟨i.val + 1, by omega⟩) = _`.

Apply the tactic sequence `congr 1 <;> first | rfl | (apply Fin.ext; rfl) | (apply Fin.ext; simp [wI, ix]) | (apply Fin.ext; simp [wI, ix]; omega)`. Rewrite using `[e]`.
-/
theorem Uu_real (k r' : ℕ) (x : HPar k r') :
    ((∑ i, ‖(hcoord k r' x).2.2.1 i‖ ^ 2 : ℝ) : ℂ) = Uu k r' x.1 := by
  unfold Uu
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsq]
  have e : (hcoord k r' x).2.2.1 i = x.1 (ix k r' (Sum.inr (Sum.inr i))) := by
    show x.1 (wI k r' ⟨i.val + 1, by omega⟩) = _
    congr 1 <;> first | rfl | (apply Fin.ext; rfl) | (apply Fin.ext; simp [wI, ix]) | (apply Fin.ext; simp [wI, ix]; omega)
  rw [e]

/- English proof (translation)
Establish `hl` using `l.isLt`. Unfold `Lsq`. Rewrite using `[Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sum]`. Use `congr 1`. Rewrite using `[← fsum_lt r' l.val (by omega) (fun j => star (AN k r' x.1 j) * AN k r' x.1 j)]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[nsq, hc1 k r' hk x j]`. Simplify using the standard rewrite rules.
-/
theorem Lsq_c (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    (Lsq (hcoord k r' x) l : ℂ) = 1 + ∑ j ∈ Finset.range l.val, star (AN k r' x.1 j) * AN k r' x.1 j := by
  have hl := l.isLt
  unfold Lsq
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sum]
  congr 1
  rw [← fsum_lt r' l.val (by omega) (fun j => star (AN k r' x.1 j) * AN k r' x.1 j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [nsq, hc1 k r' hk x j]
  · simp

/- English proof (translation)
Establish `hL : (Lsq (hcoord k r' x) (Fin.last (1 + r')) : ℂ) = 1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j`. Rewrite using `[Lsq_c k r' hk x, Fin.val_last, Nat.add_comm 1 r']`. Unfold `rhoSq`. Rewrite using `[Complex.ofReal_add, Complex.ofReal_add, hL, Uu_real, Complex.ofReal_sum]`. Use `congr 1`.

Rewrite using `[← fsum r' (fun j => if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[nsq, hc2 k r' x j]`. Simplify using the standard rewrite rules.
-/
theorem rhoSq_c (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    (rhoSq (hcoord k r' x) l : ℂ) = (1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j) +
      Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0) := by
  have hL : (Lsq (hcoord k r' x) (Fin.last (1 + r')) : ℂ) =
      1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j := by
    rw [Lsq_c k r' hk x, Fin.val_last, Nat.add_comm 1 r']
  unfold rhoSq
  rw [Complex.ofReal_add, Complex.ofReal_add, hL, Uu_real, Complex.ofReal_sum]
  congr 1
  rw [← fsum r' (fun j => if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [nsq, hc2 k r' x j]
  · simp

/- English proof (translation)
Establish `hl` using `l.isLt`. Establish `hB : ∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) = ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)`. Rewrite using `[← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hc1 k r' hk x j, hc2 k r' x j]`.

Establish `hC : ∑ j : Fin (1 + r'), (if l.val ≤ j.val then (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) else 0) = ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) - ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j)`. Rewrite using `[← fsum_lt r' l.val (by omega) (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)), ← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)), eq_sub_iff_add_eq, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hc1 k r' hk x j, hc2 k r' x j]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`.

Establish `hD : herm (Hpk k r') x.1 x.1 = (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) + star (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) + Uu k r' x.1` using `by set y := x.1 with hy`. Establish `key2 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val → star (y a) * y b = y d * star (y c)`. Introduce `a b c d h1 h2`. Rewrite using `[Fin.ext h1, Fin.ext h2, mul_comm]`. Establish `key3 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val → star (y a) * y b = star (y c) * y d`.

Introduce `a b c d h1 h2`. Rewrite using `[Fin.ext h1, Fin.ext h2]`. Use `set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * (Hpk k r' *ᵥ y) ⟨n, h⟩ else 0 with hf`. Establish `hL : herm (Hpk k r') y y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n`. Rewrite using `[← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]`.

Simplify using `only [herm, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hf, Pi.star_apply]`. Rewrite using `[dif_pos i.isLt]`. Establish `h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j)`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range]`. Simplify using `only [hf, AN, AN', aF, aF', Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | skip`. Rewrite using `[Hpk_mulVec_apply_of_outer k r' y ⟨j, by omega⟩ (Or.inl (by simp only [Fin.val_mk]; omega))]`.

Apply the tactic sequence `exact key2 _ _ _ _ (by simp only [eI, Fin.val_mk]) (by simp only [esI, Fin.val_mk] <;> omega)`. Establish `h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) = star (∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j))`. Rewrite using `[star_sum, ← Finset.sum_range_reflect (fun j => star (AN' k r' y j * star (AN k r' y j))) r']`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range]`.

Simplify using `only [hf, AN, AN', aF, aF', Fin.val_mk, star_mul', star_star]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | skip`. Rewrite using `[Hpk_mulVec_apply_of_outer k r' y ⟨r' + 1 + (k - 1) + 1 + j, by omega⟩ (Or.inr (by simp only [Fin.val_mk]; omega))]`. Apply the tactic sequence `exact key3 _ _ _ _ (by simp only [esI, Fin.val_mk] <;> omega) (by simp only [eI, Fin.val_mk] <;> omega)`. Establish `h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]`. Unfold `Uu`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`. Simplify using `only [hf]`.

Rewrite using `[dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1), Hpk_mulVec_apply_of_mem_middle k r' y ⟨r' + 1 + i.val, by omega⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]`. Apply the tactic sequence `exact key3 _ _ _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix]) (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])`. Establish `h4 : f r' + f (r' + 1 + (k - 1)) = AN' k r' y r' * star (AN k r' y r') + star (AN' k r' y r' * star (AN k r' y r'))`. Simplify using `only [hf, AN, AN', aF, aF', Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | skip`.

Rewrite using `[Hpk_mulVec_apply_of_mem_middle k r' y ⟨r', by omega⟩, Hpk_mulVec_apply_of_val_eq_add k r' y ⟨r' + 1 + (k - 1), by omega⟩]`. Rewrite using `[show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]), show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from Fin.ext (by simp [wI]; omega)]`. Simplify using `only [cc, star_mul', star_sub, star_add, star_star, star_inv_sqrt_two']`. Take the linear combination `(-(star (y (wI k r' 0)) * y (wI k r' 0) - star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one`. Apply the tactic sequence `all_goals first | omega | (simp only [Fin.val_mk]; omega) | simp`.

Rewrite using `[hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega, Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)), Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r', Finset.sum_rang …`. Take the linear combination `h4`. Unfold `bco`. Rewrite using `[hC]`. Establish `hT : (hcoord k r' x).2.2.2 = x.2 + (∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j)).im` using `rfl`.

Rewrite using `[hT, hB]`. Unfold `hb`. Rewrite using `[hD, ← Uu_real k r' x]`. Generalize the expression as in `(∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) = S`. Generalize the expression as in `(∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j)) = R`.

Generalize the expression as in `(∑ i, ‖(hcoord k r' x).2.2.1 i‖ ^ 2) = U`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.star_def] <;> ring`.
-/
theorem bco_eq (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    bco (hcoord k r' x) l = hb k r' x.1 x.2 + ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j) := by
  have hl := l.isLt
  have hB : ∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) =
      ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) := by
    rw [← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc1 k r' hk x j, hc2 k r' x j]
  have hC : ∑ j : Fin (1 + r'), (if l.val ≤ j.val then (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) else 0) =
      ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) -
        ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j) := by
    rw [← fsum_lt r' l.val (by omega) (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)),
      ← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)), eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc1 k r' hk x j, hc2 k r' x j]
    split_ifs <;> first | (exfalso; omega) | simp
  have hD : herm (Hpk k r') x.1 x.1 = (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) +
      star (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) + Uu k r' x.1 := by
    set y := x.1 with hy
    have key2 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val →
        star (y a) * y b = y d * star (y c) := by
      intro a b c d h1 h2
      rw [Fin.ext h1, Fin.ext h2, mul_comm]
    have key3 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val →
        star (y a) * y b = star (y c) * y d := by
      intro a b c d h1 h2
      rw [Fin.ext h1, Fin.ext h2]
    set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * (Hpk k r' *ᵥ y) ⟨n, h⟩ else 0
      with hf
    have hL : herm (Hpk k r') y y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n := by
      rw [← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]
      simp only [herm, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf, Pi.star_apply]
      rw [dif_pos i.isLt]
    have h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hf, AN, AN', aF, aF', Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_outer k r' y ⟨j, by omega⟩ (Or.inl (by simp only [Fin.val_mk]; omega))]
      exact key2 _ _ _ _ (by simp only [eI, Fin.val_mk]) (by simp only [esI, Fin.val_mk] <;> omega)
    have h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) =
        star (∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j)) := by
      rw [star_sum, ← Finset.sum_range_reflect (fun j => star (AN' k r' y j * star (AN k r' y j))) r']
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hf, AN, AN', aF, aF', Fin.val_mk, star_mul', star_star]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_outer k r' y ⟨r' + 1 + (k - 1) + 1 + j, by omega⟩ (Or.inr (by simp only [Fin.val_mk]; omega))]
      exact key3 _ _ _ _ (by simp only [esI, Fin.val_mk] <;> omega) (by simp only [eI, Fin.val_mk] <;> omega)
    have h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y := by
      rw [← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]
      unfold Uu
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.isLt
      simp only [hf]
      rw [dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1),
        Hpk_mulVec_apply_of_mem_middle k r' y ⟨r' + 1 + i.val, by omega⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
      exact key3 _ _ _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
        (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
    have h4 : f r' + f (r' + 1 + (k - 1)) =
        AN' k r' y r' * star (AN k r' y r') + star (AN' k r' y r' * star (AN k r' y r')) := by
      simp only [hf, AN, AN', aF, aF', Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_mem_middle k r' y ⟨r', by omega⟩, Hpk_mulVec_apply_of_val_eq_add k r' y ⟨r' + 1 + (k - 1), by omega⟩]
      · rw [show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]),
          show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from
            Fin.ext (by simp [wI]; omega)]
        simp only [cc, star_mul', star_sub, star_add, star_star, star_inv_sqrt_two']
        linear_combination (-(star (y (wI k r' 0)) * y (wI k r' 0) -
          star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
      all_goals first | omega | (simp only [Fin.val_mk]; omega) | simp
    rw [hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega,
      Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)),
      Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r',
      Finset.sum_range_succ (fun j => AN' k r' y j * star (AN k r' y j)) r', star_add, h1, h2, h3]
    linear_combination h4
  unfold bco
  rw [hC]
  have hT : (hcoord k r' x).2.2.2 = x.2 + (∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j)).im := rfl
  rw [hT, hB]
  unfold hb
  rw [hD, ← Uu_real k r' x]
  generalize (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) = S
  generalize (∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j)) = R
  generalize (∑ i, ‖(hcoord k r' x).2.2.1 i‖ ^ 2) = U
  apply Complex.ext <;> simp [Complex.star_def] <;> ring

/- English proof (translation)
Unfold `Del de`. Use `congr 1`. Rewrite using `[gram_Y k r' hk x l]`. Apply the tactic sequence `try dsimp only`. Rewrite using `[← Lsq_c k r' hk x l, ← rhoSq_c k r' hk x l, ← bco_eq k r' hk x l, mul_comm (bco (hcoord k r' x) l) (star _), ← nsq, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]`.
-/
theorem del_formula (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Del k (1 + r') l (heis0 k r' x) = de (hcoord k r' x) l := by
  unfold Del de
  congr 1
  rw [gram_Y k r' hk x l]
  try dsimp only
  rw [← Lsq_c k r' hk x l, ← rhoSq_c k r' hk x l, ← bco_eq k r' hk x l,
    mul_comm (bco (hcoord k r' x) l) (star _), ← nsq, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
