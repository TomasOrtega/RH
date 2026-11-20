import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv

noncomputable section

set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable (k r' : ℕ)

def mp (j : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨j.val + 1, by omega⟩

/- English proof (translation)
Establish `h : 2 * r' + k + 1 + 1 = 2 * (1 + r') + k` using `by ring`. Rewrite using `[Fin.sum_univ_succ, ← Fin.sum_congr' _ h, Fin.sum_univ_castSucc, add_assoc (f 0)]`. Establish `e1 : ∀ j : Fin (2 * r' + k + 1), (Fin.cast h j.castSucc).succ = mp k r' j` using `fun j => Fin.ext (by simp [mp])`. Establish `e2 : (Fin.cast h (Fin.last (2 * r' + k + 1))).succ = ⟨2 * (1 + r') + k, by omega⟩` using `Fin.ext (by simp only [Fin.val_succ, Fin.coe_cast, Fin.val_last]; omega)`. Simplify using `only [e1, e2]`.
-/
theorem sum_split (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ p, f p = f 0 + ∑ j, f (mp k r' j) + f ⟨2 * (1 + r') + k, by omega⟩ := by
  have h : 2 * r' + k + 1 + 1 = 2 * (1 + r') + k := by ring
  rw [Fin.sum_univ_succ, ← Fin.sum_congr' _ h, Fin.sum_univ_castSucc, add_assoc (f 0)]
  have e1 : ∀ j : Fin (2 * r' + k + 1), (Fin.cast h j.castSucc).succ = mp k r' j :=
    fun j => Fin.ext (by simp [mp])
  have e2 : (Fin.cast h (Fin.last (2 * r' + k + 1))).succ = ⟨2 * (1 + r') + k, by omega⟩ :=
    Fin.ext (by simp only [Fin.val_succ, Fin.coe_cast, Fin.val_last]; omega)
  simp only [e1, e2]

/- English proof (translation)
Establish `hj` using `j.isLt`. Simplify using `[liftVec, mp]`. Introduce `h`. Use linear arithmetic over natural numbers and integers.
-/
@[simp] theorem lift_mp (v : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) : liftVec k 1 r' v (mp k r' j) = v j := by
  have hj := j.isLt
  simp [liftVec, mp]
  intro h
  omega

/- English proof (translation)
Simplify using `[liftVec]`.
-/
@[simp] theorem lift_zero_pos (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' v 0 = 0 := by
  simp [liftVec]

/- English proof (translation)
Simplify using `only [liftVec]`. Rewrite using `[dif_neg]`. Use linear arithmetic over natural numbers and integers.
-/
@[simp] theorem lift_last (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' v ⟨2 * (1 + r') + k, by omega⟩ = 0 := by
  simp only [liftVec]
  rw [dif_neg]
  omega

/- English proof (translation)
Establish `key : (p = eI k (1 + r') (a0 r')) ↔ p.val = 0`. Rewrite using `[Fin.ext_iff]`. Simplify using `only [eI, a0]`. Unfold `e0 bvec`. Rewrite using `[Pi.single_apply]`.

Simplify using `only [key]`.
-/
theorem goodRowsProjector_apply_eq_sum (p : Fin (2 * (1 + r') + k + 1)) : e0 k r' p = if p.val = 0 then 1 else 0 := by
  have key : (p = eI k (1 + r') (a0 r')) ↔ p.val = 0 := by
    rw [Fin.ext_iff]
    simp only [eI, a0]
  unfold e0 bvec
  rw [Pi.single_apply]
  simp only [key]

/- English proof (translation)
Establish `key : (p = esI k (1 + r') (a0 r')) ↔ p.val = 2 * (1 + r') + k`. Rewrite using `[Fin.ext_iff]`. Simplify using `only [esI, a0, Nat.sub_zero]`. Unfold `es0 bvec`. Rewrite using `[Pi.single_apply]`.

Simplify using `only [key]`.
-/
theorem last_basis_apply (p : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' p = if p.val = 2 * (1 + r') + k then 1 else 0 := by
  have key : (p = esI k (1 + r') (a0 r')) ↔ p.val = 2 * (1 + r') + k := by
    rw [Fin.ext_iff]
    simp only [esI, a0, Nat.sub_zero]
  unfold es0 bvec
  rw [Pi.single_apply]
  simp only [key]

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply]`. Rewrite using `[sum_split k r']`. Simplify using the standard rewrite rules.
-/
theorem dot_lift_lift (u v : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' u) ⬝ᵥ liftVec k 1 r' v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_split k r']
  simp

/- English proof (translation)
Rewrite using `[goodRowsProjector_apply_eq_sum, if_neg]`. Simplify using `only [mp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem e0_mp_eq_zero (j : Fin (2 * r' + k + 1)) : e0 k r' (mp k r' j) = 0 := by
  rw [goodRowsProjector_apply_eq_sum, if_neg]
  simp only [mp]
  omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Rewrite using `[last_basis_apply, if_neg]`. Simplify using `only [mp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem es0_mp_eq_zero (j : Fin (2 * r' + k + 1)) : es0 k r' (mp k r' j) = 0 := by
  have hj := j.isLt
  rw [last_basis_apply, if_neg]
  simp only [mp]
  omega

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply]`. Rewrite using `[sum_split k r']`. Simplify using `[e0_mp_eq_zero, es0_mp_eq_zero]`.
-/
theorem star_last_dot_lift (v : Fin (2 * r' + k + 1) → ℂ) : star (es0 k r') ⬝ᵥ liftVec k 1 r' v = 0 := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_split k r']
  simp [e0_mp_eq_zero, es0_mp_eq_zero]

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply]`. Rewrite using `[sum_split k r']`. Simplify using `[e0_mp_eq_zero, es0_mp_eq_zero]`.
-/
theorem star_lift_dot_last (v : Fin (2 * r' + k + 1) → ℂ) : star (liftVec k 1 r' v) ⬝ᵥ es0 k r' = 0 := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_split k r']
  simp [e0_mp_eq_zero, es0_mp_eq_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, goodRowsProjector_apply_eq_sum, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (Fin.ext (by simp [h]))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem mulVec_first_basis (M : Mat k (1 + r')) : M *ᵥ e0 k r' = fun i => M i 0 := by
  funext i
  simp only [mulVec, dotProduct, goodRowsProjector_apply_eq_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by simp [h]))
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, last_basis_apply, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1))]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hb (Fin.ext h)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem mulVec_last_basis (M : Mat k (1 + r')) : M *ᵥ es0 k r' = fun i => M i ⟨2 * (1 + r') + k, by omega⟩ := by
  funext i
  simp only [mulVec, dotProduct, last_basis_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[mulVec_first_basis]`. Use function extensionality and compare the values at `p`. Rewrite using `[goodRowsProjector_apply_eq_sum]`. Establish `h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0` using `by simp`. Establish `hp0` using `p.isLt`.

Simplify using `only [ιLev, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> (try rfl) <;> (try omega)`.
-/
theorem levi_fixes_base_vector (g : Mat k r') : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' := by
  rw [mulVec_first_basis]
  funext p
  rw [goodRowsProjector_apply_eq_sum]
  have h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0 := by simp
  have hp0 := p.isLt
  simp only [ιLev, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> (try rfl) <;> (try omega)

/- English proof (translation)
Rewrite using `[mulVec_last_basis]`. Use function extensionality and compare the values at `p`. Rewrite using `[last_basis_apply]`. Establish `hp0` using `p.isLt`. Simplify using `only [ιLev, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem levi_fixes_last_basis (g : Mat k r') : ιLev k 1 r' g *ᵥ es0 k r' = es0 k r' := by
  rw [mulVec_last_basis]
  funext p
  rw [last_basis_apply]
  have hp0 := p.isLt
  simp only [ιLev, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Simplify using `only [ιLev, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | exact congrArg (g _) (Fin.ext (by simp)) | (simp; intro; omega)`.
-/
theorem lev_mid (g : Mat k r') (p : Fin (2 * (1 + r') + k + 1)) (j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g p (mp k r' j) =
      if hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then g ⟨p.val - 1, by omega⟩ j else 0 := by
  have hj := j.isLt
  simp only [ιLev, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega | exact congrArg (g _) (Fin.ext (by simp)) | (simp; intro; omega)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_split k r']`. Simplify using `only [lift_zero_pos, lift_last, lift_mp, lev_mid, mul_zero, add_zero, zero_add]`. Simplify using `only [liftVec]`.

Distinguish the cases in `hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1`. Simplify using `only [dif_pos hp, mulVec, dotProduct]`. Simplify using `only [dif_neg hp, zero_mul, Finset.sum_const_zero]`.
-/
theorem lev_lift (g : Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' v = liftVec k 1 r' (g *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_split k r']
  simp only [lift_zero_pos, lift_last, lift_mp, lev_mid, mul_zero, add_zero, zero_add]
  simp only [liftVec]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp, mulVec, dotProduct]
  · simp only [dif_neg hp, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hp0` using `p.isLt`. Simplify using `only [w0, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> (try rfl) <;> (try omega) <;> simp_all`.
-/
theorem rankOneMatrix_middle_coord (c : ℂ) (p : Fin (2 * (1 + r') + k + 1)) (j : Fin (2 * r' + k + 1)) :
    w0 k r' c p (mp k r' j) = if p.val = j.val + 1 then 1 else 0 := by
  have hj := j.isLt
  have hp0 := p.isLt
  simp only [w0, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> (try rfl) <;> (try omega) <;> simp_all

/- English proof (translation)
Rewrite using `[mulVec_first_basis]`. Use function extensionality and compare the values at `p`. Rewrite using `[Pi.smul_apply, last_basis_apply, smul_eq_mul]`. Establish `h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0` using `by simp`. Establish `hp0` using `p.isLt`.

Simplify using `only [w0, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | simp`.
-/
theorem long_weyl_sends_base_to_dual (c : ℂ) : w0 k r' c *ᵥ e0 k r' = c • es0 k r' := by
  rw [mulVec_first_basis]
  funext p
  rw [Pi.smul_apply, last_basis_apply, smul_eq_mul]
  have h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0 := by simp
  have hp0 := p.isLt
  simp only [w0, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega | simp

/- English proof (translation)
Rewrite using `[mulVec_last_basis]`. Use function extensionality and compare the values at `p`. Rewrite using `[Pi.smul_apply, goodRowsProjector_apply_eq_sum, smul_eq_mul]`. Establish `hp0` using `p.isLt`. Simplify using `only [w0, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega | simp`.
-/
theorem rankOneMatrix_last_basis (c : ℂ) : w0 k r' c *ᵥ es0 k r' = (star c)⁻¹ • e0 k r' := by
  rw [mulVec_last_basis]
  funext p
  rw [Pi.smul_apply, goodRowsProjector_apply_eq_sum, smul_eq_mul]
  have hp0 := p.isLt
  simp only [w0, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega | simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_split k r']`. Simplify using `only [lift_zero_pos, lift_last, lift_mp, rankOneMatrix_middle_coord, mul_zero, add_zero, zero_add, ite_mul, one_mul, zero_mul]`. Simplify using `only [liftVec]`.

Distinguish the cases in `hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1`. Rewrite using `[dif_pos hp, Finset.sum_eq_single (⟨p.val - 1, by omega⟩ : Fin (2 * r' + k + 1))]`. Rewrite using `[if_pos] dsimp only`. Use linear arithmetic over natural numbers and integers. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Use `ext`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[dif_neg hp]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `j _`. Establish `hj` using `j.isLt`. Rewrite using `[if_neg]`. Introduce `h`. Apply `hp` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem rankOneMatrix_lift (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : w0 k r' c *ᵥ liftVec k 1 r' v = liftVec k 1 r' v := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_split k r']
  simp only [lift_zero_pos, lift_last, lift_mp, rankOneMatrix_middle_coord, mul_zero, add_zero, zero_add, ite_mul, one_mul,
    zero_mul]
  simp only [liftVec]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hp, Finset.sum_eq_single (⟨p.val - 1, by omega⟩ : Fin (2 * r' + k + 1))]
    · rw [if_pos]
      dsimp only
      omega
    · intro b _ hb
      rw [if_neg]
      intro h
      apply hb
      ext
      dsimp only
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hp]
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    rw [if_neg]
    intro h
    apply hp
    omega

/- English proof (translation)
Rewrite using `[mulVec_first_basis]`. Use function extensionality and compare the values at `p`. Rewrite using `[last_basis_apply]`. Establish `h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0` using `by simp`. Establish `hp0` using `p.isLt`.

Simplify using `only [Hpk, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem Hpk_mulVec_e0 : Hpk k (1 + r') *ᵥ e0 k r' = es0 k r' := by
  rw [mulVec_first_basis]
  funext p
  rw [last_basis_apply]
  have h0 : ((0 : Fin (2 * (1 + r') + k + 1)) : ℕ) = 0 := by simp
  have hp0 := p.isLt
  simp only [Hpk, Fin.ext_iff, h0, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Rewrite using `[mulVec_last_basis]`. Use function extensionality and compare the values at `p`. Rewrite using `[goodRowsProjector_apply_eq_sum]`. Establish `hp0` using `p.isLt`. Simplify using `only [Hpk, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem hermMatrix_last_basis : Hpk k (1 + r') *ᵥ es0 k r' = e0 k r' := by
  rw [mulVec_last_basis]
  funext p
  rw [goodRowsProjector_apply_eq_sum]
  have hp0 := p.isLt
  simp only [Hpk, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hp'` using `p.isLt`. Simplify using `only [Hpk, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private theorem Hpk_one_add_apply_mp_eq_dite (p : Fin (2 * (1 + r') + k + 1)) (j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') p (mp k r' j) =
      if hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then Hpk k r' ⟨p.val - 1, by omega⟩ j else 0 := by
  have hj := j.isLt
  have hp' := p.isLt
  simp only [Hpk, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_split k r']`. Simplify using `only [lift_zero_pos, lift_last, lift_mp, Hpk_one_add_apply_mp_eq_dite, mul_zero, add_zero, zero_add]`. Simplify using `only [liftVec]`.

Distinguish the cases in `hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1`. Simplify using `only [dif_pos hp, mulVec, dotProduct]`. Simplify using `only [dif_neg hp, zero_mul, Finset.sum_const_zero]`.
-/
theorem Hpk_lift (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_split k r']
  simp only [lift_zero_pos, lift_last, lift_mp, Hpk_one_add_apply_mp_eq_dite, mul_zero, add_zero, zero_add]
  simp only [liftVec]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp, mulVec, dotProduct]
  · simp only [dif_neg hp, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `hj` using `j.isLt`. Establish `hp0` using `p.isLt`. Simplify using `only [liftVec, bvec, Pi.single_apply, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem lift_bvec (j : Fin (2 * r' + k + 1)) : liftVec k 1 r' (bvec j) = bvec (mp k r' j) := by
  funext p
  have hj := j.isLt
  have hp0 := p.isLt
  simp only [liftVec, bvec, Pi.single_apply, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega

def sc (a : Fin (r' + 1)) : Fin (1 + r' + 1) := ⟨a.val + 1, by omega⟩

/- English proof (translation)
Establish `h0 : (0 : Fin (1 + r' + 1)).val < 1 + r'`. Rewrite using `[Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Simplify using `[phiV, h0, es0, a0]`.
-/
theorem phiV_zero : phiV k (1 + r') 0 = es0 k r' := by
  have h0 : (0 : Fin (1 + r' + 1)).val < 1 + r' := by
    rw [Fin.val_zero]
    omega
  simp [phiV, h0, es0, a0]

/- English proof (translation)
Establish `ha` using `a.isLt`. Distinguish the cases in `h : a.val < r'`. Establish `h' : (sc r' a).val < 1 + r'`. Simplify using `only [sc]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[phiV, dif_pos h', phiV, dif_pos h, lift_bvec]`. Use `congr 1`. Use `ext`. Simplify using `only [esI, sc, mp]`. Use linear arithmetic over natural numbers and integers.

Establish `h' : ¬ (sc r' a).val < 1 + r'`. Simplify using `only [sc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[phiV, dif_neg h', phiV, dif_neg h]`. Simplify using `only [epsV]`.

Establish `hlin : ∀ (c : ℂ) (x y : Fin (2 * r' + k + 1) → ℂ), liftVec k 1 r' (c • (x + y)) = c • (liftVec k 1 r' x + liftVec k 1 r' y)`. Introduce `c x y`. Use function extensionality and compare the values at `q`. Simplify using `only [liftVec, Pi.smul_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hlin, lift_bvec, lift_bvec]`. Apply the tactic sequence `congr 3 <;> (ext; simp only [wI, mp, Fin.val_zero, Fin.val_last]; omega)`.
-/
theorem phiV_sc (a : Fin (r' + 1)) : phiV k (1 + r') (sc r' a) = liftVec k 1 r' (phiV k r' a) := by
  have ha := a.isLt
  by_cases h : a.val < r'
  · have h' : (sc r' a).val < 1 + r' := by
      simp only [sc]
      omega
    rw [phiV, dif_pos h', phiV, dif_pos h, lift_bvec]
    congr 1
    ext
    simp only [esI, sc, mp]
    omega
  · have h' : ¬ (sc r' a).val < 1 + r' := by
      simp only [sc]
      omega
    rw [phiV, dif_neg h', phiV, dif_neg h]
    simp only [epsV]
    have hlin : ∀ (c : ℂ) (x y : Fin (2 * r' + k + 1) → ℂ),
        liftVec k 1 r' (c • (x + y)) = c • (liftVec k 1 r' x + liftVec k 1 r' y) := by
      intro c x y
      funext q
      simp only [liftVec, Pi.smul_apply, Pi.add_apply]
      split_ifs <;> simp
    rw [hlin, lift_bvec, lift_bvec]
    congr 3 <;> (ext; simp only [wI, mp, Fin.val_zero, Fin.val_last]; omega)

/- English proof (translation)
Simplify using `only [phiV', phiV_zero, hermMatrix_last_basis]`.
-/
theorem phiV'_zero : phiV' k (1 + r') 0 = e0 k r' := by
  simp only [phiV', phiV_zero, hermMatrix_last_basis]

/- English proof (translation)
Simplify using `only [phiV', phiV_sc, Hpk_lift]`.
-/
theorem phiV'_sc (a : Fin (r' + 1)) : phiV' k (1 + r') (sc r' a) = liftVec k 1 r' (phiV' k r' a) := by
  simp only [phiV', phiV_sc, Hpk_lift]

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
