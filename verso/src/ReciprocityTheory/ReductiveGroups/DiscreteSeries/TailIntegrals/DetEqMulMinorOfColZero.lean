import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GoodRowsProjectorApplyEqSum

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section lev
variable (k r' : ℕ)

/- English proof (translation)
Establish `hs : star (bvec b) = bvec b`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = b`. Substitute `h` using the available equality. Simplify using `[bvec]`.

Simplify using `[bvec, h]`. Unfold `herm`. Rewrite using `[hs]`. Simplify using `[bvec, dotProduct, Matrix.mulVec, Pi.single_apply]`.
-/
private lemma herm_bvec_bvec' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    herm H (bvec a) (bvec b) = H b a := by
  have hs : star (bvec b) = bvec b := by
    funext i
    by_cases h : i = b
    · subst h; simp [bvec]
    · simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
Establish `hs : star (bvec b) = bvec b`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = b`. Substitute `h` using the available equality. Simplify using `[bvec]`.

Simplify using `[bvec, h]`. Unfold `herm`. Rewrite using `[hs]`. Simplify using `[bvec, dotProduct, Matrix.mulVec, Pi.single_apply]`.
-/
private lemma herm_bvec_right' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (b : Fin m) :
    herm H v (bvec b) = ∑ j, H b j * v j := by
  have hs : star (bvec b) = bvec b := by
    funext i
    by_cases h : i = b
    · subst h; simp [bvec]
    · simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
Simplify using `[herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]`.
-/
private lemma herm_bvec_left' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (w : Fin m → ℂ) :
    herm H (bvec a) w = ∑ i, star (w i) * H i a := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

/- English proof (translation)
Simplify using `only [liftVec]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private lemma liftVec_apply_of_edge (u : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1))
    (hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k) : liftVec k 1 r' u i = 0 := by
  simp only [liftVec]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `only [liftVec, Fin.val_mk]`. Rewrite using `[dif_pos (by omega)]`. Conclude with `congrArg u (Fin.ext (by show a.val + 1 - 1 = a.val; omega))`.
-/
private lemma liftVec_apply_succ (u : Fin (2 * r' + k + 1) → ℂ) (a : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' u ⟨a.val + 1, by omega⟩ = u a := by
  simp only [liftVec, Fin.val_mk]
  rw [dif_pos (by omega)]
  exact congrArg u (Fin.ext (by show a.val + 1 - 1 = a.val; omega))

/- English proof (translation)
Simplify using `only [Hpk, Fin.val_mk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private lemma Hpk_one_add_apply_succ_succ (a b : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = Hpk k r' a b := by
  simp only [Hpk, Fin.val_mk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hinj : Function.Injective (fun a : Fin (2 * r' + k + 1) => (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)))`. Introduce `a b h`. Simplify using `only [Fin.mk.injEq] at h`. Conclude with `Fin.ext (by omega)`. Use `symm`.

Apply `Fintype.sum_of_injective _ hinj` to reduce the goal to its premises. Introduce `i hi`. Apply `hf` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`. Apply `hi` to reduce the goal to its premises.

Conclude with `⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩`. Introduce `a`. Both sides reduce to the same expression.
-/
private lemma sum_eq_sum_succ_of_zero_at_edges (f : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hf : ∀ i : Fin (2 * (1 + r') + k + 1), (i.val = 0 ∨ i.val = 2 * (1 + r') + k) → f i = 0) :
    ∑ i, f i = ∑ a : Fin (2 * r' + k + 1), f ⟨a.val + 1, by omega⟩ := by
  have hinj : Function.Injective
      (fun a : Fin (2 * r' + k + 1) => (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  symm
  apply Fintype.sum_of_injective _ hinj
  · intro i hi
    apply hf
    by_contra hne
    apply hi
    exact ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
  · intro a
    rfl

/- English proof (translation)
Unfold `herm`. Simplify using `only [dotProduct, Matrix.mulVec]`. Rewrite using `[sum_eq_sum_succ_of_zero_at_edges]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[sum_eq_sum_succ_of_zero_at_edges]`. Simplify using `only [Pi.star_apply, liftVec_apply_succ, Hpk_one_add_apply_succ_succ]`. Introduce `j hj`. Rewrite using `[liftVec_apply_of_edge k r' u j hj, mul_zero]`. Introduce `i hi`.

Rewrite using `[Pi.star_apply, liftVec_apply_of_edge k r' v i hi, star_zero, zero_mul]`.
-/
theorem herm_lift_lift (u v : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' u) (liftVec k 1 r' v) = herm (Hpk k r') u v := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · apply Finset.sum_congr rfl
    intro a _
    rw [sum_eq_sum_succ_of_zero_at_edges]
    · simp only [Pi.star_apply, liftVec_apply_succ, Hpk_one_add_apply_succ_succ]
    · intro j hj
      rw [liftVec_apply_of_edge k r' u j hj, mul_zero]
  · intro i hi
    rw [Pi.star_apply, liftVec_apply_of_edge k r' v i hi, star_zero, zero_mul]

/- English proof (translation)
Simplify using `only [e0]`. Rewrite using `[herm_bvec_left']`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `hi : i.val = 2 * (1 + r') + k`.

Rewrite using `[liftVec_apply_of_edge k r' v i (Or.inr hi), star_zero, zero_mul]`. Apply the tactic sequence `have h0 : Hpk k (1 + r') i (eI k (1 + r') (a0 r')) = 0 := by first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`. Rewrite using `[h0, mul_zero]`.
-/
theorem herm_first_lift_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (e0 k r') (liftVec k 1 r' v) = 0 := by
  simp only [e0]
  rw [herm_bvec_left']
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val = 2 * (1 + r') + k
  · rw [liftVec_apply_of_edge k r' v i (Or.inr hi), star_zero, zero_mul]
  · have h0 : Hpk k (1 + r') i (eI k (1 + r') (a0 r')) = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, mul_zero]

/- English proof (translation)
Simplify using `only [es0]`. Rewrite using `[herm_bvec_left']`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `hi : i.val = 0`.

Rewrite using `[liftVec_apply_of_edge k r' v i (Or.inl hi), star_zero, zero_mul]`. Apply the tactic sequence `have h0 : Hpk k (1 + r') i (esI k (1 + r') (a0 r')) = 0 := by first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`. Rewrite using `[h0, mul_zero]`.
-/
theorem herm_last_lift_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (es0 k r') (liftVec k 1 r' v) = 0 := by
  simp only [es0]
  rw [herm_bvec_left']
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val = 0
  · rw [liftVec_apply_of_edge k r' v i (Or.inl hi), star_zero, zero_mul]
  · have h0 : Hpk k (1 + r') i (esI k (1 + r') (a0 r')) = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, mul_zero]

/- English proof (translation)
Simplify using `only [e0, es0]`. Rewrite using `[herm_bvec_bvec']`. Apply the tactic sequence `first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`.
-/
theorem herm_last_first_eq_one : herm (Hpk k (1 + r')) (es0 k r') (e0 k r') = 1 := by
  simp only [e0, es0]
  rw [herm_bvec_bvec']
  first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single (esI k (1 + r') (a0 r'))]`. Apply the tactic sequence `have h1 : Hpk k (1 + r') (eI k (1 + r') (a0 r')) (esI k (1 + r') (a0 r')) = 1 := by first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`. Rewrite using `[h1, one_mul]`. Introduce `j _ hj`. Establish `hj' : j.val ≠ 2 * (1 + r') + k` using `fun h => hj (Fin.ext (by simp only [esI, a0, Fin.val_mk]; omega))`.

Apply the tactic sequence `have h0 : Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = 0 := by first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`. Rewrite using `[h0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma sum_Hpk_eI_a0_mul_eq_esI (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ j, Hpk k (1 + r') (eI k (1 + r') (a0 r')) j * w j = w (esI k (1 + r') (a0 r')) := by
  rw [Finset.sum_eq_single (esI k (1 + r') (a0 r'))]
  · have h1 : Hpk k (1 + r') (eI k (1 + r') (a0 r')) (esI k (1 + r') (a0 r')) = 1 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * (1 + r') + k := fun h => hj (Fin.ext (by simp only [esI, a0, Fin.val_mk]; omega))
    have h0 : Hpk k (1 + r') (eI k (1 + r') (a0 r')) j = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single (eI k (1 + r') (a0 r'))]`. Apply the tactic sequence `have h1 : Hpk k (1 + r') (esI k (1 + r') (a0 r')) (eI k (1 + r') (a0 r')) = 1 := by first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`. Rewrite using `[h1, one_mul]`. Introduce `j _ hj`. Establish `hj' : j.val ≠ 0` using `fun h => hj (Fin.ext (by simp only [eI, a0, Fin.val_mk]; omega))`.

Apply the tactic sequence `have h0 : Hpk k (1 + r') (esI k (1 + r') (a0 r')) j = 0 := by first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])`. Rewrite using `[h0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma sum_Hpk_esI_a0_mul_eq_eI (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ j, Hpk k (1 + r') (esI k (1 + r') (a0 r')) j * w j = w (eI k (1 + r') (a0 r')) := by
  rw [Finset.sum_eq_single (eI k (1 + r') (a0 r'))]
  · have h1 : Hpk k (1 + r') (esI k (1 + r') (a0 r')) (eI k (1 + r') (a0 r')) = 1 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext (by simp only [eI, a0, Fin.val_mk]; omega))
    have h0 : Hpk k (1 + r') (esI k (1 + r') (a0 r')) j = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`.
-/
private lemma mulVec_bvec_eq_col_fun {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    H *ᵥ bvec j = fun i => H i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [phiV', phiV]`. Apply the tactic sequence `rw [dif_pos (by first | simp | (rw [Fin.val_zero]; omega))]`. Rewrite using `[mulVec_bvec_eq_col_fun]`. Simplify using `only [e0, bvec, Pi.single_apply, Hpk, esI, eI, a0, Fin.val_mk, Fin.ext_iff, Fin.val_zero]`.

Apply the tactic sequence `(try split_ifs) <;> (first | rfl | omega)`.
-/
private lemma phiV'_one_add_zero_eq_first_basis_e0_vec : phiV' k (1 + r') 0 = e0 k r' := by
  funext i
  simp only [phiV', phiV]
  rw [dif_pos (by first | simp | (rw [Fin.val_zero]; omega))]
  rw [mulVec_bvec_eq_col_fun]
  simp only [e0, bvec, Pi.single_apply, Hpk, esI, eI, a0, Fin.val_mk, Fin.ext_iff, Fin.val_zero]
  (try split_ifs) <;> (first | rfl | omega)

/- English proof (translation)
Simplify using `only [e0]`. Rewrite using `[herm_bvec_right', sum_Hpk_eI_a0_mul_eq_esI]`. Simplify using `only [phiV', Matrix.mulVec, dotProduct]`. Rewrite using `[sum_Hpk_esI_a0_mul_eq_eI]`. Simplify using `only [phiV]`.

Use `split_ifs with hb`. Apply the tactic sequence `simp only [bvec, Pi.single_apply, esI, eI, a0, Fin.val_mk, Fin.ext_iff] (try split_ifs) <;> (first | rfl | omega)`. Apply the tactic sequence `simp only [epsV, Pi.smul_apply, Pi.add_apply, bvec, Pi.single_apply, wI, eI, a0, Fin.val_mk, Fin.ext_iff, Fin.val_zero, Fin.val_last] (try split_ifs) <;> (first | omega | simp)`.
-/
theorem herm_phi_first_eq_zero (b : Fin (1 + r' + 1)) : herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (e0 k r') = 0 := by
  simp only [e0]
  rw [herm_bvec_right', sum_Hpk_eI_a0_mul_eq_esI]
  simp only [phiV', Matrix.mulVec, dotProduct]
  rw [sum_Hpk_esI_a0_mul_eq_eI]
  simp only [phiV]
  split_ifs with hb
  · simp only [bvec, Pi.single_apply, esI, eI, a0, Fin.val_mk, Fin.ext_iff]
    (try split_ifs) <;> (first | rfl | omega)
  · simp only [epsV, Pi.smul_apply, Pi.add_apply, bvec, Pi.single_apply, wI, eI, a0, Fin.val_mk,
      Fin.ext_iff, Fin.val_zero, Fin.val_last]
    (try split_ifs) <;> (first | omega | simp)

/- English proof (translation)
Simplify using `only [heis0]`. Rewrite using `[hHA k r', herm_phi_first_eq_zero k r' b, phiV'_one_add_zero_eq_first_basis_e0_vec k r']`. Simplify using the standard rewrite rules.
-/
theorem heis_phi' (hHA : HeisAct) (x : HPar k r') (b : Fin (1 + r' + 1)) :
    heis0 k r' x *ᵥ phiV' k (1 + r') b = phiV' k (1 + r') b -
      herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x.1) • phiV' k (1 + r') 0 := by
  simp only [heis0]
  rw [hHA k r', herm_phi_first_eq_zero k r' b, phiV'_one_add_zero_eq_first_basis_e0_vec k r']
  simp

end lev

section dl
variable (k r : ℕ)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Distinguish the cases in `hc : i.val < r ∨ r + k < i.val`. Rewrite using `[Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]`. Apply the tactic sequence `simp only [Hpk, Fin.val_mk, Fin.ext_iff, and_true, true_and] (try split_ifs) <;> (first | omega | norm_num)`.

Introduce `m _ hm`. Establish `hm' : m.val ≠ 2 * r + k - i.val` using `fun h => hm (Fin.ext h)`. Simplify using `only [Hpk, Fin.ext_iff, and_true, true_and]`. Apply the tactic sequence `(try split_ifs) <;> (first | omega | norm_num)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_eq_single i]`. Apply the tactic sequence `simp only [Hpk, Fin.ext_iff, and_true, true_and] (try split_ifs) <;> (first | omega | norm_num)`. Introduce `m _ hm`. Establish `hm' : m.val ≠ i.val` using `fun h => hm (Fin.ext h)`.

Simplify using `only [Hpk, Fin.ext_iff, and_true, true_and]`. Apply the tactic sequence `(try split_ifs) <;> (first | omega | norm_num)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma Hpk_mul_Hpk_eq_one : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [Hpk, Fin.val_mk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro m _ hm
      have hm' : m.val ≠ 2 * r + k - i.val := fun h => hm (Fin.ext h)
      simp only [Hpk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · simp only [Hpk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro m _ hm
      have hm' : m.val ≠ i.val := fun h => hm (Fin.ext h)
      simp only [Hpk, Fin.ext_iff, and_true, true_and]
      (try split_ifs) <;> (first | omega | norm_num)
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]`.
-/
private lemma herm_sub_smul_left' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v w u : Fin m → ℂ) (c : ℂ) :
    herm H (v - c • w) u = herm H v u - c * herm H w u := by
  simp [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]

/- English proof (translation)
Simplify using `[herm, star_sub, star_smul, sub_dotProduct, smul_dotProduct]`.
-/
private lemma herm_sub_smul_right' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v w : Fin m → ℂ) (c : ℂ) :
    herm H u (v - c • w) = herm H u v - star c * herm H u w := by
  simp [herm, star_sub, star_smul, sub_dotProduct, smul_dotProduct]

/- English proof (translation)
Establish `HH : Hpk k r * Hpk k r = 1` using `Hpk_mul_Hpk_eq_one k r`. Establish `hinv : n⁻¹ = Hpk k r * nᴴ * Hpk k r`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `h1 : nᴴ * Hpk k r * n = Hpk k r` using `hn`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1, HH]`. Establish `hherm : ∀ z w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) (n⁻¹ *ᵥ z) w = herm (Hpk k r) z (n *ᵥ w)`. Introduce `z w`. Establish `e1 : Hpk k r * (Hpk k r * nᴴ * Hpk k r) = nᴴ * Hpk k r`.

Simplify using `only [← Matrix.mul_assoc, HH, Matrix.one_mul]`. Unfold `herm`. Rewrite using `[hinv, Matrix.mulVec_mulVec, e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]`. Establish `hc0 : ∀ h : l.val + 1 ≤ r + 1, Fin.castLE h (0 : Fin (l.val + 1)) = 0` using `fun h => Fin.ext (by simp)`. Establish `detP : (1 - Matrix.of fun a c : Fin (l.val + 1) => if c = 0 then star (β (Fin.castLE (by omega) a)) else 0).det = 1`.

Rewrite using `[Matrix.det_of_lowerTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Simplify using `[hc0, hβ]`. Simplify using `[hi]`. Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Establish `hj : j ≠ 0` using `fun h => absurd (h ▸ hij') (Fin.not_lt_zero i)`.

Simplify using `[hj, Matrix.one_apply, ne_of_lt hij']`. Establish `detQ : (1 - Matrix.of fun d b : Fin (l.val + 1) => if d = 0 then α (Fin.castLE (by omega) b) else 0).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`.

Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Simplify using `[hc0, hα]`. Simplify using `[hi]`. Introduce `i j hij`.

Establish `hij' : j < i` using `hij`. Establish `hi : i ≠ 0` using `fun h => absurd (h ▸ hij') (Fin.not_lt_zero j)`. Simplify using `[hi, Matrix.one_apply, ne_of_gt hij']`. Unfold `Dl`. Establish `hM : (Matrix.of fun a b : Fin (l.val + 1) => herm (Hpk k r) ((n⁻¹ * Y * n') *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a))) = (1 - Matrix.of fun a c : Fin (l.val + 1) => if c = 0 then star (β (Fin.castLE (by omega) a)) else 0) * (Matrix.of fun a b : …`.

Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, ← Matrix.mulVec_mulVec, hherm, hn', hnn, Matrix.mulVec_sub, Matrix.mulVec_smul, herm_sub_smul_left', herm_sub_smul_right']`. Simplify using `[Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', hc0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hM, Matrix.det_mul, Matrix.det_mul, detP, detQ, one_mul, mul_one]`.
-/
theorem Dl_conj (l : Fin (r + 1)) (Y n n' : Mat k r) (hn : n ∈ GV k r) (α β : Fin (r + 1) → ℂ)
    (hα : α 0 = 0) (hβ : β 0 = 0)
    (hn' : ∀ b, n' *ᵥ phiV' k r b = phiV' k r b - α b • phiV' k r 0)
    (hnn : ∀ a, n *ᵥ phiV' k r a = phiV' k r a - β a • phiV' k r 0) :
    Dl k r l (n⁻¹ * Y * n') = Dl k r l Y := by
  have HH : Hpk k r * Hpk k r = 1 := Hpk_mul_Hpk_eq_one k r
  have hinv : n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    have h1 : nᴴ * Hpk k r * n = Hpk k r := hn
    calc Hpk k r * nᴴ * Hpk k r * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, HH]
  have hherm : ∀ z w : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) (n⁻¹ *ᵥ z) w = herm (Hpk k r) z (n *ᵥ w) := by
    intro z w
    have e1 : Hpk k r * (Hpk k r * nᴴ * Hpk k r) = nᴴ * Hpk k r := by
      simp only [← Matrix.mul_assoc, HH, Matrix.one_mul]
    unfold herm
    rw [hinv, Matrix.mulVec_mulVec, e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  have hc0 : ∀ h : l.val + 1 ≤ r + 1, Fin.castLE h (0 : Fin (l.val + 1)) = 0 :=
    fun h => Fin.ext (by simp)
  have detP : (1 - Matrix.of fun a c : Fin (l.val + 1) =>
      if c = 0 then star (β (Fin.castLE (by omega) a)) else 0).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = 0
      · subst hi
        simp [hc0, hβ]
      · simp [hi]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := fun h => absurd (h ▸ hij') (Fin.not_lt_zero i)
      simp [hj, Matrix.one_apply, ne_of_lt hij']
  have detQ : (1 - Matrix.of fun d b : Fin (l.val + 1) =>
      if d = 0 then α (Fin.castLE (by omega) b) else 0).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = 0
      · subst hi
        simp [hc0, hα]
      · simp [hi]
    · intro i j hij
      have hij' : j < i := hij
      have hi : i ≠ 0 := fun h => absurd (h ▸ hij') (Fin.not_lt_zero j)
      simp [hi, Matrix.one_apply, ne_of_gt hij']
  unfold Dl
  have hM : (Matrix.of fun a b : Fin (l.val + 1) =>
      herm (Hpk k r) ((n⁻¹ * Y * n') *ᵥ phiV' k r (Fin.castLE (by omega) b))
        (phiV' k r (Fin.castLE (by omega) a))) =
      (1 - Matrix.of fun a c : Fin (l.val + 1) =>
          if c = 0 then star (β (Fin.castLE (by omega) a)) else 0) *
        (Matrix.of fun a b : Fin (l.val + 1) =>
          herm (Hpk k r) (Y *ᵥ phiV' k r (Fin.castLE (by omega) b))
            (phiV' k r (Fin.castLE (by omega) a))) *
        (1 - Matrix.of fun d b : Fin (l.val + 1) =>
          if d = 0 then α (Fin.castLE (by omega) b) else 0) := by
    ext a b
    simp only [Matrix.of_apply, ← Matrix.mulVec_mulVec, hherm, hn', hnn, Matrix.mulVec_sub,
      Matrix.mulVec_smul, herm_sub_smul_left', herm_sub_smul_right']
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', hc0]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, detP, detQ, one_mul, mul_one]

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Simplify using `[h]`.
-/
theorem det_eq_mul_minor_of_col_zero_alt {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (h : ∀ i : Fin m, A i.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

end dl

section a1
variable (k r' : ℕ)

/- English proof (translation)
Apply the tactic sequence `first | rfl | (ext; simp [sc])`.
-/
theorem castLE_succ_eq {m : ℕ} (h : m + 1 ≤ 1 + r' + 1) (b : Fin m) :
    Fin.castLE h b.succ = sc r' ⟨b.val, by omega⟩ := by first | rfl | (ext; simp [sc])

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hs : (sc r' b).val = b.val + 1` using `rfl`. Distinguish the cases in `hb : b.val < r'`. Establish `h1 : (sc r' b).val < 1 + r'` using `by omega`. Simplify using `only [phiV]`.

Rewrite using `[dif_pos h1, dif_pos hb]`. Simplify using `only [liftVec, bvec, Pi.single_apply, esI, hs, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]`. Apply the tactic sequence `(try split_ifs) <;> (first | rfl | omega)`. Establish `h1 : ¬ (sc r' b).val < 1 + r'` using `by omega`. Simplify using `only [phiV]`.

Rewrite using `[dif_neg h1, dif_neg hb]`. Simplify using `only [liftVec, epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply, wI, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and, Fin.val_zero, Fin.val_last]`. Apply the tactic sequence `(try split_ifs) <;> (first | rfl | omega | simp)`.
-/
private lemma phiV_one_add_sc_eq_liftVec (b : Fin (r' + 1)) :
    phiV k (1 + r') (sc r' b) = liftVec k 1 r' (phiV k r' b) := by
  funext i
  have hs : (sc r' b).val = b.val + 1 := rfl
  by_cases hb : b.val < r'
  · have h1 : (sc r' b).val < 1 + r' := by omega
    simp only [phiV]
    rw [dif_pos h1, dif_pos hb]
    simp only [liftVec, bvec, Pi.single_apply, esI, hs, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
    (try split_ifs) <;> (first | rfl | omega)
  · have h1 : ¬ (sc r' b).val < 1 + r' := by omega
    simp only [phiV]
    rw [dif_neg h1, dif_neg hb]
    simp only [liftVec, epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply, wI, Fin.val_mk,
      Fin.ext_iff, and_false, false_and, and_true, true_and, Fin.val_zero, Fin.val_last]
    (try split_ifs) <;> (first | rfl | omega | simp)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[sum_eq_sum_succ_of_zero_at_edges]`. Distinguish the cases in `hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k`. Rewrite using `[liftVec_apply_of_edge k r' _ i hi]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Establish `h0 : Hpk k (1 + r') i ⟨b.val + 1, by omega⟩ = 0`. Simplify using `only [Hpk, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]`. Apply the tactic sequence `(try split_ifs) <;> (first | rfl | omega)`.

Rewrite using `[h0, zero_mul]`. Take `⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1), (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i` from `⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩`. Simplify using `only [liftVec_apply_succ, Hpk_one_add_apply_succ_succ, Matrix.mulVec, dotProduct]`. Introduce `j hj`. Rewrite using `[liftVec_apply_of_edge k r' v j hj, mul_zero]`.
-/
private lemma Hpk_succ_mulVec_liftVec (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · by_cases hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [liftVec_apply_of_edge k r' _ i hi]
      apply Finset.sum_eq_zero
      intro b _
      have h0 : Hpk k (1 + r') i ⟨b.val + 1, by omega⟩ = 0 := by
        simp only [Hpk, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
        (try split_ifs) <;> (first | rfl | omega)
      rw [h0, zero_mul]
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1),
          (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i :=
        ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
      simp only [liftVec_apply_succ, Hpk_one_add_apply_succ_succ, Matrix.mulVec, dotProduct]
  · intro j hj
    rw [liftVec_apply_of_edge k r' v j hj, mul_zero]

/- English proof (translation)
Simplify using `only [phiV']`. Rewrite using `[phiV_one_add_sc_eq_liftVec, Hpk_succ_mulVec_liftVec]`.
-/
private lemma phiV'_one_add_sc_eq_liftVec (b : Fin (r' + 1)) :
    phiV' k (1 + r') (sc r' b) = liftVec k 1 r' (phiV' k r' b) := by
  simp only [phiV']
  rw [phiV_one_add_sc_eq_liftVec, Hpk_succ_mulVec_liftVec]

/- English proof (translation)
Use `first`. Consider the case `(simp [ιLev]; done)`. Consider the case `(simp only [ιLev, Fin.val_mk]; rw [dif_pos (by omega), dif_pos (by omega)]; rfl)`.
-/
private lemma lev_apply_succ_succ (g : Mat k r') (a b : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = g a b := by
  first
  | (simp [ιLev]; done)
  | (simp only [ιLev, Fin.val_mk]; rw [dif_pos (by omega), dif_pos (by omega)]; rfl)

/- English proof (translation)
Simplify using `only [w0, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]`. Apply the tactic sequence `(try split_ifs) <;> (first | rfl | omega)`.
-/
private lemma w0_apply_succ_succ (c : ℂ) (a b : Fin (2 * r' + k + 1)) :
    w0 k r' c ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = if a = b then 1 else 0 := by
  simp only [w0, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
  (try split_ifs) <;> (first | rfl | omega)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[sum_eq_sum_succ_of_zero_at_edges]`. Distinguish the cases in `hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k`. Rewrite using `[liftVec_apply_of_edge k r' _ i hi]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Establish `h0 : ιLev k 1 r' g i ⟨b.val + 1, by omega⟩ = 0`. Simplify using `only [ιLev, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]`. Apply the tactic sequence `(try split_ifs) <;> (first | rfl | omega)`.

Rewrite using `[h0, zero_mul]`. Take `⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1), (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i` from `⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩`. Simplify using `only [liftVec_apply_succ, lev_apply_succ_succ, Matrix.mulVec, dotProduct]`. Introduce `j hj`. Rewrite using `[liftVec_apply_of_edge k r' u j hj, mul_zero]`.
-/
private lemma lev_mulVec_liftVec (g : Mat k r') (u : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' u = liftVec k 1 r' (g *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · by_cases hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [liftVec_apply_of_edge k r' _ i hi]
      apply Finset.sum_eq_zero
      intro b _
      have h0 : ιLev k 1 r' g i ⟨b.val + 1, by omega⟩ = 0 := by
        simp only [ιLev, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
        (try split_ifs) <;> (first | rfl | omega)
      rw [h0, zero_mul]
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1),
          (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i :=
        ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
      simp only [liftVec_apply_succ, lev_apply_succ_succ, Matrix.mulVec, dotProduct]
  · intro j hj
    rw [liftVec_apply_of_edge k r' u j hj, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[sum_eq_sum_succ_of_zero_at_edges]`. Distinguish the cases in `hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k`. Rewrite using `[liftVec_apply_of_edge k r' _ i hi]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Establish `h0 : w0 k r' c i ⟨b.val + 1, by omega⟩ = 0`. Establish `hb` using `b.isLt`. Establish `hil` using `i.isLt`.

Simplify using `only [w0]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and] at *); all_goals omega)`. Rewrite using `[h0, zero_mul]`. Take `⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1), (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i` from `⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩`. Simplify using `only [liftVec_apply_succ, w0_apply_succ_succ]`.

Simplify using the standard rewrite rules. Introduce `j hj`. Rewrite using `[liftVec_apply_of_edge k r' u j hj, mul_zero]`.
-/
private lemma w0_mulVec_liftVec (c : ℂ) (u : Fin (2 * r' + k + 1) → ℂ) :
    w0 k r' c *ᵥ liftVec k 1 r' u = liftVec k 1 r' u := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · by_cases hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [liftVec_apply_of_edge k r' _ i hi]
      apply Finset.sum_eq_zero
      intro b _
      have h0 : w0 k r' c i ⟨b.val + 1, by omega⟩ = 0 := by
        have hb := b.isLt
        have hil := i.isLt
        simp only [w0]
        split_ifs with h1 h2 h3 <;>
          first | rfl | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and] at *); all_goals omega)
      rw [h0, zero_mul]
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1),
          (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i :=
        ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
      simp only [liftVec_apply_succ, w0_apply_succ_succ]
      simp
  · intro j hj
    rw [liftVec_apply_of_edge k r' u j hj, mul_zero]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, lev_mulVec_liftVec, w0_mulVec_liftVec]`.
-/
private lemma w0_mul_lev_mulVec_liftVec (c : ℂ) (g : Mat k r') (u : Fin (2 * r' + k + 1) → ℂ) :
    (w0 k r' c * ιLev k 1 r' g) *ᵥ liftVec k 1 r' u = liftVec k 1 r' (g *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, lev_mulVec_liftVec, w0_mulVec_liftVec]

/- English proof (translation)
Establish `h1 : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r'`. Use function extensionality and compare the values at `i`. Simplify using `only [e0]`. Rewrite using `[mulVec_bvec_eq_col_fun]`. Simplify using `only [ιLev, bvec, Pi.single_apply]`.

Distinguish the cases in `hp : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1`. Establish `hq : ¬ (1 ≤ (eI k (1 + r') (a0 r')).val ∧ (eI k (1 + r') (a0 r')).val < 2 * r' + k + 1 + 1)`. Simplify using `[eI, a0]`. Rewrite using `[dif_pos hp, dif_neg hq, if_neg]`. Introduce `hh`.

Rewrite `hp` using `[hh]`. Simplify using `[eI, a0] at hp`. Rewrite using `[dif_neg hp]`. Establish `h2 : w0 k r' c *ᵥ e0 k r' = c • es0 k r'`. Use function extensionality and compare the values at `i`.

Simplify using `only [e0, es0]`. Rewrite using `[mulVec_bvec_eq_col_fun]`. Simplify using `only [w0, bvec, Pi.smul_apply, Pi.single_apply, esI, eI, a0, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and, smul_eq_mul]`. Apply the tactic sequence `(try split_ifs) <;> (first | omega | simp)`. Rewrite using `[← Matrix.mulVec_mulVec, h1, h2]`.
-/
private lemma w0_mul_lev_mulVec_e0_eq_smul_es0 (c : ℂ) (g : Mat k r') :
    (w0 k r' c * ιLev k 1 r' g) *ᵥ e0 k r' = c • es0 k r' := by
  have h1 : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' := by
    funext i
    simp only [e0]
    rw [mulVec_bvec_eq_col_fun]
    simp only [ιLev, bvec, Pi.single_apply]
    by_cases hp : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
    · have hq : ¬ (1 ≤ (eI k (1 + r') (a0 r')).val ∧
          (eI k (1 + r') (a0 r')).val < 2 * r' + k + 1 + 1) := by
        simp [eI, a0]
      rw [dif_pos hp, dif_neg hq, if_neg]
      intro hh
      rw [hh] at hp
      simp [eI, a0] at hp
    · rw [dif_neg hp]
  have h2 : w0 k r' c *ᵥ e0 k r' = c • es0 k r' := by
    funext i
    simp only [e0, es0]
    rw [mulVec_bvec_eq_col_fun]
    simp only [w0, bvec, Pi.smul_apply, Pi.single_apply, esI, eI, a0, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and,
      smul_eq_mul]
    (try split_ifs) <;> (first | omega | simp)
  rw [← Matrix.mulVec_mulVec, h1, h2]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_smul, dotProduct_smul]`.
-/
private lemma herm_smul_left_tail_integrals {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (v w : Fin m → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Establish `hc0 : ∀ h : l.val + 1 ≤ 1 + r' + 1, Fin.castLE h (0 : Fin (l.val + 1)) = 0` using `fun h => Fin.ext (by simp)`. Unfold `Dl`. Rewrite using `[det_eq_mul_minor_of_col_zero_alt]`. Use `congr 1`. Simplify using `only [Matrix.of_apply, hc0, phiV'_one_add_zero_eq_first_basis_e0_vec, w0_mul_lev_mulVec_e0_eq_smul_es0, herm_smul_left_tail_integrals, herm_last_first_eq_one, mul_one]`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, castLE_succ_eq, phiV'_one_add_sc_eq_liftVec, w0_mul_lev_mulVec_liftVec, herm_lift_lift]`. Introduce `i`. Simplify using `only [Matrix.of_apply, hc0, phiV'_one_add_zero_eq_first_basis_e0_vec, w0_mul_lev_mulVec_e0_eq_smul_es0, herm_smul_left_tail_integrals, castLE_succ_eq, phiV'_one_add_sc_eq_liftVec, herm_last_lift_eq_zero, mul_zero]`.
-/
theorem Dl_Y (c : ℂ) (g : Mat k r') (l : Fin (1 + r' + 1)) :
    Dl k (1 + r') l (w0 k r' c * ιLev k 1 r' g) =
      c * (Matrix.of fun a b : Fin l.val =>
        herm (Hpk k r') (g *ᵥ phiV' k r' ⟨b.val, by omega⟩) (phiV' k r' ⟨a.val, by omega⟩)).det := by
  have hc0 : ∀ h : l.val + 1 ≤ 1 + r' + 1, Fin.castLE h (0 : Fin (l.val + 1)) = 0 :=
    fun h => Fin.ext (by simp)
  unfold Dl
  rw [det_eq_mul_minor_of_col_zero_alt]
  · congr 1
    · simp only [Matrix.of_apply, hc0, phiV'_one_add_zero_eq_first_basis_e0_vec, w0_mul_lev_mulVec_e0_eq_smul_es0, herm_smul_left_tail_integrals, herm_last_first_eq_one, mul_one]
    · congr 1
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.of_apply, castLE_succ_eq, phiV'_one_add_sc_eq_liftVec, w0_mul_lev_mulVec_liftVec,
        herm_lift_lift]
  · intro i
    simp only [Matrix.of_apply, hc0, phiV'_one_add_zero_eq_first_basis_e0_vec, w0_mul_lev_mulVec_e0_eq_smul_es0, herm_smul_left_tail_integrals, castLE_succ_eq, phiV'_one_add_sc_eq_liftVec,
      herm_last_lift_eq_zero, mul_zero]

/- English proof (translation)
Rewrite using `[Dl_Y]`. Apply the tactic sequence `first | rfl | (unfold Dl; rfl)`.
-/
theorem Dl_Y_sc (c : ℂ) (g : Mat k r') (l : Fin (r' + 1)) :
    Dl k (1 + r') (sc r' l) (w0 k r' c * ιLev k 1 r' g) = c * Dl k r' l g := by
  rw [Dl_Y]
  first | rfl | (unfold Dl; rfl)

/- English proof (translation)
Rewrite using `[Dl_Y, Matrix.det_eq_one_of_card_eq_zero]`. Apply the tactic sequence `all_goals first | (simp; done) | (simp; exact Fintype.card_eq_zero) | exact Fintype.card_eq_zero | (simp; rfl)`.
-/
theorem Dl_Y_zero (c : ℂ) (g : Mat k r') : Dl k (1 + r') 0 (w0 k r' c * ιLev k 1 r' g) = c := by
  rw [Dl_Y, Matrix.det_eq_one_of_card_eq_zero]
  all_goals first | (simp; done) | (simp; exact Fintype.card_eq_zero) | exact Fintype.card_eq_zero | (simp; rfl)

/- English proof (translation)
Establish `hn : heis0 k r' x ∈ GV k (1 + r')` using `by first`. Consider the case `exact (hHM k r' x).1`. Consider the case `(have h := hHM k r' x; simp only [Nset, Set.mem_setOf_eq] at h; exact h.1)`. Establish `hphi0` using `phiV'_one_add_zero_eq_first_basis_e0_vec k r'`. Unfold `oneStep`.

Rewrite using `[mul_assoc ((heis0 k r' x)⁻¹) (w0 k r' c) (ιLev k 1 r' g)]`. Apply `Dl_conj k (1 + r') l _ _ _ hn (fun b => herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x'.1)) (fun b => herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x.1))` to reduce the goal to its premises. Use `show herm (Hpk k (1 + r')) (phiV' k (1 + r') 0) (liftVec k 1 r' x'.1) = 0`. Rewrite using `[hphi0]`. Conclude with `herm_first_lift_eq_zero k r' _`.

Use `show herm (Hpk k (1 + r')) (phiV' k (1 + r') 0) (liftVec k 1 r' x.1) = 0`. Rewrite using `[hphi0]`. Conclude with `herm_first_lift_eq_zero k r' _`. Introduce `b`. Conclude with `heis_phi' k r' hHA x' b`.

Introduce `a`. Conclude with `heis_phi' k r' hHA x a`.
-/
theorem Dl_oneStep (hHA : HeisAct) (hHM : HeisMem) (x x' : HPar k r') (c : ℂ) (g : Mat k r')
    (l : Fin (1 + r' + 1)) :
    Dl k (1 + r') l (oneStep k r' x c g x') = Dl k (1 + r') l (w0 k r' c * ιLev k 1 r' g) := by
  have hn : heis0 k r' x ∈ GV k (1 + r') := by
    first
    | exact (hHM k r' x).1
    | (have h := hHM k r' x; simp only [Nset, Set.mem_setOf_eq] at h; exact h.1)
  have hphi0 := phiV'_one_add_zero_eq_first_basis_e0_vec k r'
  unfold oneStep
  rw [mul_assoc ((heis0 k r' x)⁻¹) (w0 k r' c) (ιLev k 1 r' g)]
  apply Dl_conj k (1 + r') l _ _ _ hn
    (fun b => herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x'.1))
    (fun b => herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x.1))
  · show herm (Hpk k (1 + r')) (phiV' k (1 + r') 0) (liftVec k 1 r' x'.1) = 0
    rw [hphi0]
    exact herm_first_lift_eq_zero k r' _
  · show herm (Hpk k (1 + r')) (phiV' k (1 + r') 0) (liftVec k 1 r' x.1) = 0
    rw [hphi0]
    exact herm_first_lift_eq_zero k r' _
  · intro b
    exact heis_phi' k r' hHA x' b
  · intro a
    exact heis_phi' k r' hHA x a

/- English proof (translation)
Rewrite using `[Fin.prod_univ_succ]`. Use `congr 1`. Conclude with `Fintype.prod_equiv (finCongr (by omega)) _ _ (fun l => congrArg F (Fin.ext (by simp [sc])))`.
-/
private lemma prod_fin_eq_zero_mul_prod_sc (F : Fin (1 + r' + 1) → ℝ≥0∞) :
    ∏ l, F l = F 0 * ∏ l : Fin (r' + 1), F (sc r' l) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact Fintype.prod_equiv (finCongr (by omega)) _ _ (fun l => congrArg F (Fin.ext (by simp [sc])))

/- English proof (translation)
Simplify using `only [FsE, Dl_oneStep k r' hHA hHM x x' c g]`. Rewrite using `[prod_fin_eq_zero_mul_prod_sc, prod_fin_eq_zero_mul_prod_sc]`. Simplify using `only [Dl_Y_zero, Dl_Y_sc, nnnorm_mul, ENNReal.coe_mul]`. Use `first`. Consider the case `simp only [ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]`.

Consider the case `simp only [ENNReal.coe_mul_rpow]`. Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FsE_oneStep (hHA : HeisAct) (hHM : HeisMem) (x x' : HPar k r') (c : ℂ) (g : Mat k r')
    (s : Fin (1 + r' + 1) → ℝ) :
    FsE k (1 + r') s (oneStep k r' x c g x') =
      (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * FsE k r' (fun l => s (sc r' l)) g := by
  simp only [FsE, Dl_oneStep k r' hHA hHM x x' c g]
  rw [prod_fin_eq_zero_mul_prod_sc, prod_fin_eq_zero_mul_prod_sc]
  simp only [Dl_Y_zero, Dl_Y_sc, nnnorm_mul, ENNReal.coe_mul]
  first
  | simp only [ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
  | simp only [ENNReal.coe_mul_rpow]
  rw [Finset.prod_mul_distrib]
  ring

end a1

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
