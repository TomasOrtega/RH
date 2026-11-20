import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Establish `hone : ∀ p q : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) p q‖ ≤ c`. Introduce `p q`. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [hc, zero_le_one.trans hc]`. Use `show ‖((emb e g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c`.

Rewrite using `[coe_emb, Matrix.add_apply]`. Distinguish the cases in `hi : ∃ k, i = e k`. Distinguish the cases in `hj : ∃ l, j = e l`. Take `⟨k, rfl⟩` from `hi`. Take `⟨l, rfl⟩` from `hj`.

Simplify using `only [matrixExtendByZero_apply, Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, add_sub_cancel]`. Conclude with `h k l`. Use `push_neg at hj`. Rewrite using `[matrixExtendByZero_apply_of_outside_col e _ i hj, add_zero]`. Conclude with `hone i j`.

Use `push_neg at hi`. Rewrite using `[extendByZero_apply_eq_zero_of_row_not_mem e _ hi, add_zero]`. Conclude with `hone i j`.
-/
private theorem ent_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) {c : ℝ}
    (hc : 1 ≤ c) (h : ∀ i j, ‖g.val i j‖ ≤ c) (i j : Fin n) : ‖(emb e g).val i j‖ ≤ c := by
  have hone : ∀ p q : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) p q‖ ≤ c := by
    intro p q
    rw [Matrix.one_apply]
    split_ifs <;> simp [hc, zero_le_one.trans hc]
  show ‖((emb e g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c
  rw [coe_emb, Matrix.add_apply]
  by_cases hi : ∃ k, i = e k
  · by_cases hj : ∃ l, j = e l
    · obtain ⟨k, rfl⟩ := hi
      obtain ⟨l, rfl⟩ := hj
      simp only [matrixExtendByZero_apply, Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, add_sub_cancel]
      exact h k l
    · push_neg at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ i hj, add_zero]
      exact hone i j
  · push_neg at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, add_zero]
    exact hone i j

/- English proof (translation)
Apply `locHeight_le (one_le_locHeight g)` to reduce the goal to its premises. Conclude with `ent_le e g (one_le_locHeight g) (norm_apply_le_locHeight g)`. Introduce `i j`. Rewrite using `[← map_inv]`. Conclude with `ent_le e g⁻¹ (one_le_locHeight g) (norm_inv_apply_le_locHeight g) i j`.
-/
private theorem loc_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) :
    locHeight (emb e g) ≤ locHeight g := by
  apply locHeight_le (one_le_locHeight g)
  · exact ent_le e g (one_le_locHeight g) (norm_apply_le_locHeight g)
  · intro i j
    rw [← map_inv]
    exact ent_le e g⁻¹ (one_le_locHeight g) (norm_inv_apply_le_locHeight g) i j

/- English proof (translation)
Introduce `K _ _ a n e g`. Establish `hfin : ∀ v, Reduction.finAt v (emb e g) = emb e (Reduction.finAt v g)`. Introduce `v`. Use `show Matrix.GeneralLinearGroup.map (Reduction.finEval v) (emb e g) = _`. Rewrite using `[emb_map]`.

Both sides reduce to the same expression. Establish `hinf : ∀ w, Reduction.infAt w (emb e g) = emb e (Reduction.infAt w g)`. Introduce `w`. Use `show Matrix.GeneralLinearGroup.map (Reduction.infEval w) (emb e g) = _`. Rewrite using `[emb_map]`.

Both sides reduce to the same expression. Unfold `AutomorphicForm.height`. Simplify using `only [hfin, hinf]`. Apply `mul_le_mul` to reduce the goal to its premises. Apply `Finset.prod_le_prod` to reduce the goal to its premises.

Introduce `w _`. Conclude with `pow_nonneg (locHeight_pos _).le _`. Introduce `w _`. Conclude with `pow_le_pow_left₀ (locHeight_pos _).le (loc_le e _) _`. Establish `h1` using `finite_mulSupport_locHeight_finAt (emb e g)`.

Establish `h2` using `finite_mulSupport_locHeight_finAt g`. Simplify using `only [hfin] at h1`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset) (by intro x hx; simp [hx]), finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset) (by intro x hx; simp [hx])]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `v _`.

Conclude with `(locHeight_pos _).le`. Introduce `v _`. Conclude with `loc_le e _`. Conclude with `finprod_nonneg fun v => (locHeight_pos _).le`. Conclude with `(zero_lt_one.trans_le (one_le_prod_locHeight g)).le`.
-/
theorem UpperTheory.height_blockEmbedding_le :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K a), AutomorphicForm.height (emb e g) ≤ AutomorphicForm.height g := by
  classical
  intro K _ _ a n e g
  have hfin : ∀ v, Reduction.finAt v (emb e g) = emb e (Reduction.finAt v g) := by
    intro v
    show Matrix.GeneralLinearGroup.map (Reduction.finEval v) (emb e g) = _
    rw [emb_map]
    rfl
  have hinf : ∀ w, Reduction.infAt w (emb e g) = emb e (Reduction.infAt w g) := by
    intro w
    show Matrix.GeneralLinearGroup.map (Reduction.infEval w) (emb e g) = _
    rw [emb_map]
    rfl
  unfold AutomorphicForm.height
  simp only [hfin, hinf]
  apply mul_le_mul
  · apply Finset.prod_le_prod
    · intro w _
      exact pow_nonneg (locHeight_pos _).le _
    · intro w _
      exact pow_le_pow_left₀ (locHeight_pos _).le (loc_le e _) _
  · have h1 := finite_mulSupport_locHeight_finAt (emb e g)
    have h2 := finite_mulSupport_locHeight_finAt g
    simp only [hfin] at h1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx]),
      finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx])]
    apply Finset.prod_le_prod
    · intro v _
      exact (locHeight_pos _).le
    · intro v _
      exact loc_le e _
  · exact finprod_nonneg fun v => (locHeight_pos _).le
  · exact (zero_lt_one.trans_le (one_le_prod_locHeight g)).le
