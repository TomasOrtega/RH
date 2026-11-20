import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

/- English proof (translation)
Establish `h : ‖∏ i, (g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ locHeight g ^ n`. Rewrite using `[norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]`. Rewrite using `[one_smul]` and apply the resulting hypothesis.

Rewrite using `[Units.neg_smul, one_smul, norm_neg]` and apply the resulting hypothesis.
-/
private theorem UpperTheory.V.Fb.norm_term_le {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E)
    (σ : Equiv.Perm (Fin n)) :
    ‖Equiv.Perm.sign σ • ∏ i, (g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ locHeight g ^ n := by
  have h : ‖∏ i, (g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ locHeight g ^ n := by
    rw [norm_prod]
    calc ∏ i, ‖(g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ ∏ _i : Fin n, locHeight g :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_apply_le_locHeight g _ _
      _ = locHeight g ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `(norm_sum_le _ _).trans ((Finset.sum_le_sum fun σ _ => norm_term_le g σ).trans ?_)` and prove the remaining obligations. Simplify using `[Fintype.card_perm]`.
-/
private theorem UpperTheory.V.Fb.norm_det_le_arch {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) :
    ‖(g : Matrix (Fin n) (Fin n) E).det‖ ≤ n.factorial * locHeight g ^ n := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun σ _ => norm_term_le g σ).trans ?_)
  simp [Fintype.card_perm]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_pos (locHeight_pos g) n).le fun σ _ => norm_term_le g σ`.
-/
private theorem UpperTheory.V.Fb.norm_det_le_ultra {E : Type*} [NormedField E] [IsUltrametricDist E] {n : ℕ}
    (g : GL (Fin n) E) : ‖(g : Matrix (Fin n) (Fin n) E).det‖ ≤ locHeight g ^ n := by
  rw [Matrix.det_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_pos (locHeight_pos g) n).le
    fun σ _ => norm_term_le g σ

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction IsDedekindDomain in
/- English proof (translation)
Introduce `K _ _ n`. Use `⟨∏ w : InfinitePlace K, (n.factorial : ℝ) ^ w.mult, n, Finset.prod_pos fun w _ => pow_pos (by exact_mod_cast n.factorial_pos) _, fun g => ?_⟩` and prove the remaining obligations. Establish `hi : ∀ w : InfinitePlace K, ((AdelicGLn.det K n g : AdeleRing (𝓞 K) K)).1 w = (infAt w g : Matrix (Fin n) (Fin n) w.Completion).det` using `fun w => by`. Rewrite using `[AdelicGLn.coe_det, ← infEval_apply, RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hf : ∀ v : HeightOneSpectrum (𝓞 K), ((AdelicGLn.det K n g : AdeleRing (𝓞 K) K)).2 v = (finAt v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)).det` using `fun v => by`. Rewrite using `[AdelicGLn.coe_det, ← finEval_apply, RingHom.map_det]`. Both sides reduce to the same expression. Establish `h1` using `finite_mulSupport_norm (AdelicGLn.det K n g)`. Establish `h2` using `finite_mulSupport_locHeight_finAt g`.

Establish `e1` using `finprod_eq_prod_of_mulSupport_subset _ (s := (h1.union h2).toFinset) (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl hv)`. Establish `e2` using `finprod_eq_prod_of_mulSupport_subset _ (s := (h1.union h2).toFinset) (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inr hv)`. Rewrite using `[ideleModule_eq, AutomorphicForm.height, e1, e2, mul_pow, ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `mul_le_mul (Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => ?_) (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun w _ => by have := locHeight_pos (infAt w g); positivity)` and prove the remaining obligations. Rewrite using `[hi, ← pow_mul, mul_comm w.mult n, pow_mul, ← mul_pow]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_arch _) _`. Rewrite using `[hf]`. Conclude with `norm_det_le_ultra _`.
-/
theorem UpperTheory.adelicNorm_det_le_height_pow :
    UpperTheory.V.Fb.DetBound := by
  classical
  intro K _ _ n
  refine ⟨∏ w : InfinitePlace K, (n.factorial : ℝ) ^ w.mult, n,
    Finset.prod_pos fun w _ => pow_pos (by exact_mod_cast n.factorial_pos) _, fun g => ?_⟩
  have hi : ∀ w : InfinitePlace K, ((AdelicGLn.det K n g : AdeleRing (𝓞 K) K)).1 w =
      (infAt w g : Matrix (Fin n) (Fin n) w.Completion).det := fun w => by
    rw [AdelicGLn.coe_det, ← infEval_apply, RingHom.map_det]; rfl
  have hf : ∀ v : HeightOneSpectrum (𝓞 K), ((AdelicGLn.det K n g : AdeleRing (𝓞 K) K)).2 v =
      (finAt v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)).det := fun v => by
    rw [AdelicGLn.coe_det, ← finEval_apply, RingHom.map_det]; rfl
  have h1 := finite_mulSupport_norm (AdelicGLn.det K n g)
  have h2 := finite_mulSupport_locHeight_finAt g
  have e1 := finprod_eq_prod_of_mulSupport_subset _ (s := (h1.union h2).toFinset)
    (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl hv)
  have e2 := finprod_eq_prod_of_mulSupport_subset _ (s := (h1.union h2).toFinset)
    (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inr hv)
  rw [ideleModule_eq, AutomorphicForm.height, e1, e2, mul_pow, ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => ?_)
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by have := locHeight_pos (infAt w g); positivity)
  · rw [hi, ← pow_mul, mul_comm w.mult n, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_arch _) _
  · rw [hf]; exact norm_det_le_ultra _
