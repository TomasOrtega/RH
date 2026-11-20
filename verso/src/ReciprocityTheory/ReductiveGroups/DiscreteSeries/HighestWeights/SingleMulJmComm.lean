import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OpEqExp

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Take `⟨-, h2⟩` from `hY`. Establish `h` using `congrFun (congrFun h2 a) b`. Unfold `Jm at h`. Rewrite `h` using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h <;> first`.

Consider the case `exact h`. Consider the case `linear_combination (1 / 2 : ℂ) * h`. Consider the case `linear_combination (-1 / 2 : ℂ) * h`.
-/
theorem inK_entry_eq_zero {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    {a b : Fin n} (hab : ε a ≠ ε b) : Y a b = 0 := by
  obtain ⟨-, h2⟩ := hY
  have h := congrFun (congrFun h2 a) b
  unfold Jm at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h <;>
    first
    | exact h
    | linear_combination (1 / 2 : ℂ) * h
    | linear_combination (-1 / 2 : ℂ) * h

/- English proof (translation)
Unfold `Jm`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hi : a = i`. Distinguish the cases in `hj : b = j`.

Substitute `hi` using the available equality. Substitute `hj` using the available equality. Simplify using `only [hab]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.single_apply, hj]`.

Simplify using `[Matrix.single_apply, hi]`.
-/
theorem single_mul_Jm_comm {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) (c : ℂ) :
    Matrix.single a b c * Jm ε = Jm ε * Matrix.single a b c := by
  unfold Jm
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : a = i
  · by_cases hj : b = j
    · subst hi
      subst hj
      simp only [hab]
      ring
    · simp [Matrix.single_apply, hj]
  · simp [Matrix.single_apply, hi]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro v hv`. Simplify using `using hv`. Consider the case `succ k ih`. Introduce `v hv`.

Rewrite using `[pow_succ', ContinuousLinearMap.mul_apply]`. Conclude with `hA _ (ih v hv)`.
-/
private theorem pow_mem_lemma {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (W : Submodule ℂ V) (A : V →L[ℂ] V) (hA : ∀ v ∈ W, A v ∈ W) (k : ℕ) :
    ∀ v ∈ W, (A ^ k) v ∈ W := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact hA _ (ih v hv)

/- English proof (translation)
Introduce `v hv`. Establish `hs` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V v)`. Use `(Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs.tendsto_sum_nat (Filter.Eventually.of_forall fun m => ?_)` and prove the remaining obligations. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply]`.

Conclude with `W.smul_mem _ (pow_mem_lemma W A hA k v hv)`.
-/
theorem exp_mem_of_stable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ V) (A : V →L[ℂ] V) (hA : ∀ v ∈ W, A v ∈ W) :
    ∀ v ∈ W, NormedSpace.exp A v ∈ W := by
  intro v hv
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL
    (ContinuousLinearMap.apply ℂ V v)
  refine (Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs.tendsto_sum_nat
    (Filter.Eventually.of_forall fun m => ?_)
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply]
  exact W.smul_mem _ (pow_mem_lemma W A hA k v hv)

/- English proof (translation)
Unfold `inK inG`. Use `⟨?_, h2⟩` and prove the remaining obligations. Rewrite using `[h1, ← h2, neg_mul, neg_add_cancel]`.
-/
theorem inK_of_skew_comm {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h1 : Xᴴ = -X)
    (h2 : X * Jm ε = Jm ε * X) : inK ε X := by
  unfold inK inG
  refine ⟨?_, h2⟩
  rw [h1, ← h2, neg_mul, neg_add_cancel]

/- English proof (translation)
Establish `hstab : ∀ Y, inK ε Y → ∀ v ∈ W, T.dτ Y v ∈ W`. Introduce `Y hY v hv`. Rewrite using `[Matrix.matrix_eq_sum_single Y, map_sum, ContinuousLinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, ContinuousLinearMap.sum_apply]`.

Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hab : ε a = ε b`. Establish `hs : Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ)`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hs, map_smul, ContinuousLinearMap.smul_apply]`.

Conclude with `W.smul_mem _ (hW a b hab v hv)`. Simplify using `[inK_entry_eq_zero hY hab]`. Use `T.irred W fun k v hv => ?_` and prove the remaining obligations. Take `⟨Y, hY, hop⟩` from `ReciprocityTheory.ChartRestriction.DS.HW.KType.op_eq_exp T k`. Express the relevant statement in the definitionally equal form `T.op k v ∈ W`.

Rewrite using `[hop]`. Conclude with `exp_mem_of_stable W (T.dτ Y) (hstab Y hY) v hv`.
-/
theorem KType.dτ_irred {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (W : Submodule ℂ T.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, T.dτ (Matrix.single a b 1) v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hstab : ∀ Y, inK ε Y → ∀ v ∈ W, T.dτ Y v ∈ W := by
    intro Y hY v hv
    rw [Matrix.matrix_eq_sum_single Y, map_sum, ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hab : ε a = ε b
    · have hs : Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, ContinuousLinearMap.smul_apply]
      exact W.smul_mem _ (hW a b hab v hv)
    · simp [inK_entry_eq_zero hY hab]
  refine T.irred W fun k v hv => ?_
  obtain ⟨Y, hY, hop⟩ := ReciprocityTheory.ChartRestriction.DS.HW.KType.op_eq_exp T k
  change T.op k v ∈ W
  rw [hop]
  exact exp_mem_of_stable W (T.dτ Y) (hstab Y hY) v hv

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.single_apply]`. Apply the tactic sequence `by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]`.
-/
private theorem single_conjTranspose_lemma_2 {a b : Fin n} :
    (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]

/- English proof (translation)
Establish `key : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X → ∀ v ∈ W, T.dτ X v ∈ W`. Introduce `X h1 h2 v hv`. Establish `hc : Commute (Jm ε) X` using `h2.symm`. Establish `hcomm : ∀ s : ℂ, Commute (Jm ε) (NormedSpace.exp (s • X))` using `fun s => (hc.smul_right s).exp_right`. Establish `hinv : ∀ s : ℂ, NormedSpace.exp (s • X) * NormedSpace.exp (-(s • X)) = 1 ∧ NormedSpace.exp (-(s • X)) * NormedSpace.exp (s • X) = 1` using `fun s => ⟨by rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_right), add_neg_cancel, NormedSpace.exp_zero], by rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_left), neg_add_cancel, NormedSpace.exp_zero]⟩`.

Establish `hstar : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (-((t : ℂ) • X))`. Introduce `t`. Establish `ht : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h1, ht, smul_neg]`. Set `γ : ℝ → KG ε` to `fun t => ⟨⟨⟨NormedSpace.exp ((t : ℂ) • X), NormedSpace.exp (-((t : ℂ) • X)), (hinv t).1, (hinv t).2⟩, by show inUJ ε (NormedSpace.exp ((t : ℂ) • X))`.

Unfold `inUJ`. Rewrite using `[hstar t, mul_assoc, (hcomm t).eq, ← mul_assoc, (hinv t).2, one_mul]⟩, by`. Use `show NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X)`. Use `⟨?_, (hcomm t).eq.symm⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hstar t]`.

Conclude with `(hinv t).1⟩`. Establish `hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)` using `fun t => rfl`. Establish `hd` using `T.hasDeriv X (inK_of_skew_comm h1 h2) γ hγ`. Establish `hs` using `((ContinuousLinearMap.apply ℂ T.V v).continuous.tendsto _).comp (hasDerivAt_iff_tendsto_slope.mp hd)`. Use `(Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, ContinuousLinearMap.apply_apply, slope_def_module, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, SetLike.mem_coe]`. Conclude with `W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))`. Introduce `a b hab v hv`. Generalize the expression as in `hY : Matrix.single a b (1 : ℂ) = Y at hv ⊢`. Establish `hYc : Y * Jm ε = Jm ε * Y` using `by rw [← hY]; exact single_mul_Jm_comm hab 1`.

Establish `hYH : Yᴴ = Matrix.single b a 1` using `by rw [← hY]; exact single_conjTranspose_lemma_2`. Establish `hYHc : Yᴴ * Jm ε = Jm ε * Yᴴ` using `by rw [hYH]; exact single_mul_Jm_comm hab.symm 1`. Establish `hc : star ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ)` using `Complex.conj_ofReal _`. Establish `hI : star Complex.I = -Complex.I` using `Complex.conj_I`. Establish `h1 : (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ))ᴴ = -(((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ))`.

Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hc, ← neg_sub Y Yᴴ, smul_neg]`. Establish `h2 : (Complex.I • (Y + Yᴴ))ᴴ = -(Complex.I • (Y + Yᴴ))`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, hI, neg_smul, add_comm]`. Establish `h1J : (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) * Jm ε = Jm ε * (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ))`. Rewrite using `[smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hYc, hYHc]`.

Establish `h2J : (Complex.I • (Y + Yᴴ)) * Jm ε = Jm ε * (Complex.I • (Y + Yᴴ))`. Rewrite using `[smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hYc, hYHc]`. Establish `hdec : Y = ((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ) + (-(Complex.I / 2)) • (Complex.I • (Y + Yᴴ))`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`.

Use `push_cast`. Take the linear combination `((Y i j + Yᴴ i j) / 2) * Complex.I_sq`. Rewrite using `[hdec, map_add, ContinuousLinearMap.add_apply, map_smul T.dτ (-(Complex.I / 2)) (Complex.I • (Y + Yᴴ)), ContinuousLinearMap.smul_apply]`. Conclude with `W.add_mem (key _ h1 h1J v hv) (W.smul_mem _ (key _ h2 h2J v hv))`.
-/
theorem KType.dτ_stable_of_stable {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (W : Submodule ℂ T.V) (hW : ∀ k : KG ε, ∀ v ∈ W, T.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, T.dτ (Matrix.single a b 1) v ∈ W := by
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X →
      ∀ v ∈ W, T.dτ X v ∈ W := by
    intro X h1 h2 v hv
    have hc : Commute (Jm ε) X := h2.symm
    have hcomm : ∀ s : ℂ, Commute (Jm ε) (NormedSpace.exp (s • X)) := fun s =>
      (hc.smul_right s).exp_right
    have hinv : ∀ s : ℂ, NormedSpace.exp (s • X) * NormedSpace.exp (-(s • X)) = 1 ∧
        NormedSpace.exp (-(s • X)) * NormedSpace.exp (s • X) = 1 := fun s =>
      ⟨by rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_right), add_neg_cancel,
          NormedSpace.exp_zero],
       by rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_left), neg_add_cancel,
          NormedSpace.exp_zero]⟩
    have hstar : ∀ t : ℝ,
        (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (-((t : ℂ) • X)) := by
      intro t
      have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h1, ht, smul_neg]
    let γ : ℝ → KG ε := fun t =>
      ⟨⟨⟨NormedSpace.exp ((t : ℂ) • X), NormedSpace.exp (-((t : ℂ) • X)), (hinv t).1,
          (hinv t).2⟩, by
        show inUJ ε (NormedSpace.exp ((t : ℂ) • X))
        unfold inUJ
        rw [hstar t, mul_assoc, (hcomm t).eq, ← mul_assoc, (hinv t).2, one_mul]⟩, by
        show NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X)
        refine ⟨?_, (hcomm t).eq.symm⟩
        rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hstar t]
        exact (hinv t).1⟩
    have hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hd := T.hasDeriv X (inK_of_skew_comm h1 h2) γ hγ
    have hs := ((ContinuousLinearMap.apply ℂ T.V v).continuous.tendsto _).comp
      (hasDerivAt_iff_tendsto_slope.mp hd)
    refine (Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, slope_def_module,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, SetLike.mem_coe]
    exact W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  generalize hY : Matrix.single a b (1 : ℂ) = Y at hv ⊢
  have hYc : Y * Jm ε = Jm ε * Y := by rw [← hY]; exact single_mul_Jm_comm hab 1
  have hYH : Yᴴ = Matrix.single b a 1 := by rw [← hY]; exact single_conjTranspose_lemma_2
  have hYHc : Yᴴ * Jm ε = Jm ε * Yᴴ := by rw [hYH]; exact single_mul_Jm_comm hab.symm 1
  have hc : star ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have h1 : (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ))ᴴ = -(((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hc, ← neg_sub Y Yᴴ, smul_neg]
  have h2 : (Complex.I • (Y + Yᴴ))ᴴ = -(Complex.I • (Y + Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hI, neg_smul, add_comm]
  have h1J : (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) * Jm ε = Jm ε * (((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ)) := by
    rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hYc, hYHc]
  have h2J : (Complex.I • (Y + Yᴴ)) * Jm ε = Jm ε * (Complex.I • (Y + Yᴴ)) := by
    rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hYc, hYHc]
  have hdec : Y = ((1 / 2 : ℝ) : ℂ) • (Y - Yᴴ) + (-(Complex.I / 2)) • (Complex.I • (Y + Yᴴ)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    linear_combination ((Y i j + Yᴴ i j) / 2) * Complex.I_sq
  rw [hdec, map_add, ContinuousLinearMap.add_apply,
    map_smul T.dτ (-(Complex.I / 2)) (Complex.I • (Y + Yᴴ)), ContinuousLinearMap.smul_apply]
  exact W.add_mem (key _ h1 h1J v hv) (W.smul_mem _ (key _ h2 h2J v hv))

end ReciprocityTheory.ChartRestriction.DS.HW
