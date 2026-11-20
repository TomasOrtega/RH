import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Take `⟨hG, hC⟩` from `hX`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `inG at hG ⊢`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]`. Establish `ht : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`.

Rewrite using `[ht, ← smul_add, hG, smul_zero]`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hC]`.
-/
theorem inK_real_smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  obtain ⟨hG, hC⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at hG ⊢
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [ht, ← smul_add, hG, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hC]

def zM (a b : Fin n) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b c - Matrix.single b a (star c)

/- English proof (translation)
Establish `hd : ∀ i j, (i = a ∧ j = b) ∨ (i = b ∧ j = a) → (if ε i then (1 : ℂ) else -1) = if ε j then 1 else -1`. Apply the tactic sequence `rintro i j (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hab]`. Unfold `Jm`. Use extensionality with `i j`. Simplify using `only [Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Distinguish the cases in `hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a)`. Rewrite using `[hd i j hij, mul_comm]`. Establish `hz : zM a b c i j = 0`. Unfold `zM`. Simplify using `only [Matrix.sub_apply, Matrix.single_apply]`.

Use `push_neg at hij`. Rewrite using `[if_neg, if_neg, sub_zero]`. Conclude with `fun h => hij.2 h.1.symm h.2.symm`. Conclude with `fun h => hij.1 h.1.symm h.2.symm`. Rewrite using `[hz, mul_zero, zero_mul]`.
-/
theorem Jm_comm_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : Jm ε * zM a b c = zM a b c * Jm ε := by
  have hd : ∀ i j, (i = a ∧ j = b) ∨ (i = b ∧ j = a) →
      (if ε i then (1 : ℂ) else -1) = if ε j then 1 else -1 := by
    rintro i j (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hab]
  unfold Jm
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a)
  · rw [hd i j hij, mul_comm]
  · have hz : zM a b c i j = 0 := by
      unfold zM
      simp only [Matrix.sub_apply, Matrix.single_apply]
      push_neg at hij
      rw [if_neg, if_neg, sub_zero]
      · exact fun h => hij.2 h.1.symm h.2.symm
      · exact fun h => hij.1 h.1.symm h.2.symm
    rw [hz, mul_zero, zero_mul]

/- English proof (translation)
Establish `hH : (zM a b c)ᴴ = -zM a b c`. Use extensionality with `i j`. Establish `e1 : (a = j ∧ b = i) ↔ (b = i ∧ a = j)` using `and_comm`. Establish `e2 : (b = j ∧ a = i) ↔ (a = i ∧ b = j)` using `and_comm`. Simplify using `only [zM, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, e1, e2]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `⟨?_, (Jm_comm_zM hab c).symm⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[hH, Jm_comm_zM hab c, neg_mul, neg_add_cancel]`.
-/
theorem inK_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : inK ε (zM a b c) := by
  have hH : (zM a b c)ᴴ = -zM a b c := by
    ext i j
    have e1 : (a = j ∧ b = i) ↔ (b = i ∧ a = j) := and_comm
    have e2 : (b = j ∧ a = i) ↔ (a = i ∧ b = j) := and_comm
    simp only [zM, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, e1, e2]
    split_ifs <;> simp
  refine ⟨?_, (Jm_comm_zM hab c).symm⟩
  unfold inG
  rw [hH, Jm_comm_zM hab c, neg_mul, neg_add_cancel]

section Act

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Unfold `actM`. Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using `[Matrix.single_apply]`. Introduce `j _ hj`. Simplify using `[Matrix.single_apply, Ne.symm hj]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Simplify using `[Matrix.single_apply, Ne.symm hi]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `actM`. Simplify using `only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem actM_sub (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X - Y) = actM E X - actM E Y := by
  unfold actM
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Unfold `zM`. Rewrite using `[actM_sub, actM_single, actM_single]`.
-/
theorem actM_zM (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (zM a b c) = c • E a b - star c • E b a := by
  unfold zM
  rw [actM_sub, actM_single, actM_single]

end Act

section Rep

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}

/- English proof (translation)
Take `⟨hG, hC⟩` from `hX`. Establish `hJJ : Jm ε * Jm ε = 1`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hskew : Xᴴ = -X`. Establish `h1 : Xᴴ * Jm ε = -(X * Jm ε)`. Rewrite using `[hC]`.

Conclude with `eq_neg_of_add_eq_zero_left hG`. Combine the equalities or inequalities in the displayed calculation. Establish `ht : star (t : ℂ) = (t : ℂ)` using `Complex.conj_ofReal t`. Establish `hY : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X)`. Rewrite using `[Matrix.conjTranspose_smul, hskew, ht, smul_neg]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hY, ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X))), add_neg_cancel, NormedSpace.exp_zero]`. Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `hc : Commute ((t : ℂ) • X) (Jm ε)` using `by show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)`.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hC]`. Conclude with `hc.exp_left.eq`.
-/
private theorem exp_smul_mem_Kset_of_skew_of_commute_Jm {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  obtain ⟨hG, hC⟩ := hX
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(X * Jm ε) * Jm ε := by rw [h1]
      _ = -X := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hY : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hskew, ht, smul_neg]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hY,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X))), add_neg_cancel,
      NormedSpace.exp_zero]
  · letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    have hc : Commute ((t : ℂ) • X) (Jm ε) := by
      show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hC]
    exact hc.exp_left.eq

/- English proof (translation)
Establish `hk : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε` using `fun t => exp_smul_mem_Kset_of_skew_of_commute_Jm hX t`. Use `choose w hwV hw using fun t : ℝ => hVK₁ _ (hk t) (v : D₁) v.2`. Set `W : ℝ → V₁` to `fun t => ⟨w t, hwV t⟩`. Establish `hW : ∀ t, (((W t : V₁) : D₁) : H₁) = σ₁ (NormedSpace.exp ((t : ℂ) • X)) ((v : D₁) : H₁)` using `hw`. Establish `h1 : HasDerivAt (fun t : ℝ => (((W t : V₁) : D₁) : H₁)) (((u : V₁) : D₁) : H₁) 0`.

Establish `hd` using `hD₁.deriv X hX.1 (v : D₁)`. Rewrite `hd` using `[← hu]`. Conclude with `hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hW t)`. Establish `h2 : HasDerivAt W u 0`. Rewrite `h1`, the goal using `[hasDerivAt_iff_isLittleO_nhds_zero]`.

Rewrite `h1`, the goal using `[← Asymptotics.isLittleO_norm_left]`. Conclude with `h1.congr_left (fun h => rfl)`. Set `L : V₁ →L[ℂ] H₂` to `LinearMap.toContinuousLinearMap ((D₂.subtype.comp V₂.subtype).comp φ)`. Establish `h3 : HasDerivAt (fun t => L (W t)) (L u) 0` using `(L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2`. Establish `h4 : (fun t => L (W t)) = fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (((φ v : V₂) : D₂) : H₂)`.

Use function extensionality and compare the values at `t`. Conclude with `hφK _ (hk t) v (W t) (hW t)`. Rewrite `h3` using `[h4]`. Conclude with `(hD₂.deriv X hX.1 ((φ v : V₂) : D₂)).unique h3`.
-/
theorem phi_actM_inK (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁]
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (v u : V₁) (hu : (u : D₁) = actM E₁ X v) :
    ((actM E₂ X ((φ v : V₂) : D₂) : D₂) : H₂) = (((φ u : V₂) : D₂) : H₂) := by
  classical
  have hk : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t => exp_smul_mem_Kset_of_skew_of_commute_Jm hX t
  choose w hwV hw using fun t : ℝ => hVK₁ _ (hk t) (v : D₁) v.2
  let W : ℝ → V₁ := fun t => ⟨w t, hwV t⟩
  have hW : ∀ t, (((W t : V₁) : D₁) : H₁) = σ₁ (NormedSpace.exp ((t : ℂ) • X)) ((v : D₁) : H₁) := hw
  have h1 : HasDerivAt (fun t : ℝ => (((W t : V₁) : D₁) : H₁)) (((u : V₁) : D₁) : H₁) 0 := by
    have hd := hD₁.deriv X hX.1 (v : D₁)
    rw [← hu] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hW t)
  have h2 : HasDerivAt W u 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h1 ⊢
    rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
    exact h1.congr_left (fun h => rfl)
  let L : V₁ →L[ℂ] H₂ := LinearMap.toContinuousLinearMap ((D₂.subtype.comp V₂.subtype).comp φ)
  have h3 : HasDerivAt (fun t => L (W t)) (L u) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h4 : (fun t => L (W t)) =
      fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (((φ v : V₂) : D₂) : H₂) := by
    funext t
    exact hφK _ (hk t) v (W t) (hW t)
  rw [h4] at h3
  exact (hD₂.deriv X hX.1 ((φ v : V₂) : D₂)).unique h3

/- English proof (translation)
Rewrite using `[smul_sub Complex.I, smul_smul, smul_smul, Complex.I_mul_I, mul_neg, Complex.I_mul_I, neg_neg, neg_one_smul, one_smul]`. Rewrite using `[show (A - B) - (-A - B) = (2 : ℂ) • A by module, smul_smul]`. Evaluate the numerical expressions.
-/
private theorem eq_half_smul_sub_I_smul_combo {M : Type*} [AddCommGroup M] [Module ℂ M] (A B : M) :
    A = (1 / 2 : ℂ) • ((A - B) - Complex.I • (Complex.I • A - (-Complex.I) • B)) := by
  rw [smul_sub Complex.I, smul_smul, smul_smul, Complex.I_mul_I, mul_neg, Complex.I_mul_I, neg_neg,
    neg_one_smul, one_smul]
  rw [show (A - B) - (-A - B) = (2 : ℂ) • A by module, smul_smul]
  norm_num

/- English proof (translation)
Establish `hmem : ∀ c : ℂ, c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁) ∈ V₁` using `fun c => V₁.sub_mem (V₁.smul_mem _ (hst a b hab _ v.2)) (V₁.smul_mem _ (hst b a hab.symm _ v.2))`. Set `wc : ℂ → V₁` to `fun c => ⟨c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁), hmem c⟩`. Establish `key : ∀ c : ℂ, c • E₂ a b ((φ v : V₂) : D₂) - star c • E₂ b a ((φ v : V₂) : D₂) = ((φ (wc c) : V₂) : D₂)`. Introduce `c`. Establish `h` using `phi_actM_inK hD₁ hD₂ hVK₁ φ hφK (inK_zM hab c) v (wc c) (by rw [actM_zM]; rfl)`.

Rewrite `h` using `[actM_zM, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply]`. Conclude with `Subtype.ext h`. Establish `hw0 : (⟨E₁ a b v, hst a b hab _ v.2⟩ : V₁) = (1 / 2 : ℂ) • (wc 1 - Complex.I • wc Complex.I)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show E₁ a b (v : D₁) = (1 / 2 : ℂ) • (((1 : ℂ) • E₁ a b (v : D₁) - star (1 : ℂ) • E₁ b a (v : D₁)) - Complex.I • (Complex.I • E₁ a b (v : D₁) - star Complex.I • E₁ b a (v : D₁)))`.

Rewrite using `[star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]`. Conclude with `eq_half_smul_sub_I_smul_combo _ _`. Rewrite using `[hw0, map_smul, map_sub, map_smul]`. Use `show E₂ a b ((φ v : V₂) : D₂) = (1 / 2 : ℂ) • (((φ (wc 1) : V₂) : D₂) - Complex.I • ((φ (wc Complex.I) : V₂) : D₂))`. Rewrite using `[← key 1, ← key Complex.I, star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]`.

Conclude with `eq_half_smul_sub_I_smul_combo _ _`.
-/
theorem phi_E_comm (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁] (hst : IsKStableSub ε E₁ V₁)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂) := by
  have hmem : ∀ c : ℂ, c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁) ∈ V₁ := fun c =>
    V₁.sub_mem (V₁.smul_mem _ (hst a b hab _ v.2)) (V₁.smul_mem _ (hst b a hab.symm _ v.2))
  let wc : ℂ → V₁ := fun c => ⟨c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁), hmem c⟩
  have key : ∀ c : ℂ, c • E₂ a b ((φ v : V₂) : D₂) - star c • E₂ b a ((φ v : V₂) : D₂) =
      ((φ (wc c) : V₂) : D₂) := by
    intro c
    have h := phi_actM_inK hD₁ hD₂ hVK₁ φ hφK (inK_zM hab c) v (wc c) (by rw [actM_zM]; rfl)
    rw [actM_zM, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply] at h
    exact Subtype.ext h
  have hw0 : (⟨E₁ a b v, hst a b hab _ v.2⟩ : V₁) = (1 / 2 : ℂ) • (wc 1 - Complex.I • wc Complex.I) := by
    apply Subtype.ext
    show E₁ a b (v : D₁) = (1 / 2 : ℂ) • (((1 : ℂ) • E₁ a b (v : D₁) - star (1 : ℂ) • E₁ b a (v : D₁)) -
      Complex.I • (Complex.I • E₁ a b (v : D₁) - star Complex.I • E₁ b a (v : D₁)))
    rw [star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
    exact eq_half_smul_sub_I_smul_combo _ _
  rw [hw0, map_smul, map_sub, map_smul]
  show E₂ a b ((φ v : V₂) : D₂) =
    (1 / 2 : ℂ) • (((φ (wc 1) : V₂) : D₂) - Complex.I • ((φ (wc Complex.I) : V₂) : D₂))
  rw [← key 1, ← key Complex.I, star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
  exact eq_half_smul_sub_I_smul_combo _ _

end Rep

end USum

end ReciprocityTheory.ChartRestriction.DS
