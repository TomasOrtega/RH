import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd

/- English proof (translation)
Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `x`. Take `⟨y, rfl⟩ : ∃ y, x = c * y` from `⟨c⁻¹ * x, by field_simp⟩`. Rewrite using `[scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]`. Use `congr 1`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.scalar_apply, h, mul_sub]`.
-/
private theorem charpoly_smul' {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by field_simp⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h, mul_sub]

/- English proof (translation)
Proceed by induction on `m using Finset.induction_on with`. Consider the case `empty => simp [one_scaleRoots]`. Consider the case `insert j m hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]`.
-/
private theorem scaleRoots_prod' {K ι : Type} [Field K] (m : Finset ι) (a : ι → K) (s : K) :
    (∏ j ∈ m, (X - C (a j))).scaleRoots s = ∏ j ∈ m, (X - C (a j * s)) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp [one_scaleRoots]
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.
-/
private theorem sub_le' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/- English proof (translation)
Proceed by induction on `m using Finset.induction_on with`. Consider the case `empty`. Introduce `i`. Simplify using `only [Finset.prod_empty, sub_self, norm_zero, zero_lt_one, and_true, coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `insert j m hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj]`. Use `set p := ∏ j ∈ m, (X - C (a j))`. Use `set q := ∏ j ∈ m, (X - C (b j))`. Establish `hb : ‖b j‖ ≤ 1`.

Use `IsUltrametricDist.norm_add_le_max (b j - a j) (a j)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.trans (max_le (hab j).le (ha j))`. Establish `h1 : ∀ i, ‖a j * p.coeff i‖ ≤ 1` using `fun i => by`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ (ha j) (norm_nonneg _) (ih i).1`. Establish `h2 : ∀ i, ‖a j * p.coeff i - b j * q.coeff i‖ < 1` using `fun i => by`. Establish `e : a j * p.coeff i - b j * q.coeff i = b j * (p.coeff i - q.coeff i) - (b j - a j) * p.coeff i` using `by ring`. Rewrite using `[e]`. Apply the tactic sequence `refine (sub_le' _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul]`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) (ih i).2`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hab j) (ih i).1`. Introduce `i`. Consider the cases of `i with`. Consider the case `zero`.

Simplify using `only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub, norm_neg]`. Use `⟨h1 0, ?_⟩` and prove the remaining obligations. Rewrite using `[neg_sub_neg, norm_sub_rev]`. Conclude with `h2 0`. Consider the case `succ i`.

Simplify using `only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]`. Use `⟨(sub_le' _ _).trans (max_le (ih i).1 (h1 _)), ?_⟩` and prove the remaining obligations. Rewrite using `[sub_sub_sub_comm]`. Conclude with `(sub_le' _ _).trans_lt (max_lt (ih i).2 (h2 _))`.
-/
private theorem prod_cong {K ι : Type} [NormedField K] [IsUltrametricDist K] (m : Finset ι) (a b : ι → K)
    (ha : ∀ j, ‖a j‖ ≤ 1) (hab : ∀ j, ‖b j - a j‖ < 1) :
    ∀ i, ‖(∏ j ∈ m, (X - C (a j))).coeff i‖ ≤ 1 ∧
      ‖(∏ j ∈ m, (X - C (a j))).coeff i - (∏ j ∈ m, (X - C (b j))).coeff i‖ < 1 := by
  classical
  induction m using Finset.induction_on with
  | empty =>
    intro i
    simp only [Finset.prod_empty, sub_self, norm_zero, zero_lt_one, and_true, coeff_one]
    split_ifs <;> simp
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    set p := ∏ j ∈ m, (X - C (a j))
    set q := ∏ j ∈ m, (X - C (b j))
    have hb : ‖b j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (b j - a j) (a j)
      rw [sub_add_cancel] at this
      exact this.trans (max_le (hab j).le (ha j))
    have h1 : ∀ i, ‖a j * p.coeff i‖ ≤ 1 := fun i => by
      rw [norm_mul]; exact mul_le_one₀ (ha j) (norm_nonneg _) (ih i).1
    have h2 : ∀ i, ‖a j * p.coeff i - b j * q.coeff i‖ < 1 := fun i => by
      have e : a j * p.coeff i - b j * q.coeff i = b j * (p.coeff i - q.coeff i) - (b j - a j) * p.coeff i := by ring
      rw [e]
      refine (sub_le' _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) (ih i).2
      · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hab j) (ih i).1
    intro i
    cases i with
    | zero =>
      simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub, norm_neg]
      refine ⟨h1 0, ?_⟩
      rw [neg_sub_neg, norm_sub_rev]
      exact h2 0
    | succ i =>
      simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      refine ⟨(sub_le' _ _).trans (max_le (ih i).1 (h1 _)), ?_⟩
      rw [sub_sub_sub_comm]
      exact (sub_le' _ _).trans_lt (max_lt (ih i).2 (h2 _))

/- English proof (translation)
Introduce `l _ Γ _ n r δ`. Establish `conj : ∀ (g : GL (Fin n) (Qbar l)) (s : Γ), ((g * tw r δ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = (δ s : Qbar l) • ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))` using `fun g s => by`. Simplify using `only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `H χ ⟨g, hg⟩`.

Use `⟨g, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[conj, hg s hs, ← Matrix.diagonal_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using `[mul_comm]`.

Introduce and unpack `H χ χ' e ⟨g, hg⟩ h`. Set `P : GL (Fin n) (Qbar l)` to `⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix, by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp, by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩`. Use `⟨P * g, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e1 : P * g * r s * (P * g)⁻¹ = P * (g * r s * g⁻¹) * P⁻¹` using `by group`. Rewrite using `[e1, Units.val_mul, Units.val_mul P, hg s hs]`.

Express the relevant statement in the definitionally equal form `e.toPEquiv.toMatrix * _ * e.symm.toPEquiv.toMatrix = _`. Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_apply, h i s hs]`. Introduce and unpack `H κ ⟨g, hg⟩`.

Use `⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conj, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]`. Rewrite using `[conj, Matrix.smul_apply, (hg s).2 i]`. Simplify using `[mul_comm]`. Introduce `χ hδ h s i`.

Establish `e1 : ∏ j, (X - C (((χ j * δ) s : (Qbar l)ˣ) : Qbar l)) = (∏ j, (X - C (χ j s : Qbar l))).scaleRoots (δ s)`. Rewrite using `[scaleRoots_prod']`. Simplify using the standard rewrite rules. Establish `e2 : (∏ j, (X - C (χ j s : Qbar l))).natDegree = n`. Rewrite using `[natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, tw_val, charpoly_smul' _ (Units.ne_zero _), coeff_scaleRoots, coeff_scaleRoots, e2, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← sub_mul, norm_mul, norm_pow, hδ, one_pow, mul_one]`. Conclude with `h s i`. Introduce `χ χ' e hχ h hc s i`. Establish `h1` using `h s i`.

Rewrite `h1` using `[← Equiv.prod_comp e fun j => (X - C (χ j s : Qbar l))]`. Establish `h2` using `(prod_cong Finset.univ (fun j => (χ (e j) s : Qbar l)) (fun j => (χ' j s : Qbar l)) (fun j => (hχ _ _).le) (fun j => hc j s) i).2`. Rewrite using `[← sub_add_sub_cancel _ ((∏ j, (X - C (χ (e j) s : Qbar l))).coeff i)]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)`. Introduce `hr`.

Establish `key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W` using `fun W => by`. Prove the components needed by the constructor for the conclusion. Introduce `h g v hv`. Use `W.smul_mem ((δ g : Qbar l)⁻¹) (h g v hv)` as an intermediate fact. Rewrite `this` using `[tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Then use the resulting hypothesis.

Introduce `h g v hv`. Rewrite using `[tw_val, Matrix.smul_mulVec]`. Conclude with `W.smul_mem _ (h g v hv)`. Unfold `IsIrr IsIrrSub at hr ⊢`. Simplify `hr` using `only [key]`.
-/
theorem UpperTheory.V.Sd.shapeFacts :
    UpperTheory.V.Sd.ShapeFacts := by
  intro l _ Γ _ n r δ
  have conj : ∀ (g : GL (Fin n) (Qbar l)) (s : Γ), ((g * tw r δ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      (δ s : Qbar l) • ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := fun g s => by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro H χ ⟨g, hg⟩
    refine ⟨g, fun s hs => ?_⟩
    rw [conj, hg s hs, ← Matrix.diagonal_smul]
    congr 1
    ext i
    simp [mul_comm]
  · rintro H χ χ' e ⟨g, hg⟩ h
    let P : GL (Fin n) (Qbar l) := ⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
    refine ⟨P * g, fun s hs => ?_⟩
    have e1 : P * g * r s * (P * g)⁻¹ = P * (g * r s * g⁻¹) * P⁻¹ := by group
    rw [e1, Units.val_mul, Units.val_mul P, hg s hs]
    change e.toPEquiv.toMatrix * _ * e.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [Matrix.diagonal_apply, h i s hs]
  · rintro H κ ⟨g, hg⟩
    refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · rw [conj, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
    · rw [conj, Matrix.smul_apply, (hg s).2 i]
      simp [mul_comm]
  · intro χ hδ h s i
    have e1 : ∏ j, (X - C (((χ j * δ) s : (Qbar l)ˣ) : Qbar l)) = (∏ j, (X - C (χ j s : Qbar l))).scaleRoots (δ s) := by
      rw [scaleRoots_prod']; simp
    have e2 : (∏ j, (X - C (χ j s : Qbar l))).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]; simp
    rw [e1, tw_val, charpoly_smul' _ (Units.ne_zero _), coeff_scaleRoots, coeff_scaleRoots, e2,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← sub_mul, norm_mul, norm_pow, hδ, one_pow, mul_one]
    exact h s i
  · intro χ χ' e hχ h hc s i
    have h1 := h s i
    rw [← Equiv.prod_comp e fun j => (X - C (χ j s : Qbar l))] at h1
    have h2 := (prod_cong Finset.univ (fun j => (χ (e j) s : Qbar l)) (fun j => (χ' j s : Qbar l))
      (fun j => (hχ _ _).le) (fun j => hc j s) i).2
    rw [← sub_add_sub_cancel _ ((∏ j, (X - C (χ (e j) s : Qbar l))).coeff i)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  · intro hr
    have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : Qbar l)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
