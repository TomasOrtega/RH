import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQ

noncomputable section

open Finset Matrix MeasureTheory Topology Filter

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ} {P Q : ℕ}

def gMatL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' s t := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp [star_add] <;> ring
  map_smul' c s := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul] <;> ring

/- English proof (translation)
Establish `hS : ∀ a b, ‖gMat s a b‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖` using `fun a b => (Finset.single_le_sum (f := fun b => ‖gMat s a b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b, ‖gMat s a b‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))`. Establish `h0 : 0 ≤ ∑ a, ∑ b, ‖gMat s a b‖` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Use `norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg h0).2 fun a => (le_of_eq ?_).trans (hS a a)` and prove the remaining obligations. Simplify using `[gMat, kMat, pmat]`.

Use `(pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)` and prove the remaining obligations. Take `⟨⟨a, b⟩, h⟩` from `ab`. Establish `h1 : ¬ (b < a ∧ ε a ≠ ε b)` using `fun h' => h'.2 h.2`. Establish `h2 : ¬ (a < b ∧ ε b ≠ ε a)` using `fun h' => lt_asymm h'.1 h.1`. Establish `h3 : a ≠ b` using `h.1.ne'`.

Simplify using `[gMat, kMat, pmat, h3, h, h1, h2]`. Use `(pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)` and prove the remaining obligations. Take `⟨⟨a, b⟩, h⟩` from `ab`. Establish `h1 : ¬ (b < a ∧ ε a = ε b)` using `fun h' => h.2 h'.2`. Establish `h2 : ¬ (a < b ∧ ε b = ε a)` using `fun h' => lt_asymm h'.1 h.1`.

Establish `h3 : a ≠ b` using `h.1.ne'`. Simplify using `[gMat, kMat, pmat, h3, h, h1, h2]`.
-/
theorem norm_le_sum_gMat {ε : Fin n → Bool} (s : GCo ε) : ‖s‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖ := by
  have hS : ∀ a b, ‖gMat s a b‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖ := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖gMat s a b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖gMat s a b‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
  have h0 : 0 ≤ ∑ a, ∑ b, ‖gMat s a b‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun a => (le_of_eq ?_).trans (hS a a)
    simp [gMat, kMat, pmat]
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)
    obtain ⟨⟨a, b⟩, h⟩ := ab
    have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => h'.2 h.2
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h' => lt_asymm h'.1 h.1
    have h3 : a ≠ b := h.1.ne'
    simp [gMat, kMat, pmat, h3, h, h1, h2]
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)
    obtain ⟨⟨a, b⟩, h⟩ := ab
    have h1 : ¬ (b < a ∧ ε a = ε b) := fun h' => h.2 h'.2
    have h2 : ¬ (a < b ∧ ε b = ε a) := fun h' => lt_asymm h'.1 h.1
    have h3 : a ≠ b := h.1.ne'
    simp [gMat, kMat, pmat, h3, h, h1, h2]

/- English proof (translation)
Establish `h1 : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure` using `by show (Measure.pi fun _ => (volume : Measure ℝ)).IsAddHaarMeasure; infer_instance`. Establish `h2 : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure` using `by show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance`. Establish `h3 : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure` using `by show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance`. Establish `h4 : (volume : Measure (KCo ε)).IsAddHaarMeasure` using `by show ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (KPair ε → ℂ))).IsAddHaarMeasure infer_instance`. Use `⟨h4, h3, ?_⟩` and prove the remaining obligations.

Use `show ((volume : Measure (KCo ε)).prod (volume : Measure (PCoord ε → ℂ))).IsAddHaarMeasure`. Conclude with `MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _`.
-/
theorem gco_haar (ε : Fin n → Bool) :
    (volume : Measure (KCo ε)).IsAddHaarMeasure ∧ (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure ∧
      (volume : Measure (GCo ε)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℝ)).IsAddHaarMeasure; infer_instance
  have h2 : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance
  have h3 : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance
  have h4 : (volume : Measure (KCo ε)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (KPair ε → ℂ))).IsAddHaarMeasure
    infer_instance
  refine ⟨h4, h3, ?_⟩
  show ((volume : Measure (KCo ε)).prod (volume : Measure (PCoord ε → ℂ))).IsAddHaarMeasure
  exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem upqT_borel (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem lieU_borel (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal_apply, he1, he2, Matrix.one_apply] <;>`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jpq_eq_diag (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.UG.Jpq P Q = Matrix.diagonal (fun i => if ε (e i) = true then (1 : ℂ) else -1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal_apply, he1, he2, Matrix.one_apply] <;>
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Jpq_eq_diag e he1 he2]`. Use extensionality with `a b`. Simplify using `[Jm, Matrix.diagonal_apply]`.
-/
theorem Jm_eq_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Jm ε = Matrix.reindex e e (Formalism.UG.Jpq P Q) := by
  rw [Jpq_eq_diag e he1 he2]
  ext a b
  simp [Jm, Matrix.diagonal_apply]

def yE (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) : ℂ :=
  (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (e.symm a) (e.symm b)

/- English proof (translation)
Establish `h : (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0` using `X.2`. Rewrite `h` using `[Jpq_eq_diag e he1 he2]`. Establish `h'` using `congrFun (congrFun h (e.symm a)) (e.symm b)`. Simplify `h'` using `[yE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.
-/
theorem lie_rel (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) :
    star (yE e X b a) * (if ε b = true then (1 : ℂ) else -1) +
      (if ε a = true then (1 : ℂ) else -1) * yE e X a b = 0 := by
  have h : (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 := X.2
  rw [Jpq_eq_diag e he1 he2] at h
  have h' := congrFun (congrFun h (e.symm a)) (e.symm b)
  simpa [yE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

/- English proof (translation)
Establish `R` using `lie_rel e he1 he2 X a b`. Rewrite `R` using `[← h]`. Simplify using `only [Complex.star_def] at R ⊢`. Apply the tactic sequence `cases ha : ε a <;> simp [ha] at R <;> first | linear_combination R | linear_combination -R`.
-/
theorem lie_rel_c (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) (h : ε a = ε b) : yE e X a b = -star (yE e X b a) := by
  have R := lie_rel e he1 he2 X a b
  rw [← h] at R
  simp only [Complex.star_def] at R ⊢
  cases ha : ε a <;> simp [ha] at R <;> first | linear_combination R | linear_combination -R

/- English proof (translation)
Establish `R` using `lie_rel e he1 he2 X a b`. Simplify using `only [Complex.star_def] at R ⊢`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at R h ⊢ <;> first | linear_combination R | linear_combination -R`.
-/
theorem lie_rel_nc (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) (h : ε a ≠ ε b) : yE e X a b = star (yE e X b a) := by
  have R := lie_rel e he1 he2 X a b
  simp only [Complex.star_def] at R ⊢
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at R h ⊢ <;>
    first | linear_combination R | linear_combination -R

/- English proof (translation)
Establish `R` using `congrArg Complex.re (lie_rel e he1 he2 X a a)`. Apply the tactic sequence `cases ha : ε a <;> simp [ha] at R <;> linarith`.
-/
theorem lie_rel_d (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a : Fin n) : (yE e X a a).re = 0 := by
  have R := congrArg Complex.re (lie_rel e he1 he2 X a a)
  cases ha : ε a <;> simp [ha] at R <;> linarith

def sOfLie (e : Fin P ⊕ Fin Q ≃ Fin n) (ε : Fin n → Bool) (X : Formalism.BasicNotions.lieU P Q) : GCo ε :=
  (((fun a => (yE e X a a).im), fun ab => yE e X ab.1.1 ab.1.2), fun ab => yE e X ab.1.1 ab.1.2)

/- English proof (translation)
Simplify using `only [gMat, kMat, pmat, sOfLie, Matrix.add_apply]`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Establish `n1 : a ≠ b` using `hab.ne`. Establish `n2 : ¬ (b < a)` using `not_lt.2 hab.le`. Distinguish the cases in `hε : ε a = ε b`.

Simplify using `[n1, n2, hab, hε]`. Conclude with `(lie_rel_c e he1 he2 X a b hε).symm`. Establish `hε' : ε b ≠ ε a` using `Ne.symm hε`. Simplify using `[n1, n2, hab, hε, hε']`. Conclude with `(lie_rel_nc e he1 he2 X a b hε).symm`.

Establish `hre` using `lie_rel_d e he1 he2 X a`. Simplify using the standard rewrite rules. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Establish `n1 : a ≠ b` using `hab.ne'`. Establish `n2 : ¬ (a < b)` using `not_lt.2 hab.le`.

Distinguish the cases in `hε : ε a = ε b`. Simplify using `[n1, n2, hab, hε]`. Simplify using `[n1, n2, hab, hε]`.
-/
theorem gMat_sOfLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) : gMat (sOfLie e ε X) a b = yE e X a b := by
  simp only [gMat, kMat, pmat, sOfLie, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have n1 : a ≠ b := hab.ne
    have n2 : ¬ (b < a) := not_lt.2 hab.le
    by_cases hε : ε a = ε b
    · simp [n1, n2, hab, hε]
      exact (lie_rel_c e he1 he2 X a b hε).symm
    · have hε' : ε b ≠ ε a := Ne.symm hε
      simp [n1, n2, hab, hε, hε']
      exact (lie_rel_nc e he1 he2 X a b hε).symm
  · have hre := lie_rel_d e he1 he2 X a
    simp
    apply Complex.ext <;> simp [hre]
  · have n1 : a ≠ b := hab.ne'
    have n2 : ¬ (a < b) := not_lt.2 hab.le
    by_cases hε : ε a = ε b
    · simp [n1, n2, hab, hε]
    · simp [n1, n2, hab, hε]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show Matrix.reindex e.symm e.symm (gMat (sOfLie e ε X)) i j = _`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]`. Rewrite using `[gMat_sOfLie e he1 he2 X]`.

Simplify using `[yE]`.
-/
theorem gToLie_surj (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) : gToLie e he1 he2 (sOfLie e ε X) = X := by
  apply Subtype.ext
  ext i j
  show Matrix.reindex e.symm e.symm (gMat (sOfLie e ε X)) i j = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [gMat_sOfLie e he1 he2 X]
  simp [yE]

/- English proof (translation)
Establish `hc : Continuous (fun M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Matrix.reindex e e M)` using `continuous_id.matrix_submatrix _ _`. Establish `hc' : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M)` using `continuous_id.matrix_submatrix _ _`. Simplify using `only [NormedSpace.exp_eq_tsum_rat]`. Use `show (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom (∑' k : ℕ, ((k.factorial : ℚ)⁻¹ : ℚ) • X ^ k) = _`. Rewrite using `[Function.LeftInverse.map_tsum (g := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom) _ (by exact hc) (by exact hc') (fun M => by ext i j; simp)]`.

Simplify using `only [map_rat_smul, map_pow]`. Both sides reduce to the same expression.
-/
theorem exp_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    Matrix.reindex e e (NormedSpace.exp X) = NormedSpace.exp (Matrix.reindex e e X) := by
  have hc : Continuous (fun M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Matrix.reindex e e M) :=
    continuous_id.matrix_submatrix _ _
  have hc' : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M) :=
    continuous_id.matrix_submatrix _ _
  simp only [NormedSpace.exp_eq_tsum_rat]
  show (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom (∑' k : ℕ, ((k.factorial : ℚ)⁻¹ : ℚ) • X ^ k) = _
  rw [Function.LeftInverse.map_tsum (g := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom) _ (by exact hc) (by exact hc')
    (fun M => by ext i j; simp)]
  simp only [map_rat_smul, map_pow]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`.
-/
theorem cT_eq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : Formalism.UG.cT (starRingEnd ℂ) A = Aᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

/- English proof (translation)
Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]`.
-/
theorem Jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/- English proof (translation)
Rewrite using `[Jm_eq_reindex e he1 he2]`. Simplify using `[Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`.
-/
theorem reindex_form (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Matrix.reindex e e A)ᴴ * Jm ε * Matrix.reindex e e A = Matrix.reindex e e (Aᴴ * Formalism.UG.Jpq P Q * A) := by
  rw [Jm_eq_reindex e he1 he2]
  simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

def upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) (g : Formalism.BasicNotions.UpqT P Q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)

/- English proof (translation)
Rewrite using `[← cT_eq]`. Conclude with `Iff.rfl`.
-/
theorem mem_Upq_iff (g : GL (Fin P ⊕ Fin Q) ℂ) :
    g ∈ Formalism.UG.Upq P Q ↔
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q * g = Formalism.UG.Jpq P Q := by
  rw [← cT_eq]; exact Iff.rfl

/- English proof (translation)
The claim follows from `(mem_Upq_iff _).1 (show Formalism.UG.Upq P Q from g).2`.
-/
theorem mat_mem (g : Formalism.BasicNotions.UpqT P Q) :
    (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g = Formalism.UG.Jpq P Q :=
  (mem_Upq_iff _).1 (show Formalism.UG.Upq P Q from g).2

/- English proof (translation)
Apply `Units.inv_eq_of_mul_eq_one_left` to reduce the goal to its premises. Establish `h` using `mat_mem g`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h, Jpq_mul_self]`.
-/
theorem mat_inv (g : Formalism.BasicNotions.UpqT P Q) :
    ((((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) :
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      Formalism.UG.Jpq P Q * (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q := by
  apply Units.inv_eq_of_mul_eq_one_left
  have h := mat_mem g
  calc Formalism.UG.Jpq P Q * (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g
      = Formalism.UG.Jpq P Q * ((Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jpq_mul_self]

/- English proof (translation)
Unfold `inUJ upqMat`. Rewrite using `[reindex_form e he1 he2, mat_mem, ← Jm_eq_reindex e he1 he2]`.
-/
theorem upqMat_inUJ (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (g : Formalism.BasicNotions.UpqT P Q) : inUJ ε (upqMat e g) := by
  unfold inUJ upqMat
  rw [reindex_form e he1 he2, mat_mem, ← Jm_eq_reindex e he1 he2]

/- English proof (translation)
Use extensionality with `M`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `upqMat_inUJ e he1 he2 g`. Introduce `hM set A := Matrix.reindex e.symm e.symm M with hA`.

Establish `hAM : Matrix.reindex e e A = M` using `by rw [hA]; ext a b; simp`. Establish `hform : Aᴴ * Formalism.UG.Jpq P Q * A = Formalism.UG.Jpq P Q`. Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises. Rewrite using `[← reindex_form e he1 he2, hAM, ← Jm_eq_reindex e he1 he2]`. Conclude with `hM`.

Establish `h2 : (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hform, Jpq_mul_self]`. Establish `h1 : A * (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) = 1` using `mul_eq_one_comm.mp h2`.

Set `u : GL (Fin P ⊕ Fin Q) ℂ` to `⟨A, Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q, h1, h2⟩`. Establish `hu : u ∈ Formalism.UG.Upq P Q` using `(mem_Upq_iff u).2 hform`. Use `⟨(⟨u, hu⟩ : Formalism.UG.Upq P Q), ?_⟩` and prove the remaining obligations. Conclude with `hAM`.
-/
theorem range_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Set.range (upqMat e) = {M | inUJ ε M} := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact upqMat_inUJ e he1 he2 g
  · intro hM
    set A := Matrix.reindex e.symm e.symm M with hA
    have hAM : Matrix.reindex e e A = M := by rw [hA]; ext a b; simp
    have hform : Aᴴ * Formalism.UG.Jpq P Q * A = Formalism.UG.Jpq P Q := by
      apply (Matrix.reindex e e).injective
      rw [← reindex_form e he1 he2, hAM, ← Jm_eq_reindex e he1 he2]
      exact hM
    have h2 : (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
      calc (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = Formalism.UG.Jpq P Q * (Aᴴ * Formalism.UG.Jpq P Q * A) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hform, Jpq_mul_self]
    have h1 : A * (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) = 1 := mul_eq_one_comm.mp h2
    let u : GL (Fin P ⊕ Fin Q) ℂ := ⟨A, Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q, h1, h2⟩
    have hu : u ∈ Formalism.UG.Upq P Q := (mem_Upq_iff u).2 hform
    refine ⟨(⟨u, hu⟩ : Formalism.UG.Upq P Q), ?_⟩
    exact hAM

/- English proof (translation)
Establish `h : Continuous fun g : Formalism.BasicNotions.UpqT P Q => Formalism.BasicNotions.UpqT.mat g` using `Units.continuous_val.comp continuous_subtype_val`. Conclude with `h.matrix_submatrix _ _`.
-/
theorem upqMat_cont (e : Fin P ⊕ Fin Q ≃ Fin n) : Continuous (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
  have h : Continuous fun g : Formalism.BasicNotions.UpqT P Q => Formalism.BasicNotions.UpqT.mat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_submatrix _ _

/- English proof (translation)
Set `f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ` to `fun M => (Matrix.reindex e.symm e.symm M, MulOpposite.op (Formalism.UG.Jpq P Q * (Matrix.reindex e.symm e.symm M)ᴴ * Formalism.UG.Jpq P Q))`. Establish `hr : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M` using `continuous_id.matrix_submatrix _ _`. Establish `hf : Continuous f` using `hr.prodMk (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul hr.matrix_conjTranspose).matrix_mul continuous_const))`. Establish `hcomp : f ∘ (upqMat e : Formalism.BasicNotions.UpqT P Q → _) = Units.embedProduct _ ∘ (fun g : Formalism.BasicNotions.UpqT P Q => ((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ))`. Use function extensionality and compare the values at `g`.

Simplify using `only [Function.comp_apply, f, Units.embedProduct_apply, upqMat]`. Rewrite using `[mat_inv]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish `hI : IsInducing (upqMat e : Formalism.BasicNotions.UpqT P Q → _)`.

Use `IsInducing.of_comp (upqMat_cont e) hf ?_` and prove the remaining obligations. Rewrite using `[hcomp]`. Conclude with `Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal`. Establish `hE : IsEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _)`. Use `⟨hI, fun a b h => ?_⟩` and prove the remaining obligations.

Establish `h' : Formalism.BasicNotions.UpqT.mat a = Formalism.BasicNotions.UpqT.mat b` using `(Matrix.reindex e e).injective h`. Conclude with `Subtype.ext (Units.ext h')`. Use `⟨hE, ?_⟩` and prove the remaining obligations. Rewrite using `[range_upqMat e he1 he2]`. Conclude with `isClosed_inUJ ε`.
-/
theorem isClosedEmbedding_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    IsClosedEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
  let f : Matrix (Fin n) (Fin n) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun M => (Matrix.reindex e.symm e.symm M,
      MulOpposite.op (Formalism.UG.Jpq P Q * (Matrix.reindex e.symm e.symm M)ᴴ * Formalism.UG.Jpq P Q))
  have hr : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M :=
    continuous_id.matrix_submatrix _ _
  have hf : Continuous f :=
    hr.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul hr.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ (upqMat e : Formalism.BasicNotions.UpqT P Q → _) =
      Units.embedProduct _ ∘ (fun g : Formalism.BasicNotions.UpqT P Q => ((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ)) := by
    funext g
    simp only [Function.comp_apply, f, Units.embedProduct_apply, upqMat]
    rw [mat_inv]
    simp
    rfl
  have hI : IsInducing (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
    refine IsInducing.of_comp (upqMat_cont e) hf ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal
  have hE : IsEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
    refine ⟨hI, fun a b h => ?_⟩
    have h' : Formalism.BasicNotions.UpqT.mat a = Formalism.BasicNotions.UpqT.mat b := (Matrix.reindex e e).injective h
    exact Subtype.ext (Units.ext h')
  refine ⟨hE, ?_⟩
  rw [range_upqMat e he1 he2]
  exact isClosed_inUJ ε

/- English proof (translation)
Use `haveI := upqT_borel P Q`. Conclude with `Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) (isClosedEmbedding_upqMat e he1 he2)`.
-/
theorem measurableEmbedding_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    @MeasurableEmbedding (Formalism.BasicNotions.UpqT P Q) (Fin n → Fin n → ℂ) _ _ (fun g => upqMat e g) := by
  haveI := upqT_borel P Q
  exact Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ)
    (isClosedEmbedding_upqMat e he1 he2)

/- English proof (translation)
The claim follows from `Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) (isClosedEmbedding_toM ε)`.
-/
theorem measurableEmbedding_toM (ε : Fin n → Bool) :
    @MeasurableEmbedding (UJ ε) (Fin n → Fin n → ℂ) _ _ (fun g : UJ ε => toM g) :=
  Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) (isClosedEmbedding_toM ε)

/- English proof (translation)
Use `show Matrix.reindex e e (Matrix.reindex e.symm e.symm (gMat s)) = gMat s`. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem gToLie_val (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Matrix.reindex e e ((gToLie e he1 he2 s : Formalism.BasicNotions.lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      gMat s := by
  show Matrix.reindex e e (Matrix.reindex e.symm e.symm (gMat s)) = gMat s
  ext a b; simp

/- English proof (translation)
Use extensionality with `M`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, ⟨X, hX, hgX⟩, rfl⟩`. Establish `hin : upqMat e g ∈ Set.range (fun u : UJ ε => toM u)`. Rewrite using `[range_toM]`.

Conclude with `upqMat_inUJ e he1 he2 g`. Take `⟨u, hu⟩` from `hin`. Use `⟨u, ⟨sOfLie e ε X, ?_, ?_⟩, hu⟩` and prove the remaining obligations. Use `show gToLie e he1 he2 (sOfLie e ε X) ∈ Formalism.BasicNotions.ballU P Q r`. Rewrite using `[gToLie_surj]`.

Conclude with `hX`. Establish `hu' : toM u = upqMat e g` using `hu`. Rewrite using `[hu', upqMat, hgX, exp_reindex, ← gToLie_val e he1 he2, gToLie_surj]`. Introduce and unpack `⟨u, ⟨s, hs, hus⟩, rfl⟩`. Establish `hin : toM u ∈ Set.range (upqMat e)`.

Rewrite using `[range_upqMat e he1 he2]`. Conclude with `u.2`. Take `⟨g, hg⟩` from `hin`. Use `⟨g, ⟨gToLie e he1 he2 s, hs, ?_⟩, hg⟩` and prove the remaining obligations. Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises.

Rewrite using `[exp_reindex, gToLie_val e he1 he2]`. Use `show upqMat e g = _`. Rewrite using `[hg, hus]`.
-/
theorem image_expBall (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (r : ℝ) :
    upqMat e '' {g : Formalism.BasicNotions.UpqT P Q | ∃ X ∈ Formalism.BasicNotions.ballU P Q r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} =
      (fun g : UJ ε => toM g) '' expSet {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} := by
  ext M
  constructor
  · rintro ⟨g, ⟨X, hX, hgX⟩, rfl⟩
    have hin : upqMat e g ∈ Set.range (fun u : UJ ε => toM u) := by
      rw [range_toM]; exact upqMat_inUJ e he1 he2 g
    obtain ⟨u, hu⟩ := hin
    refine ⟨u, ⟨sOfLie e ε X, ?_, ?_⟩, hu⟩
    · show gToLie e he1 he2 (sOfLie e ε X) ∈ Formalism.BasicNotions.ballU P Q r
      rw [gToLie_surj]; exact hX
    · have hu' : toM u = upqMat e g := hu
      rw [hu', upqMat, hgX, exp_reindex, ← gToLie_val e he1 he2, gToLie_surj]
  · rintro ⟨u, ⟨s, hs, hus⟩, rfl⟩
    have hin : toM u ∈ Set.range (upqMat e) := by
      rw [range_upqMat e he1 he2]; exact u.2
    obtain ⟨g, hg⟩ := hin
    refine ⟨g, ⟨gToLie e he1 he2 s, hs, ?_⟩, hg⟩
    apply (Matrix.reindex e e).injective
    rw [exp_reindex, gToLie_val e he1 he2]
    show upqMat e g = _
    rw [hg, hus]

end ReciprocityTheory.ChartRestriction.DS
