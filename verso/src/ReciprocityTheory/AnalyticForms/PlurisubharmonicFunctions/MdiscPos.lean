import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open Matrix Finset
open scoped ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def pmGmat (w : Fin D → ι → Fin D → ℂ) (g : Fin D → Fin D × ι) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun x a => w (g a).1 (g a).2 x

def pmGram (w : Fin D → ι → Fin D → ℂ) (k : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => ∑ r, w k r a * star (w k r b)

/- English proof (translation)
Simplify using `only [Matrix.sum_apply, pmGram, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by simp [hx])]`. Conclude with `Finset.sum_congr rfl fun x hx => by simp [hx]`.
-/
theorem pm_sum_gram_apply (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) (a b : Fin D) :
    (∑ k ∈ S, pmGram w k) a b =
      ∑ p : Fin D × ι, (if p.1 ∈ S then (1 : ℂ) else 0) * (w p.1 p.2 a * star (w p.1 p.2 b)) := by
  simp only [Matrix.sum_apply, pmGram, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by simp [hx])]
  exact Finset.sum_congr rfl fun x hx => by simp [hx]

/- English proof (translation)
Simplify using `only [det_apply, pm_sum_gram_apply]`. Simplify using `only [Fintype.prod_sum, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_mul_distrib, pmGmat, Matrix.of_apply, Finset.prod_boole, Finset.mem_univ, true_imp_iff, Units.smul_def, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pm_det_sum_gram (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) :
    (∑ k ∈ S, pmGram w k).det = ∑ g : Fin D → Fin D × ι,
      (if ∀ a, (g a).1 ∈ S then (1 : ℂ) else 0) *
        ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) := by
  simp only [det_apply, pm_sum_gram_apply]
  simp only [Fintype.prod_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, pmGmat, Matrix.of_apply, Finset.prod_boole,
    Finset.mem_univ, true_imp_iff, Units.smul_def, zsmul_eq_mul]
  ring

/- English proof (translation)
Establish `hc : ∀ T : Finset (Fin D), D - (D - T.card) = T.card` using `fun T => Nat.sub_sub_self (by simpa using Finset.card_le_univ T)`. Rewrite using `[← Fintype.sum_bijective (Compl.compl : Finset (Fin D) → Finset (Fin D)) compl_involutive.bijective (fun T : Finset (Fin D) => (-1 : ℂ) ^ T.card * if T ⊆ Kᶜ then 1 else 0) _ fun T => by`. Simplify using `only [Finset.card_compl, Fintype.card_fin, hc, Finset.subset_compl_comm]]`. Simplify using `only [mul_ite, mul_one, mul_zero]`. Rewrite using `[← Finset.sum_filter]`.

Establish `hf : (univ.filter fun T : Finset (Fin D) => T ⊆ Kᶜ) = Kᶜ.powerset` using `by ext; simp`. Rewrite using `[hf]`. Establish `h` using `Finset.sum_powerset_neg_one_pow_card (x := Kᶜ)`. Establish `h2` using `congrArg (Int.cast : ℤ → ℂ) h`. Move the coercions through the operations in `at h2`.

Rewrite using `[h2]`. Simplify using `[Finset.compl_eq_empty_iff]`.
-/
theorem pm_alt (K : Finset (Fin D)) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if K ⊆ S then 1 else 0) =
      if K = univ then 1 else 0 := by
  have hc : ∀ T : Finset (Fin D), D - (D - T.card) = T.card := fun T =>
    Nat.sub_sub_self (by simpa using Finset.card_le_univ T)
  rw [← Fintype.sum_bijective (Compl.compl : Finset (Fin D) → Finset (Fin D)) compl_involutive.bijective
    (fun T : Finset (Fin D) => (-1 : ℂ) ^ T.card * if T ⊆ Kᶜ then 1 else 0) _ fun T => by
      simp only [Finset.card_compl, Fintype.card_fin, hc, Finset.subset_compl_comm]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hf : (univ.filter fun T : Finset (Fin D) => T ⊆ Kᶜ) = Kᶜ.powerset := by ext; simp
  rw [hf]
  have h := Finset.sum_powerset_neg_one_pow_card (x := Kᶜ)
  have h2 := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at h2
  rw [h2]
  simp [Finset.compl_eq_empty_iff]

def pmWt (g : Fin D → Fin D × ι) : ℝ :=
  if univ.image (fun a => (g a).1) = univ then 1 else 0

/- English proof (translation)
Apply the tactic sequence `unfold pmWt; split_ifs <;> norm_num`.
-/
theorem pmWt_nonneg (g : Fin D → Fin D × ι) : 0 ≤ pmWt g := by
  unfold pmWt; split_ifs <;> norm_num

/- English proof (translation)
Unfold `pmWt`. Establish `: univ.image (fun a => ((g ∘ τ) a).1) = univ.image (fun a => (g a).1)`. Use extensionality with `x`. Simplify using `only [mem_image, mem_univ, true_and, Function.comp_apply]`. Conclude with `⟨fun ⟨a, h⟩ => ⟨τ a, h⟩, fun ⟨a, h⟩ => ⟨τ.symm a, by simpa using h⟩⟩`.

Rewrite using `[this]`.
-/
theorem pmWt_comp_perm (g : Fin D → Fin D × ι) (τ : Equiv.Perm (Fin D)) :
    pmWt (g ∘ τ) = pmWt g := by
  unfold pmWt
  have : univ.image (fun a => ((g ∘ τ) a).1) = univ.image (fun a => (g a).1) := by
    ext x
    simp only [mem_image, mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨a, h⟩ => ⟨τ a, h⟩, fun ⟨a, h⟩ => ⟨τ.symm a, by simpa using h⟩⟩
  rw [this]

/- English proof (translation)
Establish `h : ∀ S : Finset (Fin D), (∀ a, (g a).1 ∈ S) ↔ univ.image (fun a => (g a).1) ⊆ S`. Introduce `S`. Simplify using `[Finset.image_subset_iff]`. Simplify using `only [h, pm_alt, pmWt]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem pm_sum_alt (g : Fin D → Fin D × ι) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if ∀ a, (g a).1 ∈ S then 1 else 0) =
      (pmWt g : ℂ) := by
  have h : ∀ S : Finset (Fin D), (∀ a, (g a).1 ∈ S) ↔ univ.image (fun a => (g a).1) ⊆ S := by
    intro S; simp [Finset.image_subset_iff]
  simp only [h, pm_alt, pmWt]
  split_ifs <;> simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g h e => by funext a; simpa using congrFun e (τ.symm a), fun g => ⟨g ∘ τ.symm, by funext a; simp⟩⟩`.
-/
theorem pm_comp_bijective (τ : Equiv.Perm (Fin D)) :
    Function.Bijective (fun g : Fin D → Fin D × ι => g ∘ τ) :=
  ⟨fun g h e => by funext a; simpa using congrFun e (τ.symm a),
    fun g => ⟨g ∘ τ.symm, by funext a; simp⟩⟩

/- English proof (translation)
Establish `hcard : (D.factorial : ℂ) = ∑ _τ : Equiv.Perm (Fin D), (1 : ℂ)`. Simplify using `[Fintype.card_perm]`. Rewrite using `[hcard, Finset.sum_mul]`. Simplify using `only [one_mul]`. Rewrite using `[Finset.sum_congr rfl fun τ _ => (Fintype.sum_bijective _ (pm_comp_bijective (ι := ι) τ) (fun g => (pmWt (g ∘ τ) : ℂ) * ((pmGmat w (g ∘ τ)).det * ∏ a, star (w ((g ∘ τ) a).1 ((g ∘ τ) a).2 a))) (fun g => (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a))) fun _ => …`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Establish `hsub : ∀ τ : Equiv.Perm (Fin D), pmGmat w (g ∘ τ) = (pmGmat w g).submatrix id τ` using `fun τ => rfl`. Establish `hstar : star (pmGmat w g).det = ∑ τ : Equiv.Perm (Fin D), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ a, star (w (g (τ a)).1 (g (τ a)).2 a)`. Rewrite using `[← det_conjTranspose, det_apply]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [conjTranspose_apply, pmGmat, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]`. Simplify using `only [pmWt_comp_perm, hsub, det_permute', Function.comp_apply]`. Rewrite using `[hstar, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pm_sum_perm_reindex (w : Fin D → ι → Fin D → ℂ) :
    (D.factorial : ℂ) * ∑ g : Fin D → Fin D × ι,
        (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) =
      ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) := by
  have hcard : (D.factorial : ℂ) = ∑ _τ : Equiv.Perm (Fin D), (1 : ℂ) := by
    simp [Fintype.card_perm]
  rw [hcard, Finset.sum_mul]
  simp only [one_mul]
  rw [Finset.sum_congr rfl fun τ _ => (Fintype.sum_bijective _ (pm_comp_bijective (ι := ι) τ)
    (fun g => (pmWt (g ∘ τ) : ℂ) * ((pmGmat w (g ∘ τ)).det *
      ∏ a, star (w ((g ∘ τ) a).1 ((g ∘ τ) a).2 a)))
    (fun g => (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)))
    fun _ => rfl).symm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hsub : ∀ τ : Equiv.Perm (Fin D), pmGmat w (g ∘ τ) = (pmGmat w g).submatrix id τ :=
    fun τ => rfl
  have hstar : star (pmGmat w g).det = ∑ τ : Equiv.Perm (Fin D),
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ a, star (w (g (τ a)).1 (g (τ a)).2 a) := by
    rw [← det_conjTranspose, det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [conjTranspose_apply, pmGmat, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  simp only [pmWt_comp_perm, hsub, det_permute', Function.comp_apply]
  rw [hstar, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/- English proof (translation)
Establish `hD : (D.factorial : ℂ) ≠ 0` using `by exact_mod_cast D.factorial_ne_zero`. Establish `h1 : (D.factorial : ℂ) * mdisc (pmGram w) = ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a))`. Rewrite using `[mdisc, ← mul_assoc, mul_one_div_cancel hD, one_mul]`. Simplify using `only [pm_det_sum_gram, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← pm_sum_alt, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun S _ => by ring`. Establish `h2` using `pm_sum_perm_reindex w`. Rewrite `h2` using `[← h1]`.

Establish `h3 : ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) = ((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det : ℝ) : ℂ)`. Use `push_cast`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj]`. Use `push_cast`.

Rewrite using `[eq_div_iff (pow_ne_zero 2 hD)]`. Move the coercions through the operations in `at h3`. Rewrite using `[← h3, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pm_mdisc_gram (w : Fin D → ι → Fin D → ℂ) :
    mdisc (pmGram w) = (((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det) /
      (D.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hD : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h1 : (D.factorial : ℂ) * mdisc (pmGram w) = ∑ g : Fin D → Fin D × ι,
      (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) := by
    rw [mdisc, ← mul_assoc, mul_one_div_cancel hD, one_mul]
    simp only [pm_det_sum_gram, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← pm_sum_alt, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by ring
  have h2 := pm_sum_perm_reindex w
  rw [← h1] at h2
  have h3 : ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) =
      ((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  push_cast
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  push_cast at h3
  rw [← h3, ← h2]
  ring

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)`.
-/
theorem pm_mdisc_gram_sum_nonneg (w : Fin D → ι → Fin D → ℂ) :
    0 ≤ ∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det :=
  Finset.sum_nonneg fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)

open scoped MatrixOrder in
/- English proof (translation)
Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg`. Use `⟨fun r a => star (B r a), fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hB, star_eq_conjTranspose, mul_apply]`. Simplify using `[conjTranspose_apply]`.
-/
theorem pm_exists_gram_of_posSemidef {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef) :
    ∃ v : Fin D → Fin D → ℂ, ∀ a b, A a b = ∑ r, v r a * star (v r b) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun r a => star (B r a), fun a b => ?_⟩
  rw [hB, star_eq_conjTranspose, mul_apply]
  simp [conjTranspose_apply]

open scoped MatrixOrder in
/- English proof (translation)
Take `⟨r, hr, hle⟩` from `(CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin D) (Fin D) ℂ) hA.isStrictlyPositive.isSelfAdjoint).2 fun x hx => hA.isStrictlyPositive.spectrum_pos hx`. Take `⟨v, hv⟩` from `pm_exists_gram_of_posSemidef (Matrix.le_iff.mp hle)`. Use `⟨r, hr, v, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← hv]`. Simplify using `[Matrix.algebraMap_matrix_apply]`.
-/
theorem pm_exists_gram_add_of_posDef [Nonempty (Fin D)] {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosDef) : ∃ r : ℝ, 0 < r ∧ ∃ v : Fin D → Fin D → ℂ,
      ∀ a b, A a b = ∑ s, v s a * star (v s b) + if a = b then (r : ℂ) else 0 := by
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin D) (Fin D) ℂ)
    hA.isStrictlyPositive.isSelfAdjoint).2 fun x hx => hA.isStrictlyPositive.spectrum_pos hx
  obtain ⟨v, hv⟩ := pm_exists_gram_of_posSemidef (Matrix.le_iff.mp hle)
  refine ⟨r, hr, v, fun a b => ?_⟩
  rw [← hv]
  simp [Matrix.algebraMap_matrix_apply]

/- English proof (translation)
Establish `: A = pmGram w` using `by funext k; ext a b; simp [pmGram, h]`. Rewrite using `[this, pm_mdisc_gram]`.
-/
theorem pm_mdisc_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ι → Fin D → ℂ)
    (h : ∀ k a b, A k a b = ∑ r, w k r a * star (w k r b)) :
    mdisc A = (((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det) /
      (D.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
  have : A = pmGram w := by funext k; ext a b; simp [pmGram, h]
  rw [this, pm_mdisc_gram]

/- English proof (translation)
Use `choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)`. Rewrite using `[pm_mdisc_of_gram A v hv]`. Use `⟨Complex.ofReal_im _, ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_re]`. Conclude with `div_nonneg (pm_mdisc_gram_sum_nonneg _) (by positivity)`.
-/
theorem mixedDiscriminant_nonneg_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (mdisc A).im = 0 ∧ 0 ≤ (mdisc A).re := by
  choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)
  rw [pm_mdisc_of_gram A v hv]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact div_nonneg (pm_mdisc_gram_sum_nonneg _) (by positivity)

/- English proof (translation)
Take `_ | n` from `D`. Rewrite using `[mdisc_zero]`. Simplify using the standard rewrite rules. Use `choose r hr v hv using fun k => pm_exists_gram_add_of_posDef (hA k)`. Set `w : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1)) → Fin (n + 1) → ℂ` to `fun k => Sum.elim (v k) (fun s x => if x = s then ((Real.sqrt (r k) : ℝ) : ℂ) else 0)`.

Establish `hc : ∀ k, ((Real.sqrt (r k) : ℝ) : ℂ) * star ((Real.sqrt (r k) : ℝ) : ℂ) = (r k : ℂ)`. Introduce `k`. Rewrite using `[Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr k).le]`. Establish `hw : ∀ k a b, A k a b = ∑ s, w k s a * star (w k s b)`. Introduce `k a b`.

Rewrite using `[hv, Fintype.sum_sum_type]`. Use `congr 1`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single a (fun s _ hs => by simp [w, Ne.symm hs]) (by simp)]`.

Simplify using `only [w, Sum.elim_inr]`. Conclude with `(hc k).symm`. Rewrite using `[if_neg hab]`. Use `(Finset.sum_eq_zero fun s _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `has : a = s`.

Substitute `has` using the available equality. Simplify using `[w, Ne.symm hab]`. Simplify using `[w, has]`. Rewrite using `[pm_mdisc_of_gram A w hw]`. Use `⟨Complex.ofReal_im _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Complex.ofReal_re]`. Use `div_pos ?_ (by positivity)` and prove the remaining obligations. Set `g₀ : Fin (n + 1) → Fin (n + 1) × (Fin (n + 1) ⊕ Fin (n + 1))` to `fun a => (a, Sum.inr a)`. Use `Finset.sum_pos' (fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)) ⟨g₀, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `h1 : pmWt g₀ = 1`.

Unfold `pmWt`. Rewrite using `[if_pos]`. Use extensionality with `x`. Simplify using `[g₀]`. Establish `h2 : pmGmat w g₀ = diagonal fun a => ((Real.sqrt (r a) : ℝ) : ℂ)`.

Use extensionality with `x a`. Distinguish the cases in `h : x = a`. Substitute `h` using the available equality. Simplify using `[pmGmat, w, g₀]`. Simplify using `[pmGmat, w, g₀, h]`.

Rewrite using `[h1, one_mul, h2, det_diagonal, Complex.normSq_pos]`. Use `Finset.prod_ne_zero_iff.mpr fun a _ => ?_` and prove the remaining obligations. Conclude with `(Real.sqrt_pos.mpr (hr a)).ne'` after adjusting the coercions.
-/
theorem mixedDiscriminant_pos_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosDef) : (mdisc A).im = 0 ∧ 0 < (mdisc A).re := by
  obtain _ | n := D
  · rw [mdisc_zero]; simp
  choose r hr v hv using fun k => pm_exists_gram_add_of_posDef (hA k)
  let w : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1)) → Fin (n + 1) → ℂ := fun k =>
    Sum.elim (v k) (fun s x => if x = s then ((Real.sqrt (r k) : ℝ) : ℂ) else 0)
  have hc : ∀ k, ((Real.sqrt (r k) : ℝ) : ℂ) * star ((Real.sqrt (r k) : ℝ) : ℂ) = (r k : ℂ) := by
    intro k
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr k).le]
  have hw : ∀ k a b, A k a b = ∑ s, w k s a * star (w k s b) := by
    intro k a b
    rw [hv, Fintype.sum_sum_type]
    congr 1
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, Finset.sum_eq_single a (fun s _ hs => by simp [w, Ne.symm hs]) (by simp)]
      simp only [w, Sum.elim_inr]
      exact (hc k).symm
    · rw [if_neg hab]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      by_cases has : a = s
      · subst has; simp [w, Ne.symm hab]
      · simp [w, has]
  rw [pm_mdisc_of_gram A w hw]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  refine div_pos ?_ (by positivity)
  let g₀ : Fin (n + 1) → Fin (n + 1) × (Fin (n + 1) ⊕ Fin (n + 1)) := fun a => (a, Sum.inr a)
  refine Finset.sum_pos' (fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _))
    ⟨g₀, Finset.mem_univ _, ?_⟩
  have h1 : pmWt g₀ = 1 := by
    unfold pmWt
    rw [if_pos]
    ext x; simp [g₀]
  have h2 : pmGmat w g₀ = diagonal fun a => ((Real.sqrt (r a) : ℝ) : ℂ) := by
    ext x a
    by_cases h : x = a
    · subst h; simp [pmGmat, w, g₀]
    · simp [pmGmat, w, g₀, h]
  rw [h1, one_mul, h2, det_diagonal, Complex.normSq_pos]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (hr a)).ne'

/- English proof (translation)
Use `choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)`. Use `choose u hu using fun k => pm_exists_gram_of_posSemidef (hAB k)`. Set `w : Fin D → (Fin D ⊕ Fin D) → Fin D → ℂ` to `fun k => Sum.elim (v k) (u k)`. Establish `hw : ∀ k a b, B k a b = ∑ s, w k s a * star (w k s b)`. Introduce `k a b`.

Establish `e : B k a b = A k a b + (B k - A k) a b` using `by simp`. Rewrite using `[e, hv, hu, Fintype.sum_sum_type]`. Both sides reduce to the same expression. Rewrite using `[pm_mdisc_of_gram A v hv, pm_mdisc_of_gram B w hw, Complex.ofReal_re, Complex.ofReal_re]`. Use `gcongr`.

Set `φ : (Fin D → Fin D × Fin D) → (Fin D → Fin D × (Fin D ⊕ Fin D))` to `fun g a => ((g a).1, Sum.inl (g a).2)`. Establish `hφ : Function.Injective φ`. Introduce `g h e`. Use function extensionality and compare the values at `a`. Use `congrFun e a` as an intermediate fact.

Simplify using `only [φ, Prod.mk.injEq, Sum.inl.injEq] at this`. Conclude with `Prod.ext this.1 this.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mixedDiscriminant_re_mono_of_gram (A B : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ k, (A k).PosSemidef)
    (hAB : ∀ k, (B k - A k).PosSemidef) : (mdisc A).re ≤ (mdisc B).re := by
  choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)
  choose u hu using fun k => pm_exists_gram_of_posSemidef (hAB k)
  let w : Fin D → (Fin D ⊕ Fin D) → Fin D → ℂ := fun k => Sum.elim (v k) (u k)
  have hw : ∀ k a b, B k a b = ∑ s, w k s a * star (w k s b) := by
    intro k a b
    have e : B k a b = A k a b + (B k - A k) a b := by simp
    rw [e, hv, hu, Fintype.sum_sum_type]
    rfl
  rw [pm_mdisc_of_gram A v hv, pm_mdisc_of_gram B w hw, Complex.ofReal_re, Complex.ofReal_re]
  gcongr
  let φ : (Fin D → Fin D × Fin D) → (Fin D → Fin D × (Fin D ⊕ Fin D)) :=
    fun g a => ((g a).1, Sum.inl (g a).2)
  have hφ : Function.Injective φ := by
    intro g h e
    funext a
    have := congrFun e a
    simp only [φ, Prod.mk.injEq, Sum.inl.injEq] at this
    exact Prod.ext this.1 this.2
  calc ∑ g : Fin D → Fin D × Fin D, pmWt g * Complex.normSq (pmGmat v g).det
      = ∑ g : Fin D → Fin D × Fin D, pmWt (φ g) * Complex.normSq (pmGmat w (φ g)).det :=
        Finset.sum_congr rfl fun g _ => rfl
    _ = ∑ g ∈ univ.image φ, pmWt g * Complex.normSq (pmGmat w g).det :=
        (Finset.sum_image (f := fun g => pmWt g * Complex.normSq (pmGmat w g).det)
          fun x _ y _ h => hφ h).symm
    _ ≤ ∑ g, pmWt g * Complex.normSq (pmGmat w g).det :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun g _ _ =>
          mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)

end ReciprocityTheory.AnForm.A
