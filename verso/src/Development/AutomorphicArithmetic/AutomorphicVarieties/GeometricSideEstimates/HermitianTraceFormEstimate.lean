import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Simplify using `[ell, Matrix.trace, Finset.sum_apply]`.
-/
private theorem ell_toL' (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

/- English proof (translation)
Establish `h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a` using `Algebra.subset_adjoin ⟨{ toFun := fun x => star (x i w), map_add' := fun x y => by simp, map_smul' := fun c x => by simp }, rfl⟩`. Establish `h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a` using `Algebra.subset_adjoin ⟨{ toFun := fun x => x j w, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }, rfl⟩`. Conclude with `mul_mem h1 h2`.
-/
private theorem mono_mem (i j : Fin a) (w : InfinitePlace E) :
    (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
  have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
    Algebra.subset_adjoin ⟨{ toFun := fun x => star (x i w), map_add' := fun x y => by simp, map_smul' := fun c x => by simp }, rfl⟩
  have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
    Algebra.subset_adjoin ⟨{ toFun := fun x => x j w, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }, rfl⟩
  exact mul_mem h1 h2

/- English proof (translation)
Establish `h : star M.1 = M.1` using `M.2`. Establish `h2 : ∀ i, ((M.1 i i w).re : ℂ) = M.1 i i w` using `fun i => by`. Use `congrFun (congrFun (congrFun h i) i) w` as an intermediate fact. Conclude with `Complex.conj_eq_iff_re.1 this`. Simplify using `only [Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum, Complex.ofReal_sum, h2]`.
-/
private theorem herm_trace (M : Herm E a) (w : InfinitePlace E) : (((M.1.trace w).re : ℝ) : ℂ) = ∑ i, M.1 i i w := by
  have h : star M.1 = M.1 := M.2
  have h2 : ∀ i, ((M.1 i i w).re : ℂ) = M.1 i i w := fun i => by
    have := congrFun (congrFun (congrFun h i) i) w
    exact Complex.conj_eq_iff_re.1 this
  simp only [Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum, Complex.ofReal_sum, h2]

/- English proof (translation)
The claim follows from `|trF X X| ≤ (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (‖toL X‖ * ‖toL X‖))) := by have hX : ∀ i j w, ‖X i j w‖ ≤ ‖toL X‖ := fun i j w => ((norm_le_pi_norm (toL X i j) w).trans (norm_le_pi_norm (toL X i) j)).trans (norm_le_pi_norm (toL X) i) unfold trF refine (Finset.abs_su …`.
-/
private theorem trF_bd (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    |trF X X| ≤ (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (‖toL X‖ * ‖toL X‖))) := by
  have hX : ∀ i j w, ‖X i j w‖ ≤ ‖toL X‖ := fun i j w =>
    ((norm_le_pi_norm (toL X i j) w).trans (norm_le_pi_norm (toL X i) j)).trans (norm_le_pi_norm (toL X) i)
  unfold trF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (a * (‖toL X‖ * ‖toL X‖))) fun w _ => ?_).trans (by simp)
  refine (Complex.abs_re_le_norm _).trans ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (‖toL X‖ * ‖toL X‖)) fun i _ => ?_).trans (by simp)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((‖toL X‖ * ‖toL X‖)) fun j _ => ?_).trans (by simp)
  rw [norm_mul]
  exact mul_le_mul (hX _ _ _) (hX _ _ _) (norm_nonneg _) (norm_nonneg _)

end

/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Take `⟨-, hM⟩` from `UpperTheory.hermitian_space_geometric_estimate E a ha L hL`. Establish `h1 : (a : ℝ) ≠ 0` using `by exact_mod_cast (by omega : a ≠ 0)`. Establish `h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hone : ell E a (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1` using `(UpperTheory.V.Lit.Bor.ellFacts E a).1 ha`.

Establish `hdev : ∀ g, (dev L g).1 = (mom L g).1 - ell E a (toL (mom L g).1) • (1 : Matrix (Fin a) (Fin a) (Cinf E))` using `fun g => rfl`. Establish `hdevL : ∀ g, toL (dev L g).1 = toL (mom L g).1 - ell E a (toL (mom L g).1) • toL (1 : Matrix (Fin a) (Fin a) (Cinf E))` using `fun g => rfl`. Establish `hmom : ∀ i j w, (fun g => (mom L g).1 i j w) ∈ meanAlg L` using `fun i j w => Algebra.subset_adjoin ⟨_, mono_mem i j w, rfl⟩`. Establish `hell : ∀ g, ell E a (toL (dev L g).1) = 0` using `fun g => by`. Rewrite using `[hdevL, map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_self]`.

Use `⟨fun i j w => ?_, ?_, fun g => ⟨hell g, ?_⟩⟩` and prove the remaining obligations. Establish `e : (fun g => (dev L g).1 i j w) = (fun g => (mom L g).1 i j w) - ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w / ((a : ℂ) * Fintype.card (InfinitePlace E))) • ∑ w' : InfinitePlace E, ∑ k, fun g => (mom L g).1 k k w'`. Use function extensionality and compare the values at `g`. Simplify using `only [hdev, ell_toL', Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, ← herm_trace, Complex.real_smul, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem (hmom i j w) (Subalgebra.smul_mem _ (sum_mem fun w' _ => sum_mem fun k _ => hmom k k w') _)`. Use `choose C hC using fun (p : Fin a × Fin a × InfinitePlace E) => (hM _ (mono_mem p.1 p.2.1 p.2.2)).2`. Take `⟨B₀, hB₀⟩` from `(Set.finite_range C).bddAbove`.

Establish `hB : ∀ g, ‖toL (mom L g).1‖ ≤ |B₀|` using `fun g => by`. Use `(pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun w => ?_` and prove the remaining obligations. Conclude with `((hC (i, j, w) g).trans (hB₀ ⟨_, rfl⟩)).trans (le_abs_self _)`. Take `⟨K, hK, hKb⟩` from `(LinearMap.toContinuousLinearMap (ell E a)).bound`. Use `set B₁ : ℝ := |B₀| + K * |B₀| * ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ with hB₁`.

Establish `hD : ∀ g, ‖toL (dev L g).1‖ ≤ B₁` using `fun g => by`. Rewrite using `[hdevL]`. Use `(norm_sub_le _ _).trans (add_le_add (hB g) ?_)` and prove the remaining obligations. Rewrite using `[norm_smul]`. Use `mul_le_mul_of_nonneg_right ((hKb _).trans ?_) (norm_nonneg _)` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left (hB g) hK.le`. Establish `hB1 : 0 ≤ B₁` using `by positivity`. Use `set B₂ : ℝ := (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (B₁ * B₁))) with hB₂`. Establish `hB2 : 0 ≤ B₂` using `by positivity`. Establish `hB0` using `abs_nonneg B₀`.

Use `⟨|B₀| + B₁ + B₂ + 1, by positivity, fun g => ⟨by linarith [hB g], by linarith [hD g], ?_⟩⟩` and prove the remaining obligations. Establish `: |trF (dev L g).1 (dev L g).1| ≤ B₂`. Use `(trF_bd _).trans ?_` and prove the remaining obligations. Use `hD g` as an intermediate fact. Rewrite using `[hB₂]`.

Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0` using `hell g`. Rewrite `h0` using `[ell_toL', div_eq_zero_iff]`. Establish `h0'` using `h0.resolve_right (mul_ne_zero h1 h2)`.

Establish `e : (dev L g).1 * (dev L g).1 = (mom L g).1 * (dev L g).1 - ell E a (toL (mom L g).1) • (dev L g).1` using `by conv_lhs => rw [hdev g]`. Rewrite using `[sub_mul, smul_mul_assoc, one_mul, ← hdev]`. Unfold `trF`. Rewrite using `[e]`. Simplify using `only [Matrix.trace_sub, Matrix.trace_smul, Pi.sub_apply, Pi.smul_apply, Complex.sub_re, Complex.smul_re, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0', mul_zero, sub_zero]`.
-/
theorem UpperTheory.hermitian_trace_form_estimate :
    DevFacts := by
  intro E _ _ _ a ha L hL
  obtain ⟨-, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hone : ell E a (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1 := (UpperTheory.V.Lit.Bor.ellFacts E a).1 ha
  have hdev : ∀ g, (dev L g).1 = (mom L g).1 - ell E a (toL (mom L g).1) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := fun g => rfl
  have hdevL : ∀ g, toL (dev L g).1 = toL (mom L g).1 - ell E a (toL (mom L g).1) • toL (1 : Matrix (Fin a) (Fin a) (Cinf E)) := fun g => rfl
  have hmom : ∀ i j w, (fun g => (mom L g).1 i j w) ∈ meanAlg L := fun i j w =>
    Algebra.subset_adjoin ⟨_, mono_mem i j w, rfl⟩
  have hell : ∀ g, ell E a (toL (dev L g).1) = 0 := fun g => by
    rw [hdevL, map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_self]
  refine ⟨fun i j w => ?_, ?_, fun g => ⟨hell g, ?_⟩⟩
  · have e : (fun g => (dev L g).1 i j w) = (fun g => (mom L g).1 i j w) -
        ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w / ((a : ℂ) * Fintype.card (InfinitePlace E))) •
          ∑ w' : InfinitePlace E, ∑ k, fun g => (mom L g).1 k k w' := by
      funext g
      simp only [hdev, ell_toL', Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
        ← herm_trace, Complex.real_smul, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact sub_mem (hmom i j w) (Subalgebra.smul_mem _ (sum_mem fun w' _ => sum_mem fun k _ => hmom k k w') _)
  · choose C hC using fun (p : Fin a × Fin a × InfinitePlace E) => (hM _ (mono_mem p.1 p.2.1 p.2.2)).2
    obtain ⟨B₀, hB₀⟩ := (Set.finite_range C).bddAbove
    have hB : ∀ g, ‖toL (mom L g).1‖ ≤ |B₀| := fun g => by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j =>
        (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun w => ?_
      exact ((hC (i, j, w) g).trans (hB₀ ⟨_, rfl⟩)).trans (le_abs_self _)
    obtain ⟨K, hK, hKb⟩ := (LinearMap.toContinuousLinearMap (ell E a)).bound
    set B₁ : ℝ := |B₀| + K * |B₀| * ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ with hB₁
    have hD : ∀ g, ‖toL (dev L g).1‖ ≤ B₁ := fun g => by
      rw [hdevL]
      refine (norm_sub_le _ _).trans (add_le_add (hB g) ?_)
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ((hKb _).trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hB g) hK.le
    have hB1 : 0 ≤ B₁ := by positivity
    set B₂ : ℝ := (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (B₁ * B₁))) with hB₂
    have hB2 : 0 ≤ B₂ := by positivity
    have hB0 := abs_nonneg B₀
    refine ⟨|B₀| + B₁ + B₂ + 1, by positivity, fun g => ⟨by linarith [hB g], by linarith [hD g], ?_⟩⟩
    have : |trF (dev L g).1 (dev L g).1| ≤ B₂ := by
      refine (trF_bd _).trans ?_
      have := hD g
      rw [hB₂]
      gcongr
    linarith
  · have h0 := hell g
    rw [ell_toL', div_eq_zero_iff] at h0
    have h0' := h0.resolve_right (mul_ne_zero h1 h2)
    have e : (dev L g).1 * (dev L g).1 = (mom L g).1 * (dev L g).1 - ell E a (toL (mom L g).1) • (dev L g).1 := by
      conv_lhs => rw [hdev g]
      rw [sub_mul, smul_mul_assoc, one_mul, ← hdev]
    unfold trF
    rw [e]
    simp only [Matrix.trace_sub, Matrix.trace_smul, Pi.sub_apply, Pi.smul_apply, Complex.sub_re, Complex.smul_re,
      smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0', mul_zero, sub_zero]
