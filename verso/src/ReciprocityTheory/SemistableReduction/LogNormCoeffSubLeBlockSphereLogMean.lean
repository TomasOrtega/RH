import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial NumberField

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `h1` using `harmonic_le_one_add_log (m + 1)`. Establish `h2 : harmonic (m + 1 - 1) ≤ harmonic (m + 1)`. Establish `e : m + 1 - 1 = m` using `by omega`. Rewrite using `[e, harmonic_succ]`.

Establish `: (0 : ℚ) ≤ (((m + 1 : ℕ) : ℚ))⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (harmonic (m + 1 - 1) : ℝ) ≤ harmonic (m + 1)` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem harmonic_pred_le_one_add_log {n : ℕ} (hn : 0 < n) : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := harmonic_le_one_add_log (m + 1)
  have h2 : harmonic (m + 1 - 1) ≤ harmonic (m + 1) := by
    have e : m + 1 - 1 = m := by omega
    rw [e, harmonic_succ]
    have : (0 : ℚ) ≤ (((m + 1 : ℕ) : ℚ))⁻¹ := by positivity
    linarith
  have h3 : (harmonic (m + 1 - 1) : ℝ) ≤ harmonic (m + 1) := by exact_mod_cast h2
  linarith

/- English proof (translation)
Take `⟨z, hz1, hzc⟩` from `exists_torus_coeff_le g s`. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast hn`. Use `set r : ℝ := Real.sqrt n with hrdef`. Establish `hr : 0 < r` using `Real.sqrt_pos.mpr hnpos`. Establish `hr2 : r ^ 2 = n` using `Real.sq_sqrt hnpos.le`.

Establish `hmem : ∀ b : Fin B, (WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)) : EuclideanSpace ℂ (Fin n)) ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1`. Introduce `b`. Establish `hj : ∀ j, ‖z (b, j) / (r : ℂ)‖ = 1 / r`. Introduce `j`. Rewrite using `[norm_div, hz1, Complex.norm_of_nonneg hr.le]`.

Rewrite using `[mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]`. Simplify using `only [PiLp.toLp_apply, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[div_pow, one_pow, hr2, mul_one_div_cancel hnpos.ne', Real.sqrt_one]`. Set `u : BlockSphere B n` to `fun b => ⟨WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)), hmem b⟩`. Establish `hrC : (r : ℂ) ≠ 0` using `by exact_mod_cast hr.ne'`.

Establish `hz' : (fun p => (r : ℂ) * blockPoint u p) = z`. Use function extensionality and compare the values at `p`. Simplify using `only [blockPoint, spherePoint, u, PiLp.toLp_apply]`. Clear the denominators using the available nonvanishing facts. Establish `hev` using `eval_mul_of_isMultiHomogeneous hg (r : ℂ) (blockPoint u)`.

Rewrite `hev` using `[hz']`. Establish `hcpos : 0 < ‖g.coeff s‖` using `norm_pos_iff.mpr hs`. Establish `hgz : 0 < ‖eval z g‖` using `lt_of_lt_of_le hcpos hzc`. Establish `hnorm : ‖eval z g‖ = r ^ (∑ b, a b) * ‖eval (blockPoint u) g‖`. Rewrite using `[hev, norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]`.

Establish `hgu : eval (blockPoint u) g ≠ 0`. Introduce `h0`. Rewrite `hgz` using `[hnorm, h0, norm_zero, mul_zero]`. Conclude with `lt_irrefl _ hgz`. Establish `hbb` using `blockSphere_logMean_bound hSJ hInt hn B a g u hg hgu`.

Establish `hH` using `harmonic_pred_le_one_add_log hn`. Establish `hlogr : Real.log r = Real.log n / 2` using `Real.log_sqrt hnpos.le`. Establish `hlz : Real.log ‖eval z g‖ = ((∑ b, a b : ℕ) : ℝ) * Real.log r + Real.log ‖eval (blockPoint u) g‖`. Rewrite using `[hnorm, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hgu), Real.log_pow]`. Establish `hlc : Real.log ‖g.coeff s‖ ≤ Real.log ‖eval z g‖` using `Real.log_le_log hcpos hzc`.

Use `set A : ℝ := ∑ b, (a b : ℝ) with hAdef`. Establish `hsum : ((∑ b, a b : ℕ) : ℝ) = A` using `by rw [hAdef]; push_cast; rfl`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg (fun b _ => Nat.cast_nonneg _)`. Establish `hmul : A / 2 * (harmonic (n - 1) : ℝ) ≤ A / 2 * (1 + Real.log n)` using `mul_le_mul_of_nonneg_left hH (by positivity)`. Establish `hgoal : ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) = A * (Real.log n + 1 / 2)`.

Rewrite using `[hAdef, Finset.sum_mul]`. Rewrite using `[hgoal]`. Rewrite `hlz` using `[hsum, hlogr]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_norm_coeff_sub_le_blockSphereLogMean (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {B n : ℕ}
    (hn : 0 < n) {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (s : Fin B × Fin n →₀ ℕ) (hs : g.coeff s ≠ 0) :
    Real.log ‖g.coeff s‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤ blockSphereMean B n g := by
  obtain ⟨z, hz1, hzc⟩ := exists_torus_coeff_le g s
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt n with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hnpos
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnpos.le

  have hmem : ∀ b : Fin B, (WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)) : EuclideanSpace ℂ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 := by
    intro b
    have hj : ∀ j, ‖z (b, j) / (r : ℂ)‖ = 1 / r := by
      intro j
      rw [norm_div, hz1, Complex.norm_of_nonneg hr.le]
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [PiLp.toLp_apply, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_pow, one_pow, hr2, mul_one_div_cancel hnpos.ne', Real.sqrt_one]
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)), hmem b⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : (fun p => (r : ℂ) * blockPoint u p) = z := by
    funext p
    simp only [blockPoint, spherePoint, u, PiLp.toLp_apply]
    field_simp
  have hev := eval_mul_of_isMultiHomogeneous hg (r : ℂ) (blockPoint u)
  rw [hz'] at hev
  have hcpos : 0 < ‖g.coeff s‖ := norm_pos_iff.mpr hs
  have hgz : 0 < ‖eval z g‖ := lt_of_lt_of_le hcpos hzc
  have hnorm : ‖eval z g‖ = r ^ (∑ b, a b) * ‖eval (blockPoint u) g‖ := by
    rw [hev, norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]
  have hgu : eval (blockPoint u) g ≠ 0 := by
    intro h0
    rw [hnorm, h0, norm_zero, mul_zero] at hgz
    exact lt_irrefl _ hgz
  have hbb := blockSphere_logMean_bound hSJ hInt hn B a g u hg hgu
  have hH := harmonic_pred_le_one_add_log hn
  have hlogr : Real.log r = Real.log n / 2 := Real.log_sqrt hnpos.le
  have hlz : Real.log ‖eval z g‖ =
      ((∑ b, a b : ℕ) : ℝ) * Real.log r + Real.log ‖eval (blockPoint u) g‖ := by
    rw [hnorm, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hgu), Real.log_pow]
  have hlc : Real.log ‖g.coeff s‖ ≤ Real.log ‖eval z g‖ := Real.log_le_log hcpos hzc
  set A : ℝ := ∑ b, (a b : ℝ) with hAdef
  have hsum : ((∑ b, a b : ℕ) : ℝ) = A := by rw [hAdef]; push_cast; rfl
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun b _ => Nat.cast_nonneg _)
  have hmul : A / 2 * (harmonic (n - 1) : ℝ) ≤ A / 2 * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hgoal : ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) = A * (Real.log n + 1 / 2) := by
    rw [hAdef, Finset.sum_mul]
  rw [hgoal]
  rw [hsum, hlogr] at hlz
  nlinarith

/- English proof (translation)
Establish `hc : f.coeff s ≠ 0` using `MvPolynomial.mem_support_iff.mp hs`. Establish `hA : ∀ w : FinitePlace K, w (f.coeff s) ≤ gaussAbs w f`. Introduce `w`. Unfold `gaussAbs`. Establish `h1` using `Finset.le_sup (f := fun t => (w (f.coeff t)).toNNReal) hs`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpos : ∀ w : FinitePlace K, 0 < w (f.coeff s)` using `fun w => NumberField.FinitePlace.pos_iff.mpr hc`. Establish `hU : (⋃ t ∈ f.support, Function.mulSupport (fun w : FinitePlace K => w (f.coeff t))).Finite` using `Set.Finite.biUnion f.support.finite_toSet (fun t ht => NumberField.FinitePlace.mulSupport_finite (MvPolynomial.mem_support_iff.mp ht))`. Use `set T := hU.toFinset with hT`. Establish `hsubG : Function.support (fun w : FinitePlace K => Real.log (gaussAbs w f)) ⊆ (T : Set _)`.

Introduce `w hw`. Rewrite using `[hT, Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `hnot`. Apply `hw` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot`.

Establish `h1 : gaussAbs w f = 1`. Unfold `gaussAbs`. Establish `hne : f.support.Nonempty` using `⟨s, hs⟩`. Rewrite using `[Finset.sup_congr rfl (g := fun _ => (1 : NNReal)) (fun t ht => by simp [hnot t ht]), Finset.sup_const hne]`. Simplify using the standard rewrite rules.

Simplify using `[h1]`. Establish `hsubW : Function.mulSupport (fun w : FinitePlace K => w (f.coeff s)) ⊆ (T : Set _)`. Introduce `w hw`. Rewrite using `[hT, Set.Finite.coe_toFinset]`. Conclude with `Set.mem_biUnion hs hw`.

Establish `hprod` using `NumberField.FinitePlace.prod_eq_inv_abs_norm hc`. Rewrite `hprod` using `[finprod_eq_prod_of_mulSupport_subset _ hsubW]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsubG]`. Establish `hlog : Real.log (∏ w ∈ T, w (f.coeff s)) = ∑ w ∈ T, Real.log (w (f.coeff s))` using `Real.log_prod (fun w _ => (hpos w).ne')`. Rewrite `hlog` using `[hprod]`.

Establish `hle : ∑ w ∈ T, Real.log (w (f.coeff s)) ≤ ∑ w ∈ T, Real.log (gaussAbs w f)` using `Finset.sum_le_sum (fun w _ => Real.log_le_log (hpos w) (hA w))`. Move the coercions through the operations in `at hlog`. Rewrite `hlog` using `[Real.log_inv]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem neg_log_norm_coeff_le_finitePlaces {K : Type*} [Field K] [NumberField K] {ι : Type*} (f : MvPolynomial ι K)
    (s : ι →₀ ℕ) (hs : s ∈ f.support) :
    -Real.log |((Algebra.norm ℚ (f.coeff s) : ℚ) : ℝ)| ≤
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) := by
  classical
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hA : ∀ w : FinitePlace K, w (f.coeff s) ≤ gaussAbs w f := by
    intro w
    unfold gaussAbs
    have h1 := Finset.le_sup (f := fun t => (w (f.coeff t)).toNNReal) hs
    calc w (f.coeff s) ≤ ((w (f.coeff s)).toNNReal : ℝ) := Real.le_coe_toNNReal _
      _ ≤ _ := by exact_mod_cast h1
  have hpos : ∀ w : FinitePlace K, 0 < w (f.coeff s) := fun w => NumberField.FinitePlace.pos_iff.mpr hc
  have hU : (⋃ t ∈ f.support, Function.mulSupport (fun w : FinitePlace K => w (f.coeff t))).Finite :=
    Set.Finite.biUnion f.support.finite_toSet
      (fun t ht => NumberField.FinitePlace.mulSupport_finite (MvPolynomial.mem_support_iff.mp ht))
  set T := hU.toFinset with hT
  have hsubG : Function.support (fun w : FinitePlace K => Real.log (gaussAbs w f)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    by_contra hnot
    apply hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
    have h1 : gaussAbs w f = 1 := by
      unfold gaussAbs
      have hne : f.support.Nonempty := ⟨s, hs⟩
      rw [Finset.sup_congr rfl (g := fun _ => (1 : NNReal)) (fun t ht => by simp [hnot t ht]),
        Finset.sup_const hne]
      simp
    simp [h1]
  have hsubW : Function.mulSupport (fun w : FinitePlace K => w (f.coeff s)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    exact Set.mem_biUnion hs hw
  have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm hc
  rw [finprod_eq_prod_of_mulSupport_subset _ hsubW] at hprod
  rw [finsum_eq_sum_of_support_subset _ hsubG]
  have hlog : Real.log (∏ w ∈ T, w (f.coeff s)) = ∑ w ∈ T, Real.log (w (f.coeff s)) :=
    Real.log_prod (fun w _ => (hpos w).ne')
  rw [hprod] at hlog
  have hle : ∑ w ∈ T, Real.log (w (f.coeff s)) ≤ ∑ w ∈ T, Real.log (gaussAbs w f) :=
    Finset.sum_le_sum (fun w _ => Real.log_le_log (hpos w) (hA w))
  push_cast at hlog
  rw [Real.log_inv] at hlog
  linarith

/- English proof (translation)
Establish `hne : ∀ σ : K →+* ℂ, ‖σ c‖ ≠ 0` using `fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc)`. Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ c`. Establish `h2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c` using `Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)`. Establish `hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |((Algebra.norm ℚ c : ℚ) : ℝ)|`. Rewrite using `[← norm_prod, h2, ← h]`.

Simplify using `[Complex.norm_ratCast]`. Rewrite using `[← hprod, Real.log_prod (fun σ _ => hne σ)]`.
-/
theorem sum_log_norm_embedding_eq {K : Type*} [Field K] [NumberField K] (c : K) (hc : c ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  classical
  have hne : ∀ σ : K →+* ℂ, ‖σ c‖ ≠ 0 := fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ c
  have h2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
    rw [← norm_prod, h2, ← h]
    simp [Complex.norm_ratCast]
  rw [← hprod, Real.log_prod (fun σ _ => hne σ)]

end ReciprocityTheory.MultiplicativeHeights
