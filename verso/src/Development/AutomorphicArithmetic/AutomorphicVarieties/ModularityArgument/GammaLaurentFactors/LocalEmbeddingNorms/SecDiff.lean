import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps

/- English proof (translation)
Use `⟨fun h0 => hP ((Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hr)).mp h0), fun z => ?_⟩` and prove the remaining obligations. Use `Polynomial.rootMultiplicity_comp_C_mul_X_add_C P r 0 z (isUnit_iff_ne_zero.mpr hr)` as an intermediate fact. Simplify using `using this`.
-/
private theorem comp_C_mul_X_ne_zero_and_rootMultiplicity {P : Polynomial ℂ} (hP : P ≠ 0) {r : ℂ} (hr : r ≠ 0) :
    P.comp (Polynomial.C r * Polynomial.X) ≠ 0 ∧
      ∀ z, (P.comp (Polynomial.C r * Polynomial.X)).rootMultiplicity z = P.rootMultiplicity (r * z) := by
  refine ⟨fun h0 => hP ((Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hr)).mp h0),
    fun z => ?_⟩
  have := Polynomial.rootMultiplicity_comp_C_mul_X_add_C P r 0 z (isUnit_iff_ne_zero.mpr hr)
  simpa using this

open Polynomial in
/- English proof (translation)
Introduce `q hq P P' c hP hP' h`. Establish `hqpos : (0 : ℝ) < q` using `by linarith`. Establish `hq0 : (q : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hqpos.ne'`. Establish `hqi : ((q : ℂ))⁻¹ ≠ 0` using `inv_ne_zero hq0`. Establish `hc : c = 1`.

Establish `h0` using `congrArg (Polynomial.eval 0) h`. Simplify using `[Polynomial.eval_comp, hP, hP'] at h0`. Use `first`. Consider the case `exact h0.symm`. Consider the case `exact h0`.

Substitute `hc` using the available equality. Establish `hPne : P ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hP`. Establish `hP'ne : P' ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hP'`. Take `⟨hA, mA⟩` from `comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hqi`. Take `⟨hB, mB⟩` from `comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hq0`. Take `⟨hA', mA'⟩` from `comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hqi`.

Take `⟨hB', mB'⟩` from `comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hq0`. Rewrite `h` using `[map_one, one_mul]`. Establish `key : ∀ z : ℂ, P.rootMultiplicity ((q : ℂ)⁻¹ * z) + P.rootMultiplicity ((q : ℂ) * z) + (P'.rootMultiplicity z + P'.rootMultiplicity z) = P'.rootMultiplicity ((q : ℂ)⁻¹ * z) + P'.rootMultiplicity ((q : ℂ) * z) + (P.rootMultiplicity z + P.rootMultiplicity z)`. Introduce `z`. Establish `hz` using `congrArg (Polynomial.rootMultiplicity z) h`.

Rewrite `hz` using `[Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hP'ne)), Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hPne)), Polynomial.rootMultiplicity_mul (mul_ne_zero hA hB), Polynomial.rootMultiplicity_mul (mul_ne_zero hA …`. Use linear arithmetic over natural numbers and integers. Take `⟨d, hd⟩ : ∃ d : ℂ → ℤ, ∀ z, d z = (P.rootMultiplicity z : ℤ) - P'.rootMultiplicity z` from `⟨_, fun z => rfl⟩`. Establish `rel : ∀ z, d ((q : ℂ)⁻¹ * z) + d ((q : ℂ) * z) = 2 * d z`. Introduce `z`.

Use `key z` as an intermediate fact. Simplify using `only [hd]`. Use linear arithmetic over natural numbers and integers. Establish `p0 : P.rootMultiplicity 0 = 0` using `Polynomial.rootMultiplicity_eq_zero (by`. Introduce `hr`.

Use `hr.eq_zero` as an intermediate fact. Simplify using `[hP] at this)`. Establish `p0' : P'.rootMultiplicity 0 = 0` using `Polynomial.rootMultiplicity_eq_zero (by`. Introduce `hr`. Use `hr.eq_zero` as an intermediate fact.

Simplify using `[hP'] at this)`. Establish `d0 : d 0 = 0` using `by simp [hd, p0, p0']`. Establish `supp : ∀ z, d z ≠ 0 → z ∈ (P * P').roots.toFinset`. Introduce `z hz`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots (mul_ne_zero hPne hP'ne)]`.

Express the relevant statement in the definitionally equal form `Polynomial.eval z (P * P') = 0`. Rewrite using `[Polynomial.eval_mul]`. Assume the negation of the conclusion as `hne`. Apply `hz` to reduce the goal to its premises. Establish `r1 : P.rootMultiplicity z = 0` using `Polynomial.rootMultiplicity_eq_zero (by`.

Introduce `hr`. Conclude with `hne (by rw [hr.eq_zero, zero_mul]))`. Establish `r2 : P'.rootMultiplicity z = 0` using `Polynomial.rootMultiplicity_eq_zero (by`. Introduce `hr`. Conclude with `hne (by rw [hr.eq_zero, mul_zero]))`.

Simplify using `[hd, r1, r2]`. Establish `hdz : ∀ z, d z = 0`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨z1, hz1⟩` from `hne`.

Use `set S := (P * P').roots.toFinset.filter (fun z => d z ≠ 0) with hS`. Establish `hSne : S.Nonempty` using `⟨z1, Finset.mem_filter.mpr ⟨supp z1 hz1, hz1⟩⟩`. Take `⟨z0, hz0S, hmax⟩` from `S.exists_max_image (fun z => ‖z‖) hSne`. Establish `hz0 : d z0 ≠ 0` using `(Finset.mem_filter.mp hz0S).2`. Establish `hz00 : z0 ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hz0 d0`. Establish `hnz0 : 0 < ‖z0‖` using `norm_pos_iff.mpr hz00`. Establish `hnorm : ∀ k : ℕ, ‖(q : ℂ)⁻¹ ^ k * z0‖ = q⁻¹ ^ k * ‖z0‖`. Introduce `k`.

Rewrite using `[norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]`. Establish `hup : d ((q : ℂ) * z0) = 0`. Assume the negation of the conclusion as `hne2`. Establish `hm` using `hmax _ (Finset.mem_filter.mpr ⟨supp _ hne2, hne2⟩)`. Rewrite `hm` using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `step : ∀ k : ℕ, d ((q : ℂ)⁻¹ ^ k * z0) = (k + 1) * d z0 ∧ d ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (k + 2) * d z0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Establish `r0` using `rel z0`. Rewrite `r0` using `[hup]`. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Simplify using `only [zero_add, pow_one, Nat.cast_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ k ih`. Use `⟨by rw [ih.2]; push_cast; ring, ?_⟩` and prove the remaining obligations. Establish `r1` using `rel ((q : ℂ)⁻¹ ^ (k + 1) * z0)`. Establish `e1 : (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ (k + 1 + 1) * z0` using `by ring`. Establish `e2 : (q : ℂ) * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ k * z0`.

Rewrite using `[pow_succ]`. Take the linear combination `((q : ℂ)⁻¹ ^ k * z0) * mul_inv_cancel₀ hq0`. Rewrite `r1` using `[e1, e2, ih.1, ih.2]`. Use `push_cast`. Take the linear combination `r1`.

Establish `hmem : ∀ k : ℕ, (q : ℂ)⁻¹ ^ k * z0 ∈ (S : Set ℂ)`. Introduce `k`. Establish `hk : d ((q : ℂ)⁻¹ ^ k * z0) ≠ 0`. Rewrite using `[(step k).1]`. Conclude with `mul_ne_zero (by positivity) hz0`.

Conclude with `Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨supp _ hk, hk⟩)`. Establish `hinj : Function.Injective (fun k : ℕ => (q : ℂ)⁻¹ ^ k * z0)`. Introduce `a b hab`. Establish `hn` using `congrArg norm hab`. Simplify using `only [hnorm] at hn`.

Establish `hab'` using `mul_right_cancel₀ hnz0.ne' hn`. Use `pow_right_injective₀ (inv_pos.mpr hqpos) ?_ hab'` and prove the remaining obligations. Introduce `h1`. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `Set.infinite_of_injective_forall_mem hinj hmem S.finite_toSet`. Establish `hm : ∀ z, P.rootMultiplicity z = P'.rootMultiplicity z`. Introduce `z`. Use `hdz z` as an intermediate fact. Rewrite `this` using `[hd]`.

Use linear arithmetic over natural numbers and integers. Establish `hroots : P.roots = P'.roots`. Use extensionality with `z`. Rewrite using `[Polynomial.count_roots, Polynomial.count_roots, hm]`. Establish `e1` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P) IsAlgClosed.card_roots_eq_natDegree`.

Establish `e2` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P') IsAlgClosed.card_roots_eq_natDegree`. Rewrite `e1` using `[hroots]`. Establish `v1` using `congrArg (Polynomial.eval 0) e1`. Establish `v2` using `congrArg (Polynomial.eval 0) e2`. Rewrite `v1` using `[Polynomial.eval_mul, Polynomial.eval_C, hP]`.

Rewrite `v2` using `[Polynomial.eval_mul, Polynomial.eval_C, hP']`. Establish `hlc : P.leadingCoeff = P'.leadingCoeff`. Establish `hne : Polynomial.eval 0 (Multiset.map (fun a => Polynomial.X - Polynomial.C a) P'.roots).prod ≠ 0`. Introduce `h0`. Rewrite `v2` using `[h0, mul_zero]`.

Conclude with `zero_ne_one v2`. Conclude with `mul_right_cancel₀ hne (v1.trans v2.symm)`. Rewrite `e1` using `[hlc]`. Conclude with `e1.symm.trans e2`.
-/
theorem UpperTheory.V.Z.Gam.secDiff :
    UpperTheory.V.Z.Gam.SecDiff := by
  classical
  intro q hq P P' c hP hP' h
  have hqpos : (0 : ℝ) < q := by linarith
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  have hqi : ((q : ℂ))⁻¹ ≠ 0 := inv_ne_zero hq0
  have hc : c = 1 := by
    have h0 := congrArg (Polynomial.eval 0) h
    simp [Polynomial.eval_comp, hP, hP'] at h0
    first
      | exact h0.symm
      | exact h0
  subst hc
  have hPne : P ≠ 0 := by
    rintro rfl
    simp at hP
  have hP'ne : P' ≠ 0 := by
    rintro rfl
    simp at hP'
  obtain ⟨hA, mA⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hqi
  obtain ⟨hB, mB⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hq0
  obtain ⟨hA', mA'⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hqi
  obtain ⟨hB', mB'⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hq0
  rw [map_one, one_mul] at h
  have key : ∀ z : ℂ, P.rootMultiplicity ((q : ℂ)⁻¹ * z) + P.rootMultiplicity ((q : ℂ) * z) +
      (P'.rootMultiplicity z + P'.rootMultiplicity z) =
      P'.rootMultiplicity ((q : ℂ)⁻¹ * z) + P'.rootMultiplicity ((q : ℂ) * z) +
      (P.rootMultiplicity z + P.rootMultiplicity z) := by
    intro z
    have hz := congrArg (Polynomial.rootMultiplicity z) h
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hP'ne)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hPne)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA hB),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA' hB'), sq, sq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hP'ne hP'ne),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hPne hPne), mA, mB, mA', mB'] at hz
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℤ, ∀ z, d z = (P.rootMultiplicity z : ℤ) - P'.rootMultiplicity z :=
    ⟨_, fun z => rfl⟩
  have rel : ∀ z, d ((q : ℂ)⁻¹ * z) + d ((q : ℂ) * z) = 2 * d z := by
    intro z
    have := key z
    simp only [hd]
    omega
  have p0 : P.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    intro hr
    have := hr.eq_zero
    simp [hP] at this)
  have p0' : P'.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    intro hr
    have := hr.eq_zero
    simp [hP'] at this)
  have d0 : d 0 = 0 := by simp [hd, p0, p0']
  have supp : ∀ z, d z ≠ 0 → z ∈ (P * P').roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (mul_ne_zero hPne hP'ne)]
    change Polynomial.eval z (P * P') = 0
    rw [Polynomial.eval_mul]
    by_contra hne
    apply hz
    have r1 : P.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero (by
      intro hr
      exact hne (by rw [hr.eq_zero, zero_mul]))
    have r2 : P'.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero (by
      intro hr
      exact hne (by rw [hr.eq_zero, mul_zero]))
    simp [hd, r1, r2]
  have hdz : ∀ z, d z = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨z1, hz1⟩ := hne
    set S := (P * P').roots.toFinset.filter (fun z => d z ≠ 0) with hS
    have hSne : S.Nonempty := ⟨z1, Finset.mem_filter.mpr ⟨supp z1 hz1, hz1⟩⟩
    obtain ⟨z0, hz0S, hmax⟩ := S.exists_max_image (fun z => ‖z‖) hSne
    have hz0 : d z0 ≠ 0 := (Finset.mem_filter.mp hz0S).2
    have hz00 : z0 ≠ 0 := by
      rintro rfl
      exact hz0 d0
    have hnz0 : 0 < ‖z0‖ := norm_pos_iff.mpr hz00
    have hnorm : ∀ k : ℕ, ‖(q : ℂ)⁻¹ ^ k * z0‖ = q⁻¹ ^ k * ‖z0‖ := by
      intro k
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
    have hup : d ((q : ℂ) * z0) = 0 := by
      by_contra hne2
      have hm := hmax _ (Finset.mem_filter.mpr ⟨supp _ hne2, hne2⟩)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos] at hm
      nlinarith
    have step : ∀ k : ℕ, d ((q : ℂ)⁻¹ ^ k * z0) = (k + 1) * d z0 ∧
        d ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (k + 2) * d z0 := by
      intro k
      induction k with
      | zero =>
        have r0 := rel z0
        rw [hup] at r0
        refine ⟨by simp, ?_⟩
        simp only [zero_add, pow_one, Nat.cast_zero]
        linarith
      | succ k ih =>
        refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
        have r1 := rel ((q : ℂ)⁻¹ ^ (k + 1) * z0)
        have e1 : (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ (k + 1 + 1) * z0 := by ring
        have e2 : (q : ℂ) * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ k * z0 := by
          rw [pow_succ]
          linear_combination ((q : ℂ)⁻¹ ^ k * z0) * mul_inv_cancel₀ hq0
        rw [e1, e2, ih.1, ih.2] at r1
        push_cast
        linear_combination r1
    have hmem : ∀ k : ℕ, (q : ℂ)⁻¹ ^ k * z0 ∈ (S : Set ℂ) := by
      intro k
      have hk : d ((q : ℂ)⁻¹ ^ k * z0) ≠ 0 := by
        rw [(step k).1]
        exact mul_ne_zero (by positivity) hz0
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨supp _ hk, hk⟩)
    have hinj : Function.Injective (fun k : ℕ => (q : ℂ)⁻¹ ^ k * z0) := by
      intro a b hab
      have hn := congrArg norm hab
      simp only [hnorm] at hn
      have hab' := mul_right_cancel₀ hnz0.ne' hn
      refine pow_right_injective₀ (inv_pos.mpr hqpos) ?_ hab'
      intro h1
      simp at h1
      linarith
    exact Set.infinite_of_injective_forall_mem hinj hmem S.finite_toSet
  have hm : ∀ z, P.rootMultiplicity z = P'.rootMultiplicity z := by
    intro z
    have := hdz z
    rw [hd] at this
    omega
  have hroots : P.roots = P'.roots := by
    ext z
    rw [Polynomial.count_roots, Polynomial.count_roots, hm]
  have e1 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
    IsAlgClosed.card_roots_eq_natDegree
  have e2 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P')
    IsAlgClosed.card_roots_eq_natDegree
  rw [hroots] at e1
  have v1 := congrArg (Polynomial.eval 0) e1
  have v2 := congrArg (Polynomial.eval 0) e2
  rw [Polynomial.eval_mul, Polynomial.eval_C, hP] at v1
  rw [Polynomial.eval_mul, Polynomial.eval_C, hP'] at v2
  have hlc : P.leadingCoeff = P'.leadingCoeff := by
    have hne : Polynomial.eval 0
        (Multiset.map (fun a => Polynomial.X - Polynomial.C a) P'.roots).prod ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at v2
      exact zero_ne_one v2
    exact mul_right_cancel₀ hne (v1.trans v2.symm)
  rw [hlc] at e1
  exact e1.symm.trans e2
