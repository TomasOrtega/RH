import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ContinuousGK

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `first`. Consider the case `(rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p])`. Consider the case `(rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p])`. Consider the case `(have h1 := PadicAlgCl.norm_extends p (p : ℚ_[p]); rw [map_natCast] at h1; rw [h1, Padic.norm_p])`. Consider the case `simp [Padic.norm_p]`.
-/
theorem norm_natCast_padicAlgCl : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  first
  | (rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p])
  | (rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p])
  | (have h1 := PadicAlgCl.norm_extends p (p : ℚ_[p]); rw [map_natCast] at h1; rw [h1, Padic.norm_p])
  | simp [Padic.norm_p]

/- English proof (translation)
Establish `hs : ∀ y ∈ A, τ y ∈ A`. Introduce `y hy`. Establish `h2` using `ValuationSubring.smul_mem_pointwise_smul τ y A hy`. Use `letI : MulAction (Ω ≃ₐ[F] Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction`. Establish `hsA` using `MulAction.mem_stabilizer_iff.mp hτ`.

Use `first`. Consider the case `(rw [hsA] at h2; exact h2)`. Consider the case `exact hsA ▸ h2`. Consider the case `(simp only [hsA] at h2; exact h2)`. Consider the case `(erw [hsA] at h2; exact h2)`.

Establish `key : ∀ y, ‖ι y‖ ≤ 1 → ‖ι (τ y)‖ ≤ 1` using `fun y hy => (h (τ y)).1 (hs y ((h y).2 hy))`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hc : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hpa : (0 : ℝ) < p` using `by linarith`.

Establish `ha : 0 < ‖ι x‖`. Break down `(norm_nonneg (ι x)).lt_or_eq with h0 | h0` into its components or cases. Conclude with `h0`. It suffices to derive a contradiction. Establish `h1 : ι x = 0` using `norm_eq_zero.mp h0.symm`.

Establish `hx : x = 0` using `(map_eq_zero ι).mp h1`. Substitute `hx` using the available equality. Simplify using `at hlt`. Establish `hr : 1 < ‖ι (τ x)‖ / ‖ι x‖` using `(one_lt_div ha).mpr hlt`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (p : ℝ) hr`.

Take `⟨m, hm1, hm2⟩` from `exists_mem_Ico_zpow (pow_pos ha n) hc`. Establish `hbn : (p : ℝ) * ‖ι x‖ ^ n < ‖ι (τ x)‖ ^ n`. Rewrite `hn` using `[div_pow]`. Use `first`. Consider the case `exact (lt_div_iff₀ (pow_pos ha n)).mp hn`.

Consider the case `exact (lt_div_iff (pow_pos ha n)).mp hn`. Establish `h3 : (p : ℝ) ^ (m + 1) < ‖ι (τ x)‖ ^ n`. Rewrite using `[zpow_add_one₀ hpa.ne']`. Combine the equalities or inequalities in the displayed calculation. Establish `hz : (0 : ℝ) < (p : ℝ) ^ (m + 1)` using `by first`.

Consider the case `exact zpow_pos hpa _`. Consider the case `exact zpow_pos_of_pos hpa _`. Establish `hk` using `key (x ^ n * (p : Ω) ^ (m + 1)) (by`. Simplify using `only [map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow, norm_natCast_padicAlgCl, inv_zpow]`. Rewrite using `[← div_eq_mul_inv, div_le_one hz]`.

Conclude with `hm2.le)`. Simplify using `only [map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow, norm_natCast_padicAlgCl, inv_zpow] at hk`. Rewrite `hk` using `[← div_eq_mul_inv, div_le_one hz]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_apply_le_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : ‖ι (τ x)‖ ≤ ‖ι x‖ := by
  have hs : ∀ y ∈ A, τ y ∈ A := by
    intro y hy
    have h2 := ValuationSubring.smul_mem_pointwise_smul τ y A hy
    letI : MulAction (Ω ≃ₐ[F] Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
    have hsA := MulAction.mem_stabilizer_iff.mp hτ
    first
    | (rw [hsA] at h2; exact h2)
    | exact hsA ▸ h2
    | (simp only [hsA] at h2; exact h2)
    | (erw [hsA] at h2; exact h2)
  have key : ∀ y, ‖ι y‖ ≤ 1 → ‖ι (τ y)‖ ≤ 1 := fun y hy => (h (τ y)).1 (hs y ((h y).2 hy))
  by_contra hlt
  push_neg at hlt
  have hc : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpa : (0 : ℝ) < p := by linarith
  have ha : 0 < ‖ι x‖ := by
    rcases (norm_nonneg (ι x)).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have h1 : ι x = 0 := norm_eq_zero.mp h0.symm
      have hx : x = 0 := (map_eq_zero ι).mp h1
      subst hx
      simp at hlt
  have hr : 1 < ‖ι (τ x)‖ / ‖ι x‖ := (one_lt_div ha).mpr hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (p : ℝ) hr
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow (pow_pos ha n) hc
  have hbn : (p : ℝ) * ‖ι x‖ ^ n < ‖ι (τ x)‖ ^ n := by
    rw [div_pow] at hn
    first
    | exact (lt_div_iff₀ (pow_pos ha n)).mp hn
    | exact (lt_div_iff (pow_pos ha n)).mp hn
  have h3 : (p : ℝ) ^ (m + 1) < ‖ι (τ x)‖ ^ n := by
    rw [zpow_add_one₀ hpa.ne']
    calc (p : ℝ) ^ m * p ≤ ‖ι x‖ ^ n * p := mul_le_mul_of_nonneg_right hm1 hpa.le
      _ = p * ‖ι x‖ ^ n := mul_comm _ _
      _ < ‖ι (τ x)‖ ^ n := hbn
  have hz : (0 : ℝ) < (p : ℝ) ^ (m + 1) := by
    first
    | exact zpow_pos hpa _
    | exact zpow_pos_of_pos hpa _
  have hk := key (x ^ n * (p : Ω) ^ (m + 1)) (by
    simp only [map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow,
      norm_natCast_padicAlgCl, inv_zpow]
    rw [← div_eq_mul_inv, div_le_one hz]
    exact hm2.le)
  simp only [map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow,
    norm_natCast_padicAlgCl, inv_zpow] at hk
  rw [← div_eq_mul_inv, div_le_one hz] at hk
  linarith

/- English proof (translation)
Use `le_antisymm (norm_apply_le_of_mem_dec h hτ x) ?_` and prove the remaining obligations. Establish `h1` using `norm_apply_le_of_mem_dec (τ := τ⁻¹) h (inv_mem hτ) (τ x)`. Establish `e : τ⁻¹ (τ x) = x` using `by first`. Consider the case `exact τ.symm_apply_apply x`. Consider the case `(rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])`.

Consider the case `simp`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem norm_apply_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : ‖ι (τ x)‖ = ‖ι x‖ := by
  refine le_antisymm (norm_apply_le_of_mem_dec h hτ x) ?_
  have h1 := norm_apply_le_of_mem_dec (τ := τ⁻¹) h (inv_mem hτ) (τ x)
  have e : τ⁻¹ (τ x) = x := by
    first
    | exact τ.symm_apply_apply x
    | (rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
    | simp
  rwa [e] at h1

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_mul_of_nonneg_right (hu i) (pow_nonneg (norm_nonneg _) _)`.

Use `_ = δ * ∑ i ∈ Finset.range n, ‖z‖ ^ i := by rw [Finset.mul_sum]`.
-/
theorem norm_sum_mul_pow_le (n : ℕ) (u : ℕ → PadicAlgCl p) (z : PadicAlgCl p) {δ : ℝ} (hu : ∀ i, ‖u i‖ ≤ δ) :
    ‖∑ i ∈ Finset.range n, u i * z ^ i‖ ≤ δ * ∑ i ∈ Finset.range n, ‖z‖ ^ i := by
  calc ‖∑ i ∈ Finset.range n, u i * z ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖u i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ * ‖z‖ ^ i := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_right (hu i) (pow_nonneg (norm_nonneg _) _)
    _ = δ * ∑ i ∈ Finset.range n, ‖z‖ ^ i := by rw [Finset.mul_sum]

/- English proof (translation)
Establish `hdense : ∀ c : PadicAlgCl p, c ∈ Kloc F ι → ∀ δ : ℝ, 0 < δ → ∃ f : F, ‖c - ι (algebraMap F Ω f)‖ < δ`. Introduce `c hc δ hδ`. Set `R : Subring (PadicAlgCl p)` to `(ι.comp (algebraMap F Ω)).range`. Establish `hQ : ∀ a : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) a ∈ R.topologicalClosure`. Introduce `a`.

Use `show _ ∈ closure (R : Set (PadicAlgCl p))`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `ε hε`. Establish `hr' : ∃ r : ℚ, ‖a - r‖ < ε` using `by first`. Consider the case `exact Padic.rat_dense p a hε`.

Consider the case `exact Padic.rat_dense a hε`. Consider the case `exact Padic.rat_dense (p := p) a hε`. Take `⟨r, hr⟩` from `hr'`. Use `⟨ι (algebraMap F Ω (r : F)), ⟨(r : F), rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, map_ratCast, map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r, ← map_sub]`.

Use `first`. Consider the case `(rw [norm_algebraMap']; exact hr)`. Consider the case `(rw [PadicAlgCl.norm_extends]; exact hr)`. Set `C : Subalgebra ℚ_[p] (PadicAlgCl p)` to `{ R.topologicalClosure with algebraMap_mem' := hQ }`. Establish `hKC : (Kloc F ι).toSubalgebra ≤ C`.

Establish `halg : ∀ y ∈ Set.range (ι.comp (algebraMap F Ω)), IsAlgebraic ℚ_[p] y` using `fun y _ => Algebra.IsAlgebraic.isAlgebraic y`. Use `show (IntermediateField.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))).toSubalgebra ≤ C`. Use `first`. Consider the case `(rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]`. Conclude with `Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy)`.

Consider the case `(rw [IntermediateField.adjoin_algebraic_toSubalgebra halg]`. Conclude with `Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy)`. Consider the case `(rw [IntermediateField.adjoin_eq_algebra_adjoin]`. Conclude with `Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy`. Introduce `y hy`.

Conclude with `(Algebra.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))).inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic _) hy)`. Establish `hcC : c ∈ closure (R : Set (PadicAlgCl p))` using `hKC hc`. Rewrite `hcC` using `[Metric.mem_closure_iff]`. Take `⟨b, ⟨f, rfl⟩, hb⟩` from `hcC δ hδ`. Conclude with `⟨f, by rwa [dist_eq_norm] at hb⟩`.

Establish `hsum : ∀ w : PadicAlgCl p, Polynomial.aeval w (minpoly (Kloc F ι) (ι x)) = ∑ i ∈ Finset.range ((minpoly (Kloc F ι) (ι x)).natDegree + 1), (((minpoly (Kloc F ι) (ι x)).coeff i : Kloc F ι) : PadicAlgCl p) * w ^ i`. Introduce `w`. Rewrite using `[Polynomial.aeval_eq_sum_range]`. Use `first`. Consider the case `rfl`.

Consider the case `(refine Finset.sum_congr rfl fun i _ => ?_; rw [Algebra.smul_def]; rfl)`. Consider the case `simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]`. Take `⟨N, hN⟩ : ∃ N : ℕ, N = (minpoly (Kloc F ι) (ι x)).natDegree + 1` from `⟨_, rfl⟩`. Rewrite `hsum` using `[← hN]`. Take `⟨c, hc⟩ : ∃ c : ℕ → PadicAlgCl p, ∀ i, c i = (((minpoly (Kloc F ι) (ι x)).coeff i : Kloc F ι) : PadicAlgCl p)` from `⟨_, fun _ => rfl⟩`.

Establish `hcK : ∀ i, c i ∈ Kloc F ι` using `fun i => by rw [hc i]; exact ((minpoly (Kloc F ι) (ι x)).coeff i).2`. Simplify using `only [← hc] at hsum`. Establish `hy0 : ∑ i ∈ Finset.range N, c i * ι x ^ i = 0`. Rewrite using `[← hsum]`. Conclude with `minpoly.aeval _ _`.

Assume the negation of the conclusion as `hne`. Establish `hv : 0 < ‖Polynomial.aeval (ι (τ x)) (minpoly (Kloc F ι) (ι x))‖` using `norm_pos_iff.mpr hne`. Rewrite `hv`, `hne` using `[hsum]`. Take `⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i ∈ Finset.range N, ‖ι (τ x)‖ ^ i + ∑ i ∈ Finset.range N, ‖ι x‖ ^ i` from `⟨_, rfl⟩`. Establish `hM0 : 0 ≤ M` using `by rw [hM]; positivity`.

Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ0, hδlt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * M < ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ := by`. Establish `hM1' : (0 : ℝ) < M + 1` using `by linarith`. Use `⟨‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1), div_pos hv hM1', ?_⟩` and prove the remaining obligations. Establish `hM1 : M + 1 ≠ 0` using `hM1'.ne'`. Establish `e : ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1) * (M + 1) = ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖` using `div_mul_cancel₀ _ hM1`.

Establish `hδ' : 0 < ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1)` using `div_pos hv hM1'`. Use the polynomial consequences of the given equalities and inequalities. Use `choose f hf using fun i => hdense (c i) (hcK i) δ hδ0`. Take `⟨u, hu_def⟩ : ∃ u : ℕ → PadicAlgCl p, ∀ i, u i = c i - ι (algebraMap F Ω (f i))` from `⟨_, fun _ => rfl⟩`. Establish `hu : ∀ i, ‖u i‖ ≤ δ` using `fun i => by rw [hu_def]; exact (hf i).le`.

Take `⟨w, hw⟩ : ∃ w : Ω, w = ∑ i ∈ Finset.range N, algebraMap F Ω (f i) * x ^ i` from `⟨_, rfl⟩`. Establish `hιw : ι w = ∑ i ∈ Finset.range N, ι (algebraMap F Ω (f i)) * ι x ^ i`. Rewrite using `[hw]`. Simplify using `only [map_sum, map_mul, map_pow]`. Establish `hιτw : ι (τ w) = ∑ i ∈ Finset.range N, ι (algebraMap F Ω (f i)) * ι (τ x) ^ i`.

Rewrite using `[hw]`. Simplify using `only [map_sum, map_mul, map_pow, AlgEquiv.commutes]`. Establish `h1 : ι w = -∑ i ∈ Finset.range N, u i * ι x ^ i`. Rewrite using `[hιw, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← hy0]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hu_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∑ i ∈ Finset.range N, c i * ι (τ x) ^ i = ∑ i ∈ Finset.range N, u i * ι (τ x) ^ i + ι (τ w)`. Rewrite using `[hιτw, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hu_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ‖ι (τ w)‖ = ‖ι w‖` using `norm_apply_of_mem_dec h hτ w`. Establish `h4 : ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ ≤ δ * M`. Rewrite using `[h2]`.

Combine the equalities or inequalities in the displayed calculation. Use `add_le_add (norm_sum_mul_pow_le _ u _ hu) ?_` and prove the remaining obligations. Rewrite using `[h3, h1, norm_neg]`. Conclude with `norm_sum_mul_pow_le _ u _ hu`. Use `_ = δ * M := by rw [hM, mul_add]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem minpoly_aeval_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : Polynomial.aeval (ι (τ x)) (minpoly (Kloc F ι) (ι x)) = 0 := by
  classical
  have hdense : ∀ c : PadicAlgCl p, c ∈ Kloc F ι → ∀ δ : ℝ, 0 < δ →
      ∃ f : F, ‖c - ι (algebraMap F Ω f)‖ < δ := by
    intro c hc δ hδ
    let R : Subring (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).range
    have hQ : ∀ a : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) a ∈ R.topologicalClosure := by
      intro a
      show _ ∈ closure (R : Set (PadicAlgCl p))
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hr' : ∃ r : ℚ, ‖a - r‖ < ε := by
        first
        | exact Padic.rat_dense p a hε
        | exact Padic.rat_dense a hε
        | exact Padic.rat_dense (p := p) a hε
      obtain ⟨r, hr⟩ := hr'
      refine ⟨ι (algebraMap F Ω (r : F)), ⟨(r : F), rfl⟩, ?_⟩
      rw [dist_eq_norm, map_ratCast, map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r,
        ← map_sub]
      first
      | (rw [norm_algebraMap']; exact hr)
      | (rw [PadicAlgCl.norm_extends]; exact hr)
    let C : Subalgebra ℚ_[p] (PadicAlgCl p) :=
      { R.topologicalClosure with algebraMap_mem' := hQ }
    have hKC : (Kloc F ι).toSubalgebra ≤ C := by
      have halg : ∀ y ∈ Set.range (ι.comp (algebraMap F Ω)), IsAlgebraic ℚ_[p] y :=
        fun y _ => Algebra.IsAlgebraic.isAlgebraic y
      show (IntermediateField.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))).toSubalgebra ≤ C
      first
      | (rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
         exact Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy)
      | (rw [IntermediateField.adjoin_algebraic_toSubalgebra halg]
         exact Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy)
      | (rw [IntermediateField.adjoin_eq_algebra_adjoin]
         · exact Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy
         · intro y hy
           exact (Algebra.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))).inv_mem_of_algebraic
             (Algebra.IsAlgebraic.isAlgebraic _) hy)
    have hcC : c ∈ closure (R : Set (PadicAlgCl p)) := hKC hc
    rw [Metric.mem_closure_iff] at hcC
    obtain ⟨b, ⟨f, rfl⟩, hb⟩ := hcC δ hδ
    exact ⟨f, by rwa [dist_eq_norm] at hb⟩
  have hsum : ∀ w : PadicAlgCl p, Polynomial.aeval w (minpoly (Kloc F ι) (ι x)) =
      ∑ i ∈ Finset.range ((minpoly (Kloc F ι) (ι x)).natDegree + 1),
        (((minpoly (Kloc F ι) (ι x)).coeff i : Kloc F ι) : PadicAlgCl p) * w ^ i := by
    intro w
    rw [Polynomial.aeval_eq_sum_range]
    first
    | rfl
    | (refine Finset.sum_congr rfl fun i _ => ?_; rw [Algebra.smul_def]; rfl)
    | simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (minpoly (Kloc F ι) (ι x)).natDegree + 1 := ⟨_, rfl⟩
  rw [← hN] at hsum
  obtain ⟨c, hc⟩ : ∃ c : ℕ → PadicAlgCl p,
      ∀ i, c i = (((minpoly (Kloc F ι) (ι x)).coeff i : Kloc F ι) : PadicAlgCl p) := ⟨_, fun _ => rfl⟩
  have hcK : ∀ i, c i ∈ Kloc F ι := fun i => by rw [hc i]; exact ((minpoly (Kloc F ι) (ι x)).coeff i).2
  simp only [← hc] at hsum
  have hy0 : ∑ i ∈ Finset.range N, c i * ι x ^ i = 0 := by
    rw [← hsum]; exact minpoly.aeval _ _
  by_contra hne
  have hv : 0 < ‖Polynomial.aeval (ι (τ x)) (minpoly (Kloc F ι) (ι x))‖ := norm_pos_iff.mpr hne
  rw [hsum] at hv hne
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i ∈ Finset.range N, ‖ι (τ x)‖ ^ i + ∑ i ∈ Finset.range N, ‖ι x‖ ^ i :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨δ, hδ0, hδlt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * M < ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ := by
    have hM1' : (0 : ℝ) < M + 1 := by linarith
    refine ⟨‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1), div_pos hv hM1', ?_⟩
    have hM1 : M + 1 ≠ 0 := hM1'.ne'
    have e : ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1) * (M + 1) =
        ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ := div_mul_cancel₀ _ hM1
    have hδ' : 0 < ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1) := div_pos hv hM1'
    nlinarith
  choose f hf using fun i => hdense (c i) (hcK i) δ hδ0
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → PadicAlgCl p, ∀ i, u i = c i - ι (algebraMap F Ω (f i)) :=
    ⟨_, fun _ => rfl⟩
  have hu : ∀ i, ‖u i‖ ≤ δ := fun i => by rw [hu_def]; exact (hf i).le
  obtain ⟨w, hw⟩ : ∃ w : Ω, w = ∑ i ∈ Finset.range N, algebraMap F Ω (f i) * x ^ i := ⟨_, rfl⟩
  have hιw : ι w = ∑ i ∈ Finset.range N, ι (algebraMap F Ω (f i)) * ι x ^ i := by
    rw [hw]; simp only [map_sum, map_mul, map_pow]
  have hιτw : ι (τ w) = ∑ i ∈ Finset.range N, ι (algebraMap F Ω (f i)) * ι (τ x) ^ i := by
    rw [hw]; simp only [map_sum, map_mul, map_pow, AlgEquiv.commutes]
  have h1 : ι w = -∑ i ∈ Finset.range N, u i * ι x ^ i := by
    rw [hιw, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← hy0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu_def]; ring
  have h2 : ∑ i ∈ Finset.range N, c i * ι (τ x) ^ i =
      ∑ i ∈ Finset.range N, u i * ι (τ x) ^ i + ι (τ w) := by
    rw [hιτw, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu_def]; ring
  have h3 : ‖ι (τ w)‖ = ‖ι w‖ := norm_apply_of_mem_dec h hτ w
  have h4 : ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ ≤ δ * M := by
    rw [h2]
    calc _ ≤ ‖∑ i ∈ Finset.range N, u i * ι (τ x) ^ i‖ + ‖ι (τ w)‖ := norm_add_le _ _
      _ ≤ δ * ∑ i ∈ Finset.range N, ‖ι (τ x)‖ ^ i + δ * ∑ i ∈ Finset.range N, ‖ι x‖ ^ i := by
          refine add_le_add (norm_sum_mul_pow_le _ u _ hu) ?_
          rw [h3, h1, norm_neg]
          exact norm_sum_mul_pow_le _ u _ hu
      _ = δ * M := by rw [hM, mul_add]
  linarith

/- English proof (translation)
Use `haveI := isAlgClosure_Kloc (F := F) ι`. Establish `hint : IsIntegral (Kloc F ι) (ι x)` using `by first`. Consider the case `exact Algebra.IsIntegral.isIntegral _`. Consider the case `exact (Algebra.IsAlgebraic.isAlgebraic (R := Kloc F ι) (ι x)).isIntegral`. Establish `hc : IsConjRoot (Kloc F ι) (ι x) (ι (τ x))` using `isConjRoot_of_aeval_eq_zero hint (minpoly_aeval_of_mem_dec h hτ x)`.

Take `⟨σ, hσ⟩` from `isConjRoot_iff_exists_algEquiv.mp hc`. Use `first`. Consider the case `exact ⟨σ, hσ⟩`. Consider the case `exact ⟨σ.symm, by rw [← hσ]; simp⟩`.
-/
theorem exists_apply_eq_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : ∃ σ : GK F ι, σ (ι x) = ι (τ x) := by
  haveI := isAlgClosure_Kloc (F := F) ι
  have hint : IsIntegral (Kloc F ι) (ι x) := by
    first
    | exact Algebra.IsIntegral.isIntegral _
    | exact (Algebra.IsAlgebraic.isAlgebraic (R := Kloc F ι) (ι x)).isIntegral
  have hc : IsConjRoot (Kloc F ι) (ι x) (ι (τ x)) :=
    isConjRoot_of_aeval_eq_zero hint (minpoly_aeval_of_mem_dec h hτ x)
  obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hc
  first
  | exact ⟨σ, hσ⟩
  | exact ⟨σ.symm, by rw [← hσ]; simp⟩

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element F E`. Take `⟨σ, hσ⟩` from `exists_apply_eq_of_mem_dec h hτ (α : Ω)`. Use `⟨σ, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : res ι σ (α : Ω) = τ (α : Ω)` using `ι.injective (by rw [res_spec, hσ])`. Establish `hint : IsIntegral F α` using `IsIntegral.of_finite F α`.

Establish `htop : Algebra.adjoin F {α} = ⊤` using `by first`. Consider the case `rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isIntegral hint, hα, IntermediateField.top_toSubalgebra]`. Consider the case `rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα, IntermediateField.top_toSubalgebra]`. Consider the case `rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := {α}) (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _), hα, IntermediateField.top_toSubalgebra]`. Consider the case `rw [← IntermediateField.adjoin_algebraic_toSubalgebra (S := {α}) (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _), hα, IntermediateField.top_toSubalgebra]`.

Establish `key : ((res ι σ).toAlgHom.comp E.val : E →ₐ[F] Ω) = τ.toAlgHom.comp E.val`. Apply `AlgHom.ext_of_adjoin_eq_top htop` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality.

Simplify using `using h1`. Establish `h2` using `congrArg (fun φ : E →ₐ[F] Ω => φ ⟨y, hy⟩) key`. Simplify using `using h2`.
-/
theorem exists_res_eqOn_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (E : IntermediateField F Ω) [FiniteDimensional F E] :
    ∃ σ : GK F ι, ∀ y ∈ E, res ι σ y = τ y := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  obtain ⟨σ, hσ⟩ := exists_apply_eq_of_mem_dec h hτ (α : Ω)
  refine ⟨σ, fun y hy => ?_⟩
  have h1 : res ι σ (α : Ω) = τ (α : Ω) := ι.injective (by rw [res_spec, hσ])
  have hint : IsIntegral F α := IsIntegral.of_finite F α
  have htop : Algebra.adjoin F {α} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isIntegral hint, hα,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := {α})
        (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _), hα, IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_algebraic_toSubalgebra (S := {α})
        (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _), hα, IntermediateField.top_toSubalgebra]
  have key : ((res ι σ).toAlgHom.comp E.val : E →ₐ[F] Ω) = τ.toAlgHom.comp E.val := by
    apply AlgHom.ext_of_adjoin_eq_top htop
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simpa using h1
  have h2 := congrArg (fun φ : E →ₐ[F] Ω => φ ⟨y, hy⟩) key
  simpa using h2

/- English proof (translation)
Use `haveI := isAlgClosure_Kloc (F := F) ι`. Establish `hclosed : ∀ a b : PadicAlgCl p, IsClosed {σ : GK F ι | σ a = b}`. Introduce `a b`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `σ hσ`.

Establish `hai : IsIntegral (Kloc F ι) a` using `by first`. Consider the case `exact Algebra.IsIntegral.isIntegral _`. Consider the case `exact (Algebra.IsAlgebraic.isAlgebraic (R := Kloc F ι) a).isIntegral`. Use `haveI hfin : FiniteDimensional (Kloc F ι) (IntermediateField.adjoin (Kloc F ι) {a}) := IntermediateField.adjoin.finiteDimensional hai`. Establish `hU : IsOpen ((IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup : Set (GK F ι))` using `IntermediateField.fixingSubgroup_isOpen _`.

Use `⟨(fun ρ => σ⁻¹ * ρ) ⁻¹' ((IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup : Set (GK F ι)), ?_, hU.preimage (continuous_const.mul continuous_id), ?_⟩` and prove the remaining obligations. Introduce `ρ hρ`. Establish `hfix : (σ⁻¹ * ρ) a = a` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ a (IntermediateField.mem_adjoin_simple_self _ a)`. Introduce `hρb`. Apply `hσ` to reduce the goal to its premises.

Use `show σ a = b`. Establish `e : σ ((σ⁻¹ * ρ) a) = ρ a` using `by first`. Consider the case `(rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul])`. Consider the case `(rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_right_inv, one_mul])`. Consider the case `simp`.

Rewrite using `[← hρb, ← e, hfix]`. Use `show σ⁻¹ * σ ∈ (IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup`. Rewrite using `[inv_mul_cancel]`. Conclude with `Subgroup.one_mem _`. Set `T : {E : IntermediateField F Ω // FiniteDimensional F E} → Set (GK F ι)` to `fun E => {σ | ∀ y ∈ E.1, res ι σ y = τ y}`.

Establish `hTcl : ∀ E, IsClosed (T E)`. Introduce `E`. Establish `e : T E = ⋂ y ∈ E.1, {σ : GK F ι | σ (ι y) = ι (τ y)}`. Use extensionality with `σ`. Simplify using `only [T, Set.mem_setOf_eq, Set.mem_iInter]`.

Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← res_spec, ι.injective.eq_iff]`. Rewrite using `[e]`. Conclude with `isClosed_biInter fun y _ => hclosed _ _`. Establish `hTne : ∀ E, (T E).Nonempty`.

Introduce `E`. Use `haveI := E.2`. Take `⟨σ, hσ⟩` from `exists_res_eqOn_of_mem_dec h hτ E.1`. Conclude with `⟨σ, hσ⟩`. Establish `hdir : Directed (· ⊇ ·) T`.

Introduce `E₁ E₂`. Use `haveI := E₁.2`. Use `haveI := E₂.2`. Use `⟨⟨E₁.1 ⊔ E₂.1, inferInstance⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ y hy`.

Conclude with `hσ y ((le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1) hy)`. Introduce `σ hσ y hy`. Conclude with `hσ y ((le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1) hy)`. Use `haveI : Nonempty {E : IntermediateField F Ω // FiniteDimensional F E} := ⟨⟨⊥, inferInstance⟩⟩`. Take `⟨σ, hσ⟩` from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir hTne (fun E => (hTcl E).isCompact) hTcl`.

Use `⟨σ, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite `hσ` using `[Set.mem_iInter]`. Establish `hy : IsIntegral F y` using `Algebra.IsIntegral.isIntegral y`. Conclude with `hσ ⟨IntermediateField.adjoin F {y}, IntermediateField.adjoin.finiteDimensional hy⟩ y (IntermediateField.mem_adjoin_simple_self F y)`.
-/
theorem exists_res_eq {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) : ∃ σ : GK F ι, res ι σ = τ := by
  classical
  haveI := isAlgClosure_Kloc (F := F) ι
  have hclosed : ∀ a b : PadicAlgCl p, IsClosed {σ : GK F ι | σ a = b} := by
    intro a b
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro σ hσ
    have hai : IsIntegral (Kloc F ι) a := by
      first
      | exact Algebra.IsIntegral.isIntegral _
      | exact (Algebra.IsAlgebraic.isAlgebraic (R := Kloc F ι) a).isIntegral
    haveI hfin : FiniteDimensional (Kloc F ι) (IntermediateField.adjoin (Kloc F ι) {a}) :=
      IntermediateField.adjoin.finiteDimensional hai
    have hU : IsOpen ((IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup : Set (GK F ι)) :=
      IntermediateField.fixingSubgroup_isOpen _
    refine ⟨(fun ρ => σ⁻¹ * ρ) ⁻¹' ((IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup : Set (GK F ι)),
      ?_, hU.preimage (continuous_const.mul continuous_id), ?_⟩
    · intro ρ hρ
      have hfix : (σ⁻¹ * ρ) a = a :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ a (IntermediateField.mem_adjoin_simple_self _ a)
      intro hρb
      apply hσ
      show σ a = b
      have e : σ ((σ⁻¹ * ρ) a) = ρ a := by
        first
        | (rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul])
        | (rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_right_inv, one_mul])
        | simp
      rw [← hρb, ← e, hfix]
    · show σ⁻¹ * σ ∈ (IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
  let T : {E : IntermediateField F Ω // FiniteDimensional F E} → Set (GK F ι) :=
    fun E => {σ | ∀ y ∈ E.1, res ι σ y = τ y}
  have hTcl : ∀ E, IsClosed (T E) := by
    intro E
    have e : T E = ⋂ y ∈ E.1, {σ : GK F ι | σ (ι y) = ι (τ y)} := by
      ext σ
      simp only [T, Set.mem_setOf_eq, Set.mem_iInter]
      refine forall₂_congr fun y _ => ?_
      rw [← res_spec, ι.injective.eq_iff]
    rw [e]
    exact isClosed_biInter fun y _ => hclosed _ _
  have hTne : ∀ E, (T E).Nonempty := by
    intro E
    haveI := E.2
    obtain ⟨σ, hσ⟩ := exists_res_eqOn_of_mem_dec h hτ E.1
    exact ⟨σ, hσ⟩
  have hdir : Directed (· ⊇ ·) T := by
    intro E₁ E₂
    haveI := E₁.2
    haveI := E₂.2
    refine ⟨⟨E₁.1 ⊔ E₂.1, inferInstance⟩, ?_, ?_⟩
    · intro σ hσ y hy
      exact hσ y ((le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1) hy)
    · intro σ hσ y hy
      exact hσ y ((le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1) hy)
  haveI : Nonempty {E : IntermediateField F Ω // FiniteDimensional F E} := ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir hTne
    (fun E => (hTcl E).isCompact) hTcl
  refine ⟨σ, ?_⟩
  ext y
  rw [Set.mem_iInter] at hσ
  have hy : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  exact hσ ⟨IntermediateField.adjoin F {y}, IntermediateField.adjoin.finiteDimensional hy⟩ y
    (IntermediateField.mem_adjoin_simple_self F y)

def resDec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) : GK F ι →* Dec (F := F) A :=
  (res ι).codRestrict (Dec (F := F) A) (res_mem_dec h)

/- English proof (translation)
Use `⟨fun σ₁ σ₂ he => res_injective ι (congrArg Subtype.val he), fun τ => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `exists_res_eq h τ.2`. Conclude with `⟨σ, Subtype.ext hσ⟩`.
-/
theorem bijective_resDec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) :
    Function.Bijective (resDec (F := F) h) := by
  refine ⟨fun σ₁ σ₂ he => res_injective ι (congrArg Subtype.val he), fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_res_eq h τ.2
  exact ⟨σ, Subtype.ext hσ⟩

/- English proof (translation)
Use `first`. Consider the case `exact (continuous_res ι).subtype_mk _`. Consider the case `exact Continuous.subtype_mk (continuous_res ι) (res_mem_dec h)`. Consider the case `exact continuous_induced_rng.2 (continuous_res ι)`.
-/
theorem continuous_resDec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) :
    Continuous (resDec (F := F) h) := by
  first
  | exact (continuous_res ι).subtype_mk _
  | exact Continuous.subtype_mk (continuous_res ι) (res_mem_dec h)
  | exact continuous_induced_rng.2 (continuous_res ι)

def equiv {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) : GK F ι ≃ₜ* Dec (F := F) A := by
  haveI := isAlgClosure_Kloc (F := F) ι
  haveI : T2Space (Ω ≃ₐ[F] Ω) := krullTopology_t2
  haveI : IsGalois (Kloc F ι) (PadicAlgCl p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  exact
  { toMulEquiv := MulEquiv.ofBijective (resDec h) (bijective_resDec h)
    continuous_toFun := continuous_resDec h
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective (resDec h) (bijective_resDec h)).toEquiv) (continuous_resDec h) }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem equiv_apply {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι) :
    (equiv h σ : Ω ≃ₐ[F] Ω) = res ι σ := rfl

end ReciprocityTheory.Neutral.Cmp
