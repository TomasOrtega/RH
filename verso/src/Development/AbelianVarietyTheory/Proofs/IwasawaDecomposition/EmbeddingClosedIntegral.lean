import Mathlib

namespace GlobalTheory.CoefEmbed

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

/- English proof (translation)
Take `⟨p, hp, hp0⟩ : IsIntegral ℤ_[l] a` from `Algebra.IsIntegral.isIntegral a`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Rewrite `hp0` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul]`. Establish `hp1` using `congrArg f hp0`.

Simplify using `only [map_add, map_sum, map_mul, map_pow, map_zero, hf] at hp1`. Use `set y := f a`. Establish `h1 : y ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l]) * y ^ i`. Take the linear combination `hp1`. Establish `hpos : 0 < ‖y‖ ^ p.natDegree` using `pow_pos (by linarith) _`.

Establish `h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l]) * y ^ i‖ < ‖y‖ ^ p.natDegree`. Use `Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_` and prove the remaining obligations. Introduce `u v hu hv`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)`. Introduce `i hi`.

Rewrite using `[norm_mul, norm_pow]`. Establish `h3 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l])‖ ≤ 1`. Rewrite using `[norm_algebraMap']`. Conclude with `(p.coeff i).2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h2` using `[← norm_neg, ← h1, norm_pow]`. Conclude with `lt_irrefl _ h2`.
-/
theorem norm_le_one (f : O →+* PadicAlgCl l)
    (hf : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))
    (a : O) : ‖f a‖ ≤ 1 := by
  obtain ⟨p, hp, hp0⟩ : IsIntegral ℤ_[l] a := Algebra.IsIntegral.isIntegral a
  by_contra hlt
  push Not at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have hp1 := congrArg f hp0
  simp only [map_add, map_sum, map_mul, map_pow, map_zero, hf] at hp1
  set y := f a
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree,
        algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l]) * y ^ i := by
    linear_combination hp1
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree,
      algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l]) * y ^ i‖ < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l])‖ ≤ 1 := by
        rw [norm_algebraMap']
        exact (p.coeff i).2
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Take `⟨b, hb⟩` from `ha.exists_right_inv`. Establish `h : ‖f a‖ * ‖f b‖ = 1` using `by rw [← norm_mul, ← map_mul, hb, map_one, norm_one]`. Use `le_antisymm (norm_le_one f hf a) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_unit (f : O →+* PadicAlgCl l)
    (hf : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))
    {a : O} (ha : IsUnit a) : ‖f a‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h : ‖f a‖ * ‖f b‖ = 1 := by rw [← norm_mul, ← map_mul, hb, map_one, norm_one]
  refine le_antisymm (norm_le_one f hf a) ?_
  calc (1 : ℝ) = ‖f a‖ * ‖f b‖ := h.symm
    _ ≤ ‖f a‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_le_one f hf b)

open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
/- English proof (translation)
Establish `h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem _root_.GlobalTheory.CoefEmbed.norm_prime_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Rewrite `hy` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, map_one, one_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := by`. Use `⟨P.natDegree - 1, ?_⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos P.natDegree with h0 | h0` into its components or cases. Rewrite `hy` using `[h0]`. Simplify using `at hy`. Use linear arithmetic over natural numbers and integers. Rewrite `hy` using `[hk]`.

Establish `hsum : ‖∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i‖ ≤ ‖y‖ ^ k`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : y ^ (k + 1) = -∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i`. Take the linear combination `hy`. Establish `h1 : ‖y‖ ^ (k + 1) ≤ ‖y‖ ^ k`. Rewrite using `[← norm_pow, heq, norm_neg]`. Conclude with `hsum`.

Establish `h2 : ‖y‖ ^ k < ‖y‖ ^ (k + 1)` using `pow_lt_pow_right₀ h (Nat.lt_succ_self k)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma norm_le_one_of_monic_root_lemma {R F : Type*} [CommRing R] [NormedField F]
    [IsUltrametricDist F] (f : R →+* F) (hf : ∀ r, ‖f r‖ ≤ 1) {P : Polynomial R}
    (hP : P.Monic) {y : F} (hy : P.eval₂ f y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, map_one,
    one_mul] at hy
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := by
    refine ⟨P.natDegree - 1, ?_⟩
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · rw [h0] at hy
      simp at hy
    · omega
  rw [hk] at hy
  have hsum : ‖∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i‖ ≤ ‖y‖ ^ k := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    calc ‖f (P.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ k :=
          mul_le_mul (hf _) (pow_le_pow_right₀ h.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
            (by positivity) zero_le_one
      _ = ‖y‖ ^ k := one_mul _
  have heq : y ^ (k + 1) = -∑ i ∈ Finset.range (k + 1), f (P.coeff i) * y ^ i := by
    linear_combination hy
  have h1 : ‖y‖ ^ (k + 1) ≤ ‖y‖ ^ k := by
    rw [← norm_pow, heq, norm_neg]
    exact hsum
  have h2 : ‖y‖ ^ k < ‖y‖ ^ (k + 1) := pow_lt_pow_right₀ h (Nat.lt_succ_self k)
  linarith

open IsLocalRing Topology in
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ hO κ hκ`. Use `set g : O →+* PadicAlgCl l := κ.comp (algebraMap O (FractionRing O)) with hg`. Establish `hgz : ∀ z : ℤ_[l], g (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])` using `hκ`. Establish `hgnat : g ((l : ℕ) : O) = ((l : ℕ) : PadicAlgCl l)` using `map_natCast g l`. Establish `hl_lt : ‖g ((l : ℕ) : O)‖ < 1` using `hgnat ▸ _root_.GlobalTheory.CoefEmbed.norm_prime_lt_one (l := l)`.

Establish `hl_pos : 0 < ‖g ((l : ℕ) : O)‖`. Establish `h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[hgnat, h, norm_algebraMap', Padic.norm_p]`. Establish `: (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Check the signs of the components of the expression.

Establish `hint : ∀ x : O, ‖g x‖ ≤ 1`. Introduce `x`. Take `⟨P, hPm, hP⟩` from `Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x`. Use `norm_le_one_of_monic_root_lemma (g.comp (algebraMap ℤ_[l] O)) (fun z => ?_) hPm ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hgz, norm_algebraMap']`.

Conclude with `PadicInt.norm_le_one z`. Rewrite using `[← Polynomial.hom_eval₂, hP, map_zero]`. Establish `hunit : ∀ u : Oˣ, ‖g u‖ = 1`. Introduce `u`. Establish `h1` using `hint u`.

Establish `h2` using `hint ↑u⁻¹`. Establish `h3 : ‖g u‖ * ‖g ↑u⁻¹‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]`. Establish `h4` using `mul_le_mul_of_nonneg_left h2 (norm_nonneg (g u))`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmax : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, hu⟩`. Use `hunit u` as an intermediate fact. Rewrite `this` using `[hu]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hl0 : ((l : ℕ) : O) ≠ 0`. Introduce `h`. Rewrite `hl_pos` using `[h, map_zero, norm_zero]`.

Conclude with `lt_irrefl _ hl_pos`. Take `⟨e, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp hmax) (by rw [hw, pow_zero, mul_one]; exact w.isUnit)`.

Establish `hϖlt : ‖g ϖ‖ < 1`. Establish `h : ‖g ((l : ℕ) : O)‖ = ‖g ϖ‖ ^ e`. Rewrite using `[hw, map_mul, norm_mul, hunit, one_mul, map_pow, norm_pow]`. Assume the negation of the conclusion as `h'`. Use `push_neg at h'`.

Use `one_le_pow₀ (n := e) h'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hginj : Function.Injective g` using `κ.injective.comp (IsFractionRing.injective O (FractionRing O))`. Establish `hϖpos : 0 < ‖g ϖ‖` using `norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr hϖ0)`.

Establish `hm : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O → ‖g y‖ ≤ ‖g ϖ‖`. Introduce `y hy`. Rewrite `hy` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hy`. Rewrite using `[map_mul, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hintc : ∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x`. Introduce `x hx`. Distinguish the cases in `hx0 : x = 0`. Conclude with `⟨0, by rw [hx0, map_zero]⟩`.

Break down `ValuationRing.isInteger_or_isInteger O x with h | h` into its components or cases. Conclude with `h`. Take `⟨y, hy⟩` from `h`. Distinguish the cases in `hyu : IsUnit y`. Take `⟨u, rfl⟩` from `hyu`.

Use `⟨↑u⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap O (FractionRing O) ↑u⁻¹ * algebraMap O (FractionRing O) ↑u = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Rewrite `h1` using `[hy]`. Conclude with `(mul_inv_eq_one₀ hx0).mp h1`.

It suffices to derive a contradiction. Establish `hym : y ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr hyu`. Establish `h1 : ‖κ x⁻¹‖ ≤ ‖g ϖ‖`. Rewrite using `[← hy]`. Conclude with `hm y hym`.

Establish `h2 : ‖κ x‖ * ‖κ x⁻¹‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]`. Establish `h3` using `mul_le_mul_of_nonneg_right hx (norm_nonneg (κ x⁻¹))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdiv : ∀ b : O, b ≠ 0 → ∃ (n : ℕ) (c : O), b * c = ((l : ℕ) : O) ^ n`.

Introduce `b hb`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ`. Take `⟨e', rfl⟩ : ∃ e', e = e' + 1` from `⟨e - 1, by omega⟩`. Use `⟨n, ↑u⁻¹ * ↑w ^ n * ϖ ^ (e' * n), ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`.

Use `u.mul_inv` as an intermediate fact. Take the linear combination `(↑w ^ n * ϖ ^ (n + e' * n)) * this`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ_[l]) (M := O)`. Use `set V : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (g '' (s : Set O)) with hV`. Establish `hgV : ∀ x : O, g x ∈ V`.

Introduce `x`. Establish `hx : x ∈ Submodule.span ℤ_[l] (s : Set O)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `V.zero_mem`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `V.add_mem hy hz`. Consider the case `smul z y _ hy`. Rewrite using `[Algebra.smul_def, map_mul, hgz, ← Algebra.smul_def]`.

Conclude with `V.smul_mem _ hy`. Establish `hrange : Set.range κ = (V : Set (PadicAlgCl l))`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective O x`.

Take `⟨n, c, hc⟩` from `hdiv b (nonZeroDivisors.ne_zero hb)`. Establish `hb' : g b ≠ 0` using `(map_ne_zero_iff g hginj).mpr (nonZeroDivisors.ne_zero hb)`. Establish `hln : g (((l : ℕ) : O) ^ n) ≠ 0`. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (norm_pos_iff.mp hl_pos)`.

Establish `hc' : g c ≠ 0`. Introduce `h`. Apply `hln` to reduce the goal to its premises. Rewrite using `[← hc, map_mul, h, mul_zero]`. Establish `key : κ (algebraMap O (FractionRing O) a / algebraMap O (FractionRing O) b) = ((l : ℚ_[l]) ^ n)⁻¹ • g (a * c)`.

Rewrite using `[map_div₀, Algebra.smul_def, map_inv₀, map_pow, map_natCast]`. Express the relevant statement in the definitionally equal form `g a / g b = _`. Rewrite using `[← map_natCast g, ← map_pow, ← hc, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[SetLike.mem_coe, key]`.

Conclude with `V.smul_mem _ (hgV _)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, _, rfl⟩` from `hy`.

Conclude with `⟨_, rfl⟩`. Consider the case `zero => exact ⟨0, map_zero κ⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, rfl⟩` from `hy`. Take `⟨b, rfl⟩` from `hz`.

Conclude with `⟨a + b, map_add κ a b⟩`. Consider the case `smul q y _ hy`. Take `⟨x, rfl⟩` from `hy`. Take `⟨z1, z2, -, rfl⟩` from `IsFractionRing.div_surjective ℤ_[l] q`. Use `⟨algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z1) / algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z2) * x, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_div₀, hκ, hκ, Algebra.smul_def, map_div₀]`. Both sides reduce to the same expression. Establish `hclosed : IsClosed (Set.range κ)`. Rewrite using `[hrange]`. Use `haveI : FiniteDimensional ℚ_[l] V := FiniteDimensional.span_of_finite ℚ_[l] ((s.finite_toSet).image g)`.

Conclude with `V.closed_of_finiteDimensional`. Take `⟨hopen, hsmall⟩` from `isAdic_iff.mp hO`. Establish `hemb : Topology.IsEmbedding g`. Use `⟨(IsTopologicalAddGroup.isInducing_iff_nhds_zero).mpr ?_, hginj⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[(Metric.nhds_basis_ball.comap g).ge_iff]`. Introduce `ε hε`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hϖlt`. Use `Filter.mem_of_superset ((hopen n).mem_nhds (IsLocalRing.maximalIdeal O ^ n).zero_mem) ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Set.mem_preimage, mem_ball_zero_iff]`. Rewrite `hx` using `[SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hx`. Rewrite using `[map_mul, norm_mul, map_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Introduce `t ht`. Take `⟨n, hn⟩` from `hsmall t ht`. Rewrite using `[(Metric.nhds_basis_ball.comap g).mem_iff]`. Use `⟨‖g ϖ‖ ^ n, by positivity, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Set.mem_preimage, mem_ball_zero_iff] at hx`. Apply `hn` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `hϖn : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr (pow_ne_zero _ hϖ0)`. Establish `hgϖn : 0 < ‖g (ϖ ^ n)‖` using `norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr (pow_ne_zero _ hϖ0))`.

Take `⟨y, hy⟩` from `hintc (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) (ϖ ^ n)) (by`. Rewrite using `[map_div₀, norm_div]`. Express the relevant statement in the definitionally equal form `‖g x‖ / ‖g (ϖ ^ n)‖ ≤ 1`. Rewrite using `[div_le_one hgϖn, map_pow, norm_pow]`. Conclude with `hx.le)`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective O (FractionRing O)` to reduce the goal to its premises. Rewrite using `[map_mul, hy]`. Clear the denominators using the available nonvanishing facts. Conclude with `⟨hemb, hclosed, hintc, hmax⟩`.
-/
theorem _root_.GlobalTheory.CoefEmbed.embedding_closed_integral : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ κ : FractionRing O →+* PadicAlgCl l, (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → Topology.IsEmbedding (fun x : O => κ (algebraMap O (FractionRing O) x)) ∧ IsClosed (Set.range κ) ∧ (∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x) ∧ ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
  intro l _ O _ _ _ _ _ _ _ hO κ hκ
  set g : O →+* PadicAlgCl l := κ.comp (algebraMap O (FractionRing O)) with hg
  have hgz : ∀ z : ℤ_[l], g (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]) :=
    hκ
  have hgnat : g ((l : ℕ) : O) = ((l : ℕ) : PadicAlgCl l) := map_natCast g l
  have hl_lt : ‖g ((l : ℕ) : O)‖ < 1 := hgnat ▸ _root_.GlobalTheory.CoefEmbed.norm_prime_lt_one (l := l)
  have hl_pos : 0 < ‖g ((l : ℕ) : O)‖ := by
    have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [hgnat, h, norm_algebraMap', Padic.norm_p]
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have hint : ∀ x : O, ‖g x‖ ≤ 1 := by
    intro x
    obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    refine norm_le_one_of_monic_root_lemma (g.comp (algebraMap ℤ_[l] O)) (fun z => ?_) hPm ?_
    · rw [RingHom.comp_apply, hgz, norm_algebraMap']
      exact PadicInt.norm_le_one z
    · rw [← Polynomial.hom_eval₂, hP, map_zero]
  have hunit : ∀ u : Oˣ, ‖g u‖ = 1 := by
    intro u
    have h1 := hint u
    have h2 := hint ↑u⁻¹
    have h3 : ‖g u‖ * ‖g ↑u⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (g u))
    linarith
  have hmax : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have := hunit u
    rw [hu] at this
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hl_pos
    exact lt_irrefl _ hl_pos
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmax) (by rw [hw, pow_zero, mul_one]; exact w.isUnit)
  have hϖlt : ‖g ϖ‖ < 1 := by
    have h : ‖g ((l : ℕ) : O)‖ = ‖g ϖ‖ ^ e := by
      rw [hw, map_mul, norm_mul, hunit, one_mul, map_pow, norm_pow]
    by_contra h'
    push_neg at h'
    have := one_le_pow₀ (n := e) h'
    linarith
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hginj : Function.Injective g :=
    κ.injective.comp (IsFractionRing.injective O (FractionRing O))
  have hϖpos : 0 < ‖g ϖ‖ := norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr hϖ0)
  have hm : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O → ‖g y‖ ≤ ‖g ϖ‖ := by
    intro y hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [map_mul, norm_mul]
    calc ‖g ϖ‖ * ‖g c‖ ≤ ‖g ϖ‖ * 1 := mul_le_mul_of_nonneg_left (hint c) (norm_nonneg _)
      _ = ‖g ϖ‖ := mul_one _
  have hintc : ∀ x : FractionRing O, ‖κ x‖ ≤ 1 → ∃ y : O, algebraMap O (FractionRing O) y = x := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by rw [hx0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger O x with h | h
    · exact h
    · obtain ⟨y, hy⟩ := h
      by_cases hyu : IsUnit y
      · obtain ⟨u, rfl⟩ := hyu
        refine ⟨↑u⁻¹, ?_⟩
        have h1 : algebraMap O (FractionRing O) ↑u⁻¹ * algebraMap O (FractionRing O) ↑u = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hy] at h1
        exact (mul_inv_eq_one₀ hx0).mp h1
      · exfalso
        have hym : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hyu
        have h1 : ‖κ x⁻¹‖ ≤ ‖g ϖ‖ := by
          rw [← hy]
          exact hm y hym
        have h2 : ‖κ x‖ * ‖κ x⁻¹‖ = 1 := by
          rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
        have h3 := mul_le_mul_of_nonneg_right hx (norm_nonneg (κ x⁻¹))
        linarith
  have hdiv : ∀ b : O, b ≠ 0 → ∃ (n : ℕ) (c : O), b * c = ((l : ℕ) : O) ^ n := by
    intro b hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    refine ⟨n, ↑u⁻¹ * ↑w ^ n * ϖ ^ (e' * n), ?_⟩
    rw [hw]
    have := u.mul_inv
    linear_combination (↑w ^ n * ϖ ^ (n + e' * n)) * this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  set V : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (g '' (s : Set O)) with hV
  have hgV : ∀ x : O, g x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact V.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact V.add_mem hy hz
    | smul z y _ hy =>
      rw [Algebra.smul_def, map_mul, hgz, ← Algebra.smul_def]
      exact V.smul_mem _ hy
  have hrange : Set.range κ = (V : Set (PadicAlgCl l)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective O x
      obtain ⟨n, c, hc⟩ := hdiv b (nonZeroDivisors.ne_zero hb)
      have hb' : g b ≠ 0 := (map_ne_zero_iff g hginj).mpr (nonZeroDivisors.ne_zero hb)
      have hln : g (((l : ℕ) : O) ^ n) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (norm_pos_iff.mp hl_pos)
      have hc' : g c ≠ 0 := by
        intro h
        apply hln
        rw [← hc, map_mul, h, mul_zero]
      have key : κ (algebraMap O (FractionRing O) a / algebraMap O (FractionRing O) b) =
          ((l : ℚ_[l]) ^ n)⁻¹ • g (a * c) := by
        rw [map_div₀, Algebra.smul_def, map_inv₀, map_pow, map_natCast]
        change g a / g b = _
        rw [← map_natCast g, ← map_pow, ← hc, map_mul, map_mul]
        field_simp
      rw [SetLike.mem_coe, key]
      exact V.smul_mem _ (hgV _)
    · intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, _, rfl⟩ := hy
        exact ⟨_, rfl⟩
      | zero => exact ⟨0, map_zero κ⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, rfl⟩ := hy
        obtain ⟨b, rfl⟩ := hz
        exact ⟨a + b, map_add κ a b⟩
      | smul q y _ hy =>
        obtain ⟨x, rfl⟩ := hy
        obtain ⟨z1, z2, -, rfl⟩ := IsFractionRing.div_surjective ℤ_[l] q
        refine ⟨algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z1) /
          algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z2) * x, ?_⟩
        rw [map_mul, map_div₀, hκ, hκ, Algebra.smul_def, map_div₀]
        rfl
  have hclosed : IsClosed (Set.range κ) := by
    rw [hrange]
    haveI : FiniteDimensional ℚ_[l] V :=
      FiniteDimensional.span_of_finite ℚ_[l] ((s.finite_toSet).image g)
    exact V.closed_of_finiteDimensional
  obtain ⟨hopen, hsmall⟩ := isAdic_iff.mp hO
  have hemb : Topology.IsEmbedding g := by
    refine ⟨(IsTopologicalAddGroup.isInducing_iff_nhds_zero).mpr ?_, hginj⟩
    apply le_antisymm
    · rw [(Metric.nhds_basis_ball.comap g).ge_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt
      refine Filter.mem_of_superset ((hopen n).mem_nhds (IsLocalRing.maximalIdeal O ^ n).zero_mem) ?_
      intro x hx
      simp only [Set.mem_preimage, mem_ball_zero_iff]
      rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_mul, norm_mul, map_pow, norm_pow]
      calc ‖g ϖ‖ ^ n * ‖g c‖ ≤ ‖g ϖ‖ ^ n * 1 :=
            mul_le_mul_of_nonneg_left (hint c) (by positivity)
        _ < ε := by rw [mul_one]; exact hn
    · intro t ht
      obtain ⟨n, hn⟩ := hsmall t ht
      rw [(Metric.nhds_basis_ball.comap g).mem_iff]
      refine ⟨‖g ϖ‖ ^ n, by positivity, ?_⟩
      intro x hx
      simp only [Set.mem_preimage, mem_ball_zero_iff] at hx
      apply hn
      rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have hϖn : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr (pow_ne_zero _ hϖ0)
      have hgϖn : 0 < ‖g (ϖ ^ n)‖ :=
        norm_pos_iff.mpr ((map_ne_zero_iff g hginj).mpr (pow_ne_zero _ hϖ0))
      obtain ⟨y, hy⟩ := hintc (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) (ϖ ^ n))
        (by
          rw [map_div₀, norm_div]
          change ‖g x‖ / ‖g (ϖ ^ n)‖ ≤ 1
          rw [div_le_one hgϖn, map_pow, norm_pow]
          exact hx.le)
      refine ⟨y, ?_⟩
      apply IsFractionRing.injective O (FractionRing O)
      rw [map_mul, hy]
      field_simp
  exact ⟨hemb, hclosed, hintc, hmax⟩

end GlobalTheory.CoefEmbed
