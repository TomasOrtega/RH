import Mathlib

open Polynomial

/- English proof (translation)
Establish `h0 : (p : PowerSeries O).map (IsLocalRing.residue O) ≠ 0`. Take `⟨i, hi⟩` from `hp`. Introduce `h`. Apply `hi` to reduce the goal to its premises. Use `congrArg (PowerSeries.coeff i) h` as an intermediate fact.

Rewrite `this` using `[PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero, IsLocalRing.residue_eq_zero_iff]`. Then use the resulting hypothesis. Take `⟨g, h, hg, hh, e⟩` from `PowerSeries.exists_isWeierstrassFactorization h0`. Establish `hI : IsLocalRing.maximalIdeal O ≠ ⊤` using `(IsLocalRing.maximalIdeal.isMaximal O).ne_top`. Establish `hd` using `hg.isWeierstrassDivisorAt hI`. Establish `hn : (((g : PowerSeries O).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat) = g.natDegree`.

Rewrite using `[← hg.coe_natDegree_eq_order_map (g : PowerSeries O) 1 (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)]`. Simplify using the standard rewrite rules. Establish `hdeg : g.degree = g.natDegree` using `Polynomial.degree_eq_natDegree hg.monic.ne_zero`. Establish `e2` using `Polynomial.modByMonic_add_div p g`. Establish `key` using `hd.eq_of_mul_add_eq_mul_add (q := h) (q' := ((p /ₘ g : O[X]) : PowerSeries O)) (r := 0) (r' := p %ₘ g) (by rw [hn, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _) (by rw [hn, ← hdeg]; exact Polynomial.degree_modByMonic_lt p hg.monic) (by`.

Rewrite using `[← e, Polynomial.coe_zero, add_zero, ← Polynomial.coe_mul, ← Polynomial.coe_add, add_comm, e2])`. Use `⟨g, p /ₘ g, hg.monic, ?_, ?_⟩` and prove the remaining obligations. Use `PowerSeries.isUnit_iff_constantCoeff.1 hh` as an intermediate fact. Rewrite `this` using `[key.1]`. Simplify using `using this`.

Rewrite `e2` using `[← key.2, zero_add]`. Conclude with `e2.symm`.
-/
private theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (p : O[X])
    (hp : ∃ i, p.coeff i ∉ IsLocalRing.maximalIdeal O) :
    ∃ g q : O[X], g.Monic ∧ IsUnit (q.coeff 0) ∧ p = g * q := by
  have h0 : (p : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    obtain ⟨i, hi⟩ := hp
    intro h
    apply hi
    have := congrArg (PowerSeries.coeff i) h
    rwa [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero,
      IsLocalRing.residue_eq_zero_iff] at this
  obtain ⟨g, h, hg, hh, e⟩ := PowerSeries.exists_isWeierstrassFactorization h0
  have hI : IsLocalRing.maximalIdeal O ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hd := hg.isWeierstrassDivisorAt hI
  have hn : (((g : PowerSeries O).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat) = g.natDegree := by
    rw [← hg.coe_natDegree_eq_order_map (g : PowerSeries O) 1
      (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)]
    simp
  have hdeg : g.degree = g.natDegree := Polynomial.degree_eq_natDegree hg.monic.ne_zero
  have e2 := Polynomial.modByMonic_add_div p g
  have key := hd.eq_of_mul_add_eq_mul_add (q := h) (q' := ((p /ₘ g : O[X]) : PowerSeries O))
    (r := 0) (r' := p %ₘ g)
    (by rw [hn, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [hn, ← hdeg]; exact Polynomial.degree_modByMonic_lt p hg.monic)
    (by
      rw [← e, Polynomial.coe_zero, add_zero, ← Polynomial.coe_mul, ← Polynomial.coe_add,
        add_comm, e2])
  refine ⟨g, p /ₘ g, hg.monic, ?_, ?_⟩
  · have := PowerSeries.isUnit_iff_constantCoeff.1 hh
    rw [key.1] at this
    simpa using this
  · rw [← key.2, zero_add] at e2
    exact e2.symm

/- English proof (translation)
Introduce `O _ _ _ _ R _ _ _ K _ _ _ _ f a ha`. Take `⟨p, hp0, hp⟩` from `Algebra.IsAlgebraic.isAlgebraic (R := O) (f a)`. Take `⟨inst⟩ : Nonempty (NormalizedGCDMonoid O)` from `inferInstance`. Establish `h1 : aeval (f a) p.primPart = 0` using `aeval_primPart_eq_zero hp0 hp`. Establish `h2 : ∃ i, p.primPart.coeff i ∉ IsLocalRing.maximalIdeal O`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Apply `hϖ.not_isUnit` to reduce the goal to its premises. Apply `isPrimitive_iff_isUnit_of_C_dvd.1 p.isPrimitive_primPart` to reduce the goal to its premises.

Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `i`. Use `hc i` as an intermediate fact. Rewrite `this` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Take `⟨g, q, hg, hq, e⟩` from `UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor _ h2`.

Establish `h3 : IsUnit (aeval a q)`. Assume the negation of the conclusion as `hu`. Establish `hm : aeval a q ∈ IsLocalRing.maximalIdeal R` using `hu`. Establish `e3 : aeval a q = aeval a q.divX * a + algebraMap O R (q.coeff 0)` using `by conv_lhs => rw [← divX_mul_X_add q]`. Simplify using the standard rewrite rules.

Rewrite `hm` using `[e3, Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ _ ha)]`. Conclude with `hm (hq.map _)`. Establish `h4 : aeval (f a) q ≠ 0`. Rewrite using `[aeval_algHom_apply]`. Conclude with `(h3.map f).ne_zero`.

Rewrite `h1` using `[e, map_mul]`. Conclude with `⟨g, hg, (mul_eq_zero.1 h1).resolve_right h4⟩`.
-/
theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type} [inst_4 : CommRing R]
    [inst_5 : Algebra O R] [inst_6 : IsLocalRing R] {K : Type} [inst_7 : Field K] [inst_8 : Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R, IsIntegral O ((f : R → K) a) := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f a ha
  classical
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O) (f a)
  obtain ⟨inst⟩ : Nonempty (NormalizedGCDMonoid O) := inferInstance
  have h1 : aeval (f a) p.primPart = 0 := aeval_primPart_eq_zero hp0 hp
  have h2 : ∃ i, p.primPart.coeff i ∉ IsLocalRing.maximalIdeal O := by
    by_contra hc
    push Not at hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    apply hϖ.not_isUnit
    apply isPrimitive_iff_isUnit_of_C_dvd.1 p.isPrimitive_primPart
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := hc i
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  obtain ⟨g, q, hg, hq, e⟩ := UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor _ h2
  have h3 : IsUnit (aeval a q) := by
    by_contra hu
    have hm : aeval a q ∈ IsLocalRing.maximalIdeal R := hu
    have e3 : aeval a q = aeval a q.divX * a + algebraMap O R (q.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add q]
      simp
    rw [e3, Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ _ ha)] at hm
    exact hm (hq.map _)
  have h4 : aeval (f a) q ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (h3.map f).ne_zero
  rw [e, map_mul] at h1
  exact ⟨g, hg, (mul_eq_zero.1 h1).resolve_right h4⟩
