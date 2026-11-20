import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Establish `hlpos : 0 < l` using `hl.out.pos`. Use `set fZ := (Polynomial.cyclotomic (l ^ (n + 1)) ℤ).comp (Polynomial.X + Polynomial.C 1) with hfZ`. Use `set g := (Polynomial.cyclotomic (l ^ (n + 1)) R).comp (Polynomial.X + Polynomial.C 1) with hg`. Establish `hgZ : g = fZ.map (Int.castRingHom R)`. Rewrite using `[hg, hfZ, Polynomial.map_comp, Polynomial.map_cyclotomic]`.

Simplify using the standard rewrite rules. Establish `hE : fZ.IsEisensteinAt (Submodule.span ℤ {(l : ℤ)})`. Rewrite using `[hfZ, Polynomial.C_1]`. Conclude with `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l n`. Establish `hq : (Polynomial.X + Polynomial.C (1 : R)).natDegree ≠ 0`.

Rewrite using `[Polynomial.natDegree_X_add_C]`. Conclude with `one_ne_zero`. Establish `hqZ : (Polynomial.X + Polynomial.C (1 : ℤ)).natDegree ≠ 0`. Rewrite using `[Polynomial.natDegree_X_add_C]`. Conclude with `one_ne_zero`.

Establish `hmon : g.Monic` using `(Polynomial.cyclotomic.monic _ R).comp (Polynomial.monic_X_add_C 1) hq`. Establish `hmonZ : fZ.Monic` using `(Polynomial.cyclotomic.monic _ ℤ).comp (Polynomial.monic_X_add_C 1) hqZ`. Establish `hdeg : g.natDegree = fZ.natDegree`. Rewrite using `[hgZ, hmonZ.natDegree_map]`. Establish `hP : (Ideal.span {(l : R)}).IsPrime` using `(Ideal.span_singleton_prime hp.ne_zero).2 hp`.

Establish `hgpos : 0 < g.natDegree`. Rewrite using `[hg, Polynomial.natDegree_comp, Polynomial.natDegree_cyclotomic, Polynomial.natDegree_X_add_C, mul_one]`. Conclude with `Nat.totient_pos.2 (pow_pos hlpos _)`. Establish `hirr : Irreducible g`. Apply `Polynomial.irreducible_of_eisenstein_criterion hP` to reduce the goal to its premises.

Rewrite using `[hmon.leadingCoeff]`. Conclude with `fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Introduce `k hk`. Establish `hk' : k < fZ.natDegree`. Rewrite using `[← hdeg]`.

Conclude with `Polynomial.coe_lt_degree.mp hk`. Establish `hmem` using `hE.mem hk'`. Rewrite `hmem` using `[Ideal.submodule_span_eq, Ideal.mem_span_singleton]`. Rewrite using `[hgZ, Polynomial.coeff_map, Ideal.mem_span_singleton]`. Use `map_dvd (Int.castRingHom R) hmem` as an intermediate fact.

Simplify using `using this`. Conclude with `Polynomial.natDegree_pos_iff_degree_pos.mp hgpos`. Rewrite using `[Polynomial.coeff_zero_eq_eval_zero, hg, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add, Polynomial.eval_one_cyclotomic_prime_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Introduce and unpack `⟨a, ha⟩`. Apply `hp.not_unit` to reduce the goal to its premises.

Establish `h1 : (l : R) * 1 = (l : R) * ((l : R) * a)`. Rewrite using `[mul_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `mul_left_cancel₀ hp.ne_zero h1`. Conclude with `isUnit_iff_exists_inv.2 ⟨a, h2.symm⟩`.

Conclude with `hmon.isPrimitive`. Establish `ht : (Polynomial.taylorEquiv (1 : R)) (Polynomial.cyclotomic (l ^ (n + 1)) R) = g`. Rewrite using `[hg, ← Polynomial.taylor_apply]`. Both sides reduce to the same expression. Rewrite `hirr` using `[← ht]`.

Conclude with `(MulEquiv.irreducible_iff _).1 hirr`.
-/
private theorem wd_irr (R : Type) [CommRing R] [IsDomain R] (l : ℕ) [hl : Fact l.Prime] (hp : Prime (l : R)) (n : ℕ) :
    Irreducible (Polynomial.cyclotomic (l ^ (n + 1)) R) := by
  classical
  have hlpos : 0 < l := hl.out.pos
  set fZ := (Polynomial.cyclotomic (l ^ (n + 1)) ℤ).comp (Polynomial.X + Polynomial.C 1) with hfZ
  set g := (Polynomial.cyclotomic (l ^ (n + 1)) R).comp (Polynomial.X + Polynomial.C 1) with hg
  have hgZ : g = fZ.map (Int.castRingHom R) := by
    rw [hg, hfZ, Polynomial.map_comp, Polynomial.map_cyclotomic]
    simp
  have hE : fZ.IsEisensteinAt (Submodule.span ℤ {(l : ℤ)}) := by
    rw [hfZ, Polynomial.C_1]
    exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l n
  have hq : (Polynomial.X + Polynomial.C (1 : R)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  have hqZ : (Polynomial.X + Polynomial.C (1 : ℤ)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  have hmon : g.Monic := (Polynomial.cyclotomic.monic _ R).comp (Polynomial.monic_X_add_C 1) hq
  have hmonZ : fZ.Monic := (Polynomial.cyclotomic.monic _ ℤ).comp (Polynomial.monic_X_add_C 1) hqZ
  have hdeg : g.natDegree = fZ.natDegree := by
    rw [hgZ, hmonZ.natDegree_map]
  have hP : (Ideal.span {(l : R)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hgpos : 0 < g.natDegree := by
    rw [hg, Polynomial.natDegree_comp, Polynomial.natDegree_cyclotomic, Polynomial.natDegree_X_add_C,
      mul_one]
    exact Nat.totient_pos.2 (pow_pos hlpos _)
  have hirr : Irreducible g := by
    apply Polynomial.irreducible_of_eisenstein_criterion hP
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro k hk
      have hk' : k < fZ.natDegree := by
        rw [← hdeg]
        exact Polynomial.coe_lt_degree.mp hk
      have hmem := hE.mem hk'
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
      rw [hgZ, Polynomial.coeff_map, Ideal.mem_span_singleton]
      have := map_dvd (Int.castRingHom R) hmem
      simpa using this
    · exact Polynomial.natDegree_pos_iff_degree_pos.mp hgpos
    · rw [Polynomial.coeff_zero_eq_eval_zero, hg, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C, zero_add, Polynomial.eval_one_cyclotomic_prime_pow,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨a, ha⟩
      apply hp.not_unit
      have h1 : (l : R) * 1 = (l : R) * ((l : R) * a) := by
        rw [mul_one]
        calc (l : R) = (l : R) ^ 2 * a := ha
          _ = (l : R) * ((l : R) * a) := by ring
      have h2 := mul_left_cancel₀ hp.ne_zero h1
      exact isUnit_iff_exists_inv.2 ⟨a, h2.symm⟩
    · exact hmon.isPrimitive
  have ht : (Polynomial.taylorEquiv (1 : R)) (Polynomial.cyclotomic (l ^ (n + 1)) R) = g := by
    rw [hg, ← Polynomial.taylor_apply]
    rfl
  rw [← ht] at hirr
  exact (MulEquiv.irreducible_iff _).1 hirr

/- English proof (translation)
Use `{ cond' := ?_ }` and prove the remaining obligations. Introduce `a b`. Establish `ha : (a : Ω) ∈ A ∧ ∀ s ∈ Ine A, s (a : Ω) = a` using `a.2`. Establish `hb : (b : Ω) ∈ A ∧ ∀ s ∈ Ine A, s (b : Ω) = b` using `b.2`. Distinguish the cases in `ha0 : (a : Ω) = 0`.

Use `⟨0, Or.inr ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[ha0]`. Distinguish the cases in `hb0 : (b : Ω) = 0`. Use `⟨0, Or.inl ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hb0]`. Break down `A.mem_or_inv_mem ((b : Ω) / a) with h | h` into its components or cases. Establish `hc : (b : Ω) / a ∈ R0 A`. Use `⟨h, fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, ha.2 s hs, hb.2 s hs]`. Use `⟨⟨_, hc⟩, Or.inl ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_div_cancel₀ _ ha0]`. Rewrite `h` using `[inv_div]`.

Establish `hc : (a : Ω) / b ∈ R0 A`. Use `⟨h, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, ha.2 s hs, hb.2 s hs]`. Use `⟨⟨_, hc⟩, Or.inr ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[mul_div_cancel₀ _ hb0]`.
-/
private theorem wd_val {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) : ValuationRing (R0 A) := by
  refine { cond' := ?_ }
  intro a b
  have ha : (a : Ω) ∈ A ∧ ∀ s ∈ Ine A, s (a : Ω) = a := a.2
  have hb : (b : Ω) ∈ A ∧ ∀ s ∈ Ine A, s (b : Ω) = b := b.2
  by_cases ha0 : (a : Ω) = 0
  · refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    simp [ha0]
  by_cases hb0 : (b : Ω) = 0
  · refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simp [hb0]
  rcases A.mem_or_inv_mem ((b : Ω) / a) with h | h
  · have hc : (b : Ω) / a ∈ R0 A := by
      refine ⟨h, fun s hs => ?_⟩
      rw [map_div₀, ha.2 s hs, hb.2 s hs]
    refine ⟨⟨_, hc⟩, Or.inl ?_⟩
    apply Subtype.ext
    simp [mul_div_cancel₀ _ ha0]
  · rw [inv_div] at h
    have hc : (a : Ω) / b ∈ R0 A := by
      refine ⟨h, fun s hs => ?_⟩
      rw [map_div₀, ha.2 s hs, hb.2 s hs]
    refine ⟨⟨_, hc⟩, Or.inr ?_⟩
    apply Subtype.ext
    simp [mul_div_cancel₀ _ hb0]

/- English proof (translation)
Establish `hN : l ^ m ≠ 0` using `pow_ne_zero _ hl.out.ne_zero`. Establish `hvz : A.valuation z = 1`. Establish `h1 : A.valuation z ^ (l ^ m) = 1`. Rewrite using `[← map_pow, hz, map_one]`. Break down `lt_trichotomy (A.valuation z) 1 with h2 | h2 | h2` into its components or cases.

Conclude with `absurd h1 (ne_of_lt (pow_lt_one₀ zero_le' h2 hN))`. Conclude with `h2`. Conclude with `absurd h1 (ne_of_gt (one_lt_pow₀ h2 hN))`. Establish `hzA : z ∈ A` using `(A.valuation_le_one_iff z).1 hvz.le`. Use `⟨hzA, ?_⟩` and prove the remaining obligations.

Set `zA : A` to `⟨z, hzA⟩`. Establish `hlmax : (l : A) ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[A.valuation_lt_one_iff]`. Simplify using `using h`. Use `haveI : CharP (IsLocalRing.ResidueField A) l := by`.

Rewrite using `[CharP.charP_iff_prime_eq_zero hl.out]`. Use `(IsLocalRing.residue_eq_zero_iff _).2 hlmax` as an intermediate fact. Simplify using `using this`. Establish `hzN : zA ^ (l ^ m) = 1` using `Subtype.ext (by simpa using hz)`. Establish `hres : (IsLocalRing.residue A zA - 1) ^ (l ^ m) = 0`.

Rewrite using `[sub_pow_char_pow, one_pow, ← map_pow, hzN, map_one, sub_self]`. Establish `h0` using `(pow_eq_zero_iff hN).1 hres`. Establish `hmem : zA - 1 ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]`. Conclude with `h0`.

Use `(A.valuation_lt_one_iff (zA - 1)).1 hmem` as an intermediate fact. Simplify using `using this`.
-/
private theorem wd_res {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l : ℕ) [hl : Fact l.Prime]
    (h : A.valuation (l : Ω) < 1) (m : ℕ) (z : Ω) (hz : z ^ l ^ m = 1) :
    z ∈ A ∧ A.valuation (z - 1) < 1 := by
  have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  have hvz : A.valuation z = 1 := by
    have h1 : A.valuation z ^ (l ^ m) = 1 := by
      rw [← map_pow, hz, map_one]
    rcases lt_trichotomy (A.valuation z) 1 with h2 | h2 | h2
    · exact absurd h1 (ne_of_lt (pow_lt_one₀ zero_le' h2 hN))
    · exact h2
    · exact absurd h1 (ne_of_gt (one_lt_pow₀ h2 hN))
  have hzA : z ∈ A := (A.valuation_le_one_iff z).1 hvz.le
  refine ⟨hzA, ?_⟩
  let zA : A := ⟨z, hzA⟩
  have hlmax : (l : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [A.valuation_lt_one_iff]
    simpa using h
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out]
    have := (IsLocalRing.residue_eq_zero_iff _).2 hlmax
    simpa using this
  have hzN : zA ^ (l ^ m) = 1 := Subtype.ext (by simpa using hz)
  have hres : (IsLocalRing.residue A zA - 1) ^ (l ^ m) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← map_pow, hzN, map_one, sub_self]
  have h0 := (pow_eq_zero_iff hN).1 hres
  have hmem : zA - 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
    exact h0
  have := (A.valuation_lt_one_iff (zA - 1)).1 hmem
  simpa using this

/- English proof (translation)
Establish `hl0 : (l : R0 A) ≠ 0`. Introduce `h0`. Establish `h1 : ((l : R0 A) : Ω) = 0`. Rewrite using `[h0]`. Both sides reduce to the same expression.

Move the coercions through the operations in `at h1`. Rewrite `h1` using `[← map_natCast (algebraMap ℚ Ω)]`. Establish `h2` using `(map_eq_zero_iff _ (algebraMap ℚ Ω).injective).1 h1`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2`. Use `⟨hl0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hu`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `hw' : (l : Ω) * (w : Ω) = 1`. Use `congrArg Subtype.val hw` as an intermediate fact. Simplify using `using this`.

Establish `h2 : A.valuation (l : Ω) * A.valuation (w : Ω) < 1` using `(mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 w.2.1)).trans_lt hval`. Rewrite `h2` using `[← map_mul, hw', map_one]`. Conclude with `lt_irrefl 1 h2`. Introduce `a b hab`. Establish `hab' : (l : Φ.R) ∣ Φ.i0 a * Φ.i0 b`.

Use `map_dvd Φ.i0 hab` as an intermediate fact. Simplify `this` using `[map_mul]`. Establish `hback : ∀ c : R0 A, (l : Φ.R) ∣ Φ.i0 c → (l : R0 A) ∣ c`. Introduce `c hc`. Use `Φ.sep c 1 (by rw [pow_one]; exact Ideal.mem_span_singleton.2 hc)` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Conclude with `Ideal.mem_span_singleton.1 this`. Break down `Φ.fl.prime.2.2 _ _ hab' with h | h` into its components or cases. Conclude with `Or.inl (hback a h)`. Conclude with `Or.inr (hback b h)`.
-/
private theorem prime_natCast_r0_of_valuation_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Φ : Fr l A j) (hval : A.valuation (l : Ω) < 1) :
    Prime (l : R0 A) := by
  have hl0 : (l : R0 A) ≠ 0 := by
    intro h0
    have h1 : ((l : R0 A) : Ω) = 0 := by
      rw [h0]
      rfl
    push_cast at h1
    rw [← map_natCast (algebraMap ℚ Ω)] at h1
    have h2 := (map_eq_zero_iff _ (algebraMap ℚ Ω).injective).1 h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  refine ⟨hl0, ?_, ?_⟩
  · intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : (l : Ω) * (w : Ω) = 1 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h2 : A.valuation (l : Ω) * A.valuation (w : Ω) < 1 :=
      (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 w.2.1)).trans_lt hval
    rw [← map_mul, hw', map_one] at h2
    exact lt_irrefl 1 h2
  · intro a b hab
    have hab' : (l : Φ.R) ∣ Φ.i0 a * Φ.i0 b := by
      have := map_dvd Φ.i0 hab
      simpa [map_mul] using this
    have hback : ∀ c : R0 A, (l : Φ.R) ∣ Φ.i0 c → (l : R0 A) ∣ c := by
      intro c hc
      have := Φ.sep c 1 (by rw [pow_one]; exact Ideal.mem_span_singleton.2 hc)
      rw [pow_one] at this
      exact Ideal.mem_span_singleton.1 this
    rcases Φ.fl.prime.2.2 _ _ hab' with h | h
    · exact Or.inl (hback a h)
    · exact Or.inr (hback b h)

/- English proof (translation)
Introduce `l _ _ Ω _ _ _ A hA j Φ ζ hζ m hm P`. Take `⟨v, hv, hlv⟩` from `hA`. Establish `hval : A.valuation (l : Ω) < 1`. Use `(hv (l : 𝓞 ℚ)).2 hlv` as an intermediate fact. Simplify using `using this`.

Use `haveI := wd_val A`. Establish `hroot : ∀ i : ℕ, (ζ m ^ i) ^ l ^ m = 1`. Introduce `i`. Rewrite using `[← pow_mul, mul_comm, pow_mul, (hζ m).1.pow_eq_one, one_pow]`. Establish `hdiff : pv P (ζ m) - ((P.eval 1 : R0 A) : Ω) = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : R0 A) : Ω) * (ζ m ^ i - 1)`.

Rewrite using `[pv, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]`. Use `push_cast`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mul_sub]`.

Establish `hcc : PowerSeries.constantCoeff (Φ.ser P) = Φ.i0 (P.eval 1)`. Unfold `Fr.ser`. Rewrite using `[Polynomial.hom_eval₂]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce `hP`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `hirr` using `wd_irr (R0 A) l (prime_natCast_r0_of_valuation_lt_one l A j Φ hval) k`. Use `letI := IsBezout.toGCDDomain (R0 A)`. Establish `hcycroot : Polynomial.aeval (ζ (k + 1)) (Polynomial.cyclotomic (l ^ (k + 1)) (R0 A)) = 0`.

Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `(hζ (k + 1)).1.isRoot_cyclotomic (pow_pos (Fact.out : l.Prime).pos _)`. Establish `hint : IsIntegral (R0 A) (ζ (k + 1))` using `⟨_, Polynomial.cyclotomic.monic _ _, hcycroot⟩`. Establish `hdvdP : minpoly (R0 A) (ζ (k + 1)) ∣ P` using `minpoly.isIntegrallyClosed_dvd hint hP`. Establish `hdvdC : minpoly (R0 A) (ζ (k + 1)) ∣ Polynomial.cyclotomic (l ^ (k + 1)) (R0 A)` using `minpoly.isIntegrallyClosed_dvd hint hcycroot`.

Take `⟨q, hq⟩` from `hdvdC`. Establish `hqu : IsUnit q` using `(hirr.isUnit_or_isUnit hq).resolve_left (minpoly.not_isUnit _ _)`. Establish `hCP : Polynomial.cyclotomic (l ^ (k + 1)) (R0 A) ∣ P`. Use `dvd_trans ?_ hdvdP` and prove the remaining obligations. Rewrite using `[hq]`.

Conclude with `hqu.mul_right_dvd.2 dvd_rfl`. Take `⟨Q, hQ⟩` from `hCP`. Unfold `Fr.ser`. Rewrite using `[hQ, Polynomial.map_mul, Polynomial.eval₂_mul, Polynomial.map_cyclotomic, map_mul]`. Establish `hc : Polynomial.eval₂ PowerSeries.C (1 + PowerSeries.X) (Polynomial.cyclotomic (l ^ (k + 1)) Φ.R) = cyc Φ.R l (k + 1)` using `rfl`.

Rewrite using `[hc, ev_cyc_self, zero_mul]`. Introduce and unpack `⟨hA1, hne, hinv⟩`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, hcc]`. Apply `Φ.unit` to reduce the goal to its premises. Introduce `hmem`.

Establish `hy : P.eval 1 ∈ Ideal.span {(l : R0 A)}`. Use `Φ.sep (P.eval 1) 1 (by rw [pow_one]; exact hmem)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `hvy : A.valuation ((P.eval 1 : R0 A) : Ω) < 1`.

Rewrite using `[← ha]`. Use `push_cast`. Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 a.2.1)).trans_lt hval`. Establish `hvd : A.valuation (pv P (ζ m) - ((P.eval 1 : R0 A) : Ω)) < 1`.

Rewrite using `[hdiff]`. Apply `Valuation.map_sum_lt _ one_ne_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[map_mul]`. Use `(mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (P.coeff i).2.1)).trans_lt ?_` and prove the remaining obligations.

Conclude with `(wd_res A l hval m _ (hroot i)).2`. Establish `hvp : A.valuation (pv P (ζ m)) < 1`. Use `Valuation.map_add_lt _ hvd hvy` as an intermediate fact. Simplify using `using this`. Establish `h1 : A.valuation (pv P (ζ m)) * A.valuation (pv P (ζ m))⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel₀ hne, map_one]`. Establish `h2 : A.valuation (pv P (ζ m)) * A.valuation (pv P (ζ m))⁻¹ < 1` using `(mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hinv)).trans_lt hvp`. Rewrite `h2` using `[h1]`. Conclude with `lt_irrefl 1 h2`.
-/
theorem UpperTheory.Kd.C7.pWD :
    UpperTheory.Kd.C7.SWD := by
  intro l _ _ Ω _ _ _ A hA j Φ ζ hζ m hm P
  obtain ⟨v, hv, hlv⟩ := hA
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  haveI := wd_val A
  have hroot : ∀ i : ℕ, (ζ m ^ i) ^ l ^ m = 1 := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, (hζ m).1.pow_eq_one, one_pow]
  have hdiff : pv P (ζ m) - ((P.eval 1 : R0 A) : Ω)
      = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : R0 A) : Ω) * (ζ m ^ i - 1) := by
    rw [pv, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_sub]
  have hcc : PowerSeries.constantCoeff (Φ.ser P) = Φ.i0 (P.eval 1) := by
    unfold Fr.ser
    rw [Polynomial.hom_eval₂]
    simp
  constructor
  · intro hP
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hirr := wd_irr (R0 A) l (prime_natCast_r0_of_valuation_lt_one l A j Φ hval) k
    classical
    letI := IsBezout.toGCDDomain (R0 A)
    have hcycroot : Polynomial.aeval (ζ (k + 1)) (Polynomial.cyclotomic (l ^ (k + 1)) (R0 A)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact (hζ (k + 1)).1.isRoot_cyclotomic (pow_pos (Fact.out : l.Prime).pos _)
    have hint : IsIntegral (R0 A) (ζ (k + 1)) := ⟨_, Polynomial.cyclotomic.monic _ _, hcycroot⟩
    have hdvdP : minpoly (R0 A) (ζ (k + 1)) ∣ P := minpoly.isIntegrallyClosed_dvd hint hP
    have hdvdC : minpoly (R0 A) (ζ (k + 1)) ∣ Polynomial.cyclotomic (l ^ (k + 1)) (R0 A) :=
      minpoly.isIntegrallyClosed_dvd hint hcycroot
    obtain ⟨q, hq⟩ := hdvdC
    have hqu : IsUnit q := (hirr.isUnit_or_isUnit hq).resolve_left (minpoly.not_isUnit _ _)
    have hCP : Polynomial.cyclotomic (l ^ (k + 1)) (R0 A) ∣ P := by
      refine dvd_trans ?_ hdvdP
      rw [hq]
      exact hqu.mul_right_dvd.2 dvd_rfl
    obtain ⟨Q, hQ⟩ := hCP
    unfold Fr.ser
    rw [hQ, Polynomial.map_mul, Polynomial.eval₂_mul, Polynomial.map_cyclotomic, map_mul]
    have hc : Polynomial.eval₂ PowerSeries.C (1 + PowerSeries.X)
        (Polynomial.cyclotomic (l ^ (k + 1)) Φ.R) = cyc Φ.R l (k + 1) := rfl
    rw [hc, ev_cyc_self, zero_mul]
  · rintro ⟨hA1, hne, hinv⟩
    rw [PowerSeries.isUnit_iff_constantCoeff, hcc]
    apply Φ.unit
    intro hmem
    have hy : P.eval 1 ∈ Ideal.span {(l : R0 A)} := by
      have := Φ.sep (P.eval 1) 1 (by rw [pow_one]; exact hmem)
      rwa [pow_one] at this
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hy
    have hvy : A.valuation ((P.eval 1 : R0 A) : Ω) < 1 := by
      rw [← ha]
      push_cast
      rw [map_mul]
      exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 a.2.1)).trans_lt hval
    have hvd : A.valuation (pv P (ζ m) - ((P.eval 1 : R0 A) : Ω)) < 1 := by
      rw [hdiff]
      apply Valuation.map_sum_lt _ one_ne_zero
      intro i _
      rw [map_mul]
      refine (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (P.coeff i).2.1)).trans_lt ?_
      exact (wd_res A l hval m _ (hroot i)).2
    have hvp : A.valuation (pv P (ζ m)) < 1 := by
      have := Valuation.map_add_lt _ hvd hvy
      simpa using this
    have h1 : A.valuation (pv P (ζ m)) * A.valuation (pv P (ζ m))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    have h2 : A.valuation (pv P (ζ m)) * A.valuation (pv P (ζ m))⁻¹ < 1 :=
      (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hinv)).trans_lt hvp
    rw [h1] at h2
    exact lt_irrefl 1 h2
