import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.InertiaInvariantValuationUniformizerBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Break down `eq_or_ne a 0 with rfl | h0` into its components or cases. Conclude with `A.zero_mem`. Break down `A.mem_or_inv_mem a with h | h` into its components or cases. Conclude with `h`. Establish `h1 : a * a ^ (q - 2) = 1`.

Rewrite using `[← pow_succ', show q - 2 + 1 = q - 1 by omega]`. Establish `: a ^ q = a ^ (q - 1) * a` using `by rw [← pow_succ, Nat.sub_add_cancel (by omega)]`. Rewrite `ha` using `[this]`. Conclude with `(mul_eq_right₀ h0).1 ha`. Rewrite using `[eq_inv_of_mul_eq_one_left h1, ← inv_pow]`.

Conclude with `A.pow_mem h _`.
-/
private theorem zero_one_mem_gammaSet_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q : ℕ} (hq2 : 2 ≤ q) {a : Ω} (ha : a ^ q = a) : a ∈ A := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact A.zero_mem
  rcases A.mem_or_inv_mem a with h | h
  · exact h
  · have h1 : a * a ^ (q - 2) = 1 := by
      rw [← pow_succ', show q - 2 + 1 = q - 1 by omega]
      have : a ^ q = a ^ (q - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [this] at ha
      exact (mul_eq_right₀ h0).1 ha
    rw [eq_inv_of_mul_eq_one_left h1, ← inv_pow]
    exact A.pow_mem h _

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hS : (∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i)) = 1`. Establish `h` using `geom_sum₂_mul a b q`. Rewrite `h` using `[ha', hb']`. Establish `hsub : a - b ≠ 0` using `sub_ne_zero.2 hne`.

Conclude with `(mul_eq_right₀ hsub).1 h`. Use `set a' : A := ⟨a, ha⟩`. Use `set b' : A := ⟨b, hb⟩`. Establish `hS' : (∑ i ∈ Finset.range q, a' ^ i * b' ^ (q - 1 - i)) = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using hS`. Establish `hr : IsLocalRing.residue A a' = IsLocalRing.residue A b'`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]`. Simplify using `using hab`. Establish `hq' : IsLocalRing.residue A (q : A) = 0`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]`. Simplify using `using hq`. Use `congrArg (IsLocalRing.residue A) hS'` as an intermediate fact. Rewrite `this` using `[map_sum, map_one]`. Simplify using `only [map_mul, map_pow, ← hr] at this`.

Rewrite `this` using `[Finset.sum_congr rfl (fun i hi => by rw [← pow_add, Nat.add_sub_cancel' (by have := Finset.mem_range.1 hi; omega)])]`. Rewrite `this` using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← map_natCast (IsLocalRing.residue A), hq', zero_mul]`. Conclude with `zero_ne_one this`.
-/
private theorem eq_of_pow_eq_self_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q : ℕ} (hq : A.valuation (q : Ω) < 1) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A) (ha' : a ^ q = a) (hb' : b ^ q = b) (hab : A.valuation (a - b) < 1) : a = b := by
  by_contra hne
  have hS : (∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i)) = 1 := by
    have h := geom_sum₂_mul a b q
    rw [ha', hb'] at h
    have hsub : a - b ≠ 0 := sub_ne_zero.2 hne
    exact (mul_eq_right₀ hsub).1 h
  set a' : A := ⟨a, ha⟩
  set b' : A := ⟨b, hb⟩
  have hS' : (∑ i ∈ Finset.range q, a' ^ i * b' ^ (q - 1 - i)) = 1 := by
    apply Subtype.ext
    simpa using hS
  have hr : IsLocalRing.residue A a' = IsLocalRing.residue A b' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hab
  have hq' : IsLocalRing.residue A (q : A) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hq
  have := congrArg (IsLocalRing.residue A) hS'
  rw [map_sum, map_one] at this
  simp only [map_mul, map_pow, ← hr] at this
  rw [Finset.sum_congr rfl (fun i hi => by rw [← pow_add, Nat.add_sub_cancel' (by have := Finset.mem_range.1 hi; omega)])] at this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← map_natCast (IsLocalRing.residue A), hq', zero_mul] at this
  exact zero_ne_one this

/- English proof (translation)
Establish `hlK : ((l : ℕ) : IsLocalRing.ResidueField A) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]`. Simplify using `using hl`. Use `haveI : CharP (IsLocalRing.ResidueField A) l := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK`. Use `letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l`.

Take `⟨Q, hQ0, hQ⟩` from `(IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 halg`. Establish `hc0 : Q.content ≠ 0`. Rewrite using `[Ne, Polynomial.content_eq_zero_iff]` and apply the resulting hypothesis. Establish `hQ'Ω : Polynomial.aeval (a : Ω) Q.primPart = 0`. Establish `h` using `hQ`.

Rewrite `h` using `[Polynomial.eq_C_content_mul_primPart Q, map_mul, Polynomial.aeval_C]`. Use `(mul_eq_zero.1 h).resolve_left ?_` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply ℤ ℚ Ω]`. Conclude with `(map_ne_zero (algebraMap ℚ Ω)).2 (by simpa using hc0)`. Establish `hQ'A : Polynomial.aeval a Q.primPart = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((Polynomial.aeval a Q.primPart : A) : Ω) = (0 : Ω)`. Rewrite using `[← hQ'Ω]`. Conclude with `(Polynomial.aeval_algHom_apply A.subtype.toIntAlgHom a Q.primPart).symm`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ¬ (l : ℤ) ∣ Q.primPart.coeff i := by`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hd : Polynomial.C (l : ℤ) ∣ Q.primPart` using `Polynomial.C_dvd_iff_dvd_coeff _ _ |>.2 hall`. Establish `hu` using `Polynomial.isPrimitive_primPart Q _ hd`. Rewrite `hu` using `[Int.isUnit_iff]`.

Use `hp.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set Q2 := Q.primPart.map (Int.castRingHom (ZMod l))`. Establish `hQ2 : Q2 ≠ 0`. Introduce `h`.

Use `congrArg (fun p => Polynomial.coeff p i) h` as an intermediate fact. Simplify using `only [Q2, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this`. Conclude with `hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this)`. Establish `hev : Polynomial.aeval (IsLocalRing.residue A a) Q2 = 0`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod l) _).comp (Int.castRingHom _)) (algebraMap ℤ _), ← Polynomial.aeval_def]`.

Conclude with `(Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a Q.primPart).trans (by`. Express the relevant statement in the definitionally equal form `IsLocalRing.residue A (Polynomial.aeval a Q.primPart) = 0`. Rewrite using `[hQ'A, map_zero])`. Establish `hint : IsIntegral (ZMod l) (IsLocalRing.residue A a)` using `IsAlgebraic.isIntegral (⟨Q2, hQ2, hev⟩ : IsAlgebraic (ZMod l) (IsLocalRing.residue A a))`. Use `haveI := IntermediateField.adjoin.finiteDimensional hint`.

Use `haveI : Finite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) := Module.finite_of_finite (ZMod l)`. Use `letI := Fintype.ofFinite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})`. Use `⟨Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}), Fintype.one_lt_card, ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `FiniteField.cast_card_eq_zero (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})`. Establish `h1 : ((Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) : ℕ) : IsLocalRing.ResidueField A) = 0`.

Use `congrArg (algebraMap (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) (IsLocalRing.ResidueField A)) h0` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Then use the resulting hypothesis. Rewrite `h1` using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]`. Simplify using `using h1`. Establish `h0` using `FiniteField.pow_card (⟨IsLocalRing.residue A a, IntermediateField.mem_adjoin_simple_self _ _⟩ : (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}))`.

Establish `h1` using `congrArg Subtype.val h0`. Simplify using `only [IntermediateField.coe_pow] at h1`. Rewrite `h1` using `[← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]`. Simplify using `using h1`.
-/
private theorem fin_lemma_3 {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l : ℕ} [hp : Fact l.Prime] (hl : A.valuation (l : Ω) < 1) (a : A) (halg : IsAlgebraic ℚ (a : Ω)) :
    ∃ q : ℕ, 2 ≤ q ∧ A.valuation (q : Ω) < 1 ∧ A.valuation ((a : Ω) ^ q - a) < 1 := by
  have hlK : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hl
  haveI : CharP (IsLocalRing.ResidueField A) l := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  obtain ⟨Q, hQ0, hQ⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 halg
  have hc0 : Q.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hQ'Ω : Polynomial.aeval (a : Ω) Q.primPart = 0 := by
    have h := hQ
    rw [Polynomial.eq_C_content_mul_primPart Q, map_mul, Polynomial.aeval_C] at h
    refine (mul_eq_zero.1 h).resolve_left ?_
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Ω]
    exact (map_ne_zero (algebraMap ℚ Ω)).2 (by simpa using hc0)
  have hQ'A : Polynomial.aeval a Q.primPart = 0 := by
    apply Subtype.ext
    change ((Polynomial.aeval a Q.primPart : A) : Ω) = (0 : Ω)
    rw [← hQ'Ω]
    exact (Polynomial.aeval_algHom_apply A.subtype.toIntAlgHom a Q.primPart).symm
  obtain ⟨i, hi⟩ : ∃ i, ¬ (l : ℤ) ∣ Q.primPart.coeff i := by
    by_contra hall
    push_neg at hall
    have hd : Polynomial.C (l : ℤ) ∣ Q.primPart := Polynomial.C_dvd_iff_dvd_coeff _ _ |>.2 hall
    have hu := Polynomial.isPrimitive_primPart Q _ hd
    rw [Int.isUnit_iff] at hu
    have := hp.out.two_le
    omega
  set Q2 := Q.primPart.map (Int.castRingHom (ZMod l))
  have hQ2 : Q2 ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p i) h
    simp only [Q2, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
    exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this)
  have hev : Polynomial.aeval (IsLocalRing.residue A a) Q2 = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod l) _).comp (Int.castRingHom _)) (algebraMap ℤ _), ← Polynomial.aeval_def]
    exact (Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a Q.primPart).trans (by
      change IsLocalRing.residue A (Polynomial.aeval a Q.primPart) = 0
      rw [hQ'A, map_zero])
  have hint : IsIntegral (ZMod l) (IsLocalRing.residue A a) := IsAlgebraic.isIntegral (⟨Q2, hQ2, hev⟩ : IsAlgebraic (ZMod l) (IsLocalRing.residue A a))
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})
  refine ⟨Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}), Fintype.one_lt_card, ?_, ?_⟩
  · have h0 := FiniteField.cast_card_eq_zero (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})
    have h1 : ((Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) : ℕ) : IsLocalRing.ResidueField A) = 0 := by
      have := congrArg (algebraMap (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) (IsLocalRing.ResidueField A)) h0
      rwa [map_natCast, map_zero] at this
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h1
    simpa using h1
  · have h0 := FiniteField.pow_card (⟨IsLocalRing.residue A a, IntermediateField.mem_adjoin_simple_self _ _⟩ : (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}))
    have h1 := congrArg Subtype.val h0
    simp only [IntermediateField.coe_pow] at h1
    rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h1
    simpa using h1

/- English proof (translation)
Take `⟨q, hq2, hq, haq⟩` from `fin_lemma_3 A hl a halg`. Use `set T : Polynomial Ω := Polynomial.X ^ q - Polynomial.X with hT`. Establish `hTm : T.Monic` using `Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast (by omega : 1 < q))`. Establish `hprod` using `(Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hTm (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits T))).symm`. Establish `hroot : ∀ w ∈ T.roots, w ^ q = w`.

Introduce `w hw`. Use `(Polynomial.mem_roots hTm.ne_zero).1 hw` as an intermediate fact. Simplify `this` using `[T, sub_eq_zero]`. Establish `hev : T.eval (a : Ω) = (T.roots.map fun w => (a : Ω) - w).prod` using `by conv_lhs => rw [hprod]`. Rewrite using `[Polynomial.eval_multiset_prod, Multiset.map_map]`.

Simplify using `[Function.comp_def]`. Establish `hv : A.valuation (T.eval (a : Ω)) < 1` using `by simpa [T] using haq`. Rewrite `hv` using `[hev, map_multiset_prod, Multiset.map_map]`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hwv⟩ : ∃ w ∈ T.roots, A.valuation ((a : Ω) - w) < 1 := by`. Assume the negation of the conclusion as `hno`.

Use `push_neg at hno`. Establish `h1 : (T.roots.map (A.valuation ∘ fun w => (a : Ω) - w)).prod = 1`. Apply `Multiset.prod_eq_one` to reduce the goal to its premises. Introduce `x hx`. Take `⟨w, hw, rfl⟩` from `Multiset.mem_map.1 hx`.

Use `le_antisymm ?_ (hno w hw)` and prove the remaining obligations. Conclude with `(A.valuation_le_one_iff _).2 (A.sub_mem a.2 (zero_one_mem_gammaSet_one A hq2 (hroot w hw)))`. Rewrite `hv` using `[h1]`. Conclude with `lt_irrefl _ hv`. Establish `hwA : w ∈ A` using `zero_one_mem_gammaSet_one A hq2 (hroot w hw)`.

Use `⟨w, ⟨hwA, fun s hs => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hsq : (s w) ^ q = s w` using `by rw [← map_pow, hroot w hw]`. Express the relevant statement in the definitionally equal form `s ∈ Inertia A at hs`. Unfold `Inertia at hs`. Conclude with `eq_of_pow_eq_self_of_valuation_sub_lt_one A hq (zero_one_mem_gammaSet_one A hq2 hsq) hwA hsq (hroot w hw) (hs.2 w ((A.valuation_le_one_iff _).2 hwA))`.

Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hwv`.
-/
private theorem exists_r0_valuation_sub_lt_one_of_isAlgebraic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (hl : A.valuation (l : Ω) < 1) (a : A) (halg : IsAlgebraic ℚ (a : Ω)) :
    ∃ w ∈ R0 A, A.valuation (w - a) < 1 := by
  obtain ⟨q, hq2, hq, haq⟩ := fin_lemma_3 A hl a halg
  set T : Polynomial Ω := Polynomial.X ^ q - Polynomial.X with hT
  have hTm : T.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast (by omega : 1 < q))
  have hprod := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hTm (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits T))).symm
  have hroot : ∀ w ∈ T.roots, w ^ q = w := by
    intro w hw
    have := (Polynomial.mem_roots hTm.ne_zero).1 hw
    simpa [T, sub_eq_zero] using this
  have hev : T.eval (a : Ω) = (T.roots.map fun w => (a : Ω) - w).prod := by
    conv_lhs => rw [hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hv : A.valuation (T.eval (a : Ω)) < 1 := by simpa [T] using haq
  rw [hev, map_multiset_prod, Multiset.map_map] at hv
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ T.roots, A.valuation ((a : Ω) - w) < 1 := by
    by_contra hno
    push_neg at hno
    have h1 : (T.roots.map (A.valuation ∘ fun w => (a : Ω) - w)).prod = 1 := by
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      refine le_antisymm ?_ (hno w hw)
      exact (A.valuation_le_one_iff _).2 (A.sub_mem a.2 (zero_one_mem_gammaSet_one A hq2 (hroot w hw)))
    rw [h1] at hv
    exact lt_irrefl _ hv
  have hwA : w ∈ A := zero_one_mem_gammaSet_one A hq2 (hroot w hw)
  refine ⟨w, ⟨hwA, fun s hs => ?_⟩, ?_⟩
  · have hsq : (s w) ^ q = s w := by rw [← map_pow, hroot w hw]
    change s ∈ Inertia A at hs
    unfold Inertia at hs
    exact eq_of_pow_eq_self_of_valuation_sub_lt_one A hq (zero_one_mem_gammaSet_one A hq2 hsq) hwA hsq (hroot w hw) (hs.2 w ((A.valuation_le_one_iff _).2 hwA))
  · rw [Valuation.map_sub_swap]
    exact hwv

open Polynomial IsLocalRing in
/- English proof (translation)
Introduce `l _ hl2 Ω _ _ _ A hA P hP hdeg`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Establish `hl : A.valuation (l : Ω) < 1`. Take `⟨pl, hpl, hlpl⟩` from `hA`.

Unfold `IsPlaceOver at hpl`. Use `(hpl (l : 𝓞 ℚ)).2 hlpl` as an intermediate fact. Simplify using `using this`. Use `set Pm := P.map (R0 A).subtype with hPm`. Establish `hmon : Pm.Monic` using `hP.map _`.

Establish `hdeg' : Pm.natDegree = P.natDegree` using `Polynomial.natDegree_map_eq_of_injective Subtype.val_injective P`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root Pm (by`. Rewrite using `[Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg']`. Conclude with `hdeg.ne')` after adjusting the coercions. Establish `hcA : ∀ i, Pm.coeff i ∈ A` using `fun i => by`.

Rewrite using `[hPm, Polynomial.coeff_map]`. Conclude with `(P.coeff i).2.1`. Establish `hαA : α ∈ A`. Assume the negation of the conclusion as `hn`. Establish `hv1 : 1 < A.valuation α`.

Rewrite using `[← not_le, A.valuation_le_one_iff]`. Conclude with `hn`. Establish `h0 : Pm.eval α = 0` using `hα`. Rewrite `h0` using `[hmon.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h0`.

Establish `e : α ^ Pm.natDegree = -∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i` using `eq_neg_of_add_eq_zero_left h0`. Establish `hle : A.valuation (∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i) ≤ A.valuation α ^ (Pm.natDegree - 1)`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[map_mul, map_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(A.valuation_le_one_iff _).2 (hcA i)`. Use `_ = A.valuation α ^ i := one_mul _`. Use `_ ≤ A.valuation α ^ (Pm.natDegree - 1) := by`. Apply `pow_le_pow_right₀ hv1.le` to reduce the goal to its premises.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `congrArg A.valuation e` as an intermediate fact. Rewrite `this` using `[Valuation.map_neg, map_pow]`. Rewrite `hle` using `[← this]`.

Establish `hlt : A.valuation α ^ (Pm.natDegree - 1) < A.valuation α ^ Pm.natDegree` using `pow_lt_pow_right₀ hv1 (by omega)`. Conclude with `absurd hle (not_le.2 hlt)`. Take `⟨w, hwR, hwv⟩` from `exists_r0_valuation_sub_lt_one_of_isAlgebraic A hl ⟨α, hαA⟩ (Algebra.IsAlgebraic.isAlgebraic α)`. Use `⟨⟨w, hwR⟩, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`.

Take `⟨u, hu⟩` from `inertia_invariant_valuation_uniformizer_bound l hl2 Ω A hA _ hnot`. Establish `hsub : R0 A ≤ A.toSubring` using `fun x hx => hx.1`. Use `set φ := Subring.inclusion hsub`. Use `set PA := P.map φ`. Establish `hcoe : ∀ y : A.toSubring, ((PA.eval y : A.toSubring) : Ω) = Pm.eval (y : Ω)`.

Introduce `y`. Establish `: Pm = PA.map A.toSubring.subtype`. Rewrite using `[hPm, Polynomial.map_map]`. Both sides reduce to the same expression. Rewrite using `[this, Polynomial.eval_map (p := PA)]`.

Conclude with `(Polynomial.eval₂_hom (p := PA) A.toSubring.subtype y).symm`. Take `⟨c, hc⟩` from `Polynomial.sub_dvd_eval_sub (⟨w, hwR.1⟩ : A.toSubring) ⟨α, hαA⟩ PA`. Establish `hPw : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = (w - α) * (c : Ω)`. Establish `h1 : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = Pm.eval w`. Rewrite using `[hPm, Polynomial.eval_map]`.

Conclude with `(Polynomial.eval₂_hom (R0 A).subtype _).symm`. Establish `h2` using `congrArg (fun z : A.toSubring => (z : Ω)) hc`. Move the coercions through the operations in `[hcoe] at h2`. Rewrite using `[h1, ← sub_zero (Pm.eval w), ← (show Pm.eval α = 0 from hα)]`. Conclude with `h2`.

Establish `hsmall : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) < 1`. Rewrite using `[hPw, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(A.valuation_le_one_iff _).2 c.2`. Use `_ = A.valuation (w - α) := mul_one _`.

Use `_ < 1 := hwv`. Establish `hinv : ((u : R0 A) : Ω) * ((u⁻¹ : (R0 A)ˣ) : R0 A) = 1`. Rewrite using `[← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]`. Establish `hv2` using `congrArg A.valuation hinv`. Rewrite `hv2` using `[map_mul, map_one, hu]`.

Establish `hle1 : A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) ≤ 1` using `(A.valuation_le_one_iff _).2 ((u⁻¹ : (R0 A)ˣ) : R0 A).2.1`. Establish `: A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) * A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' hle1) hsmall`. Rewrite `this` using `[hv2]`. Conclude with `lt_irrefl _ this`.
-/
theorem UpperTheory.Kd.C7.residue_field_teichmuller_lift_exists :
    UpperTheory.Kd.C7.FixedIntegersMonicHasRootModPrime := by
  intro l _ hl2 Ω _ _ _ A hA P hP hdeg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨pl, hpl, hlpl⟩ := hA
    unfold IsPlaceOver at hpl
    have := (hpl (l : 𝓞 ℚ)).2 hlpl
    simpa using this
  set Pm := P.map (R0 A).subtype with hPm
  have hmon : Pm.Monic := hP.map _
  have hdeg' : Pm.natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective Subtype.val_injective P
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root Pm (by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg']
    exact_mod_cast hdeg.ne')
  have hcA : ∀ i, Pm.coeff i ∈ A := fun i => by
    rw [hPm, Polynomial.coeff_map]
    exact (P.coeff i).2.1
  have hαA : α ∈ A := by
    by_contra hn
    have hv1 : 1 < A.valuation α := by
      rw [← not_le, A.valuation_le_one_iff]
      exact hn
    have h0 : Pm.eval α = 0 := hα
    rw [hmon.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum] at h0
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h0
    have e : α ^ Pm.natDegree = -∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i := eq_neg_of_add_eq_zero_left h0
    have hle : A.valuation (∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i) ≤ A.valuation α ^ (Pm.natDegree - 1) := by
      apply Valuation.map_sum_le
      intro i hi
      rw [map_mul, map_pow]
      calc A.valuation (Pm.coeff i) * A.valuation α ^ i ≤ 1 * A.valuation α ^ i := by
            gcongr
            exact (A.valuation_le_one_iff _).2 (hcA i)
        _ = A.valuation α ^ i := one_mul _
        _ ≤ A.valuation α ^ (Pm.natDegree - 1) := by
            apply pow_le_pow_right₀ hv1.le
            have := Finset.mem_range.1 hi
            omega
    have := congrArg A.valuation e
    rw [Valuation.map_neg, map_pow] at this
    rw [← this] at hle
    have hlt : A.valuation α ^ (Pm.natDegree - 1) < A.valuation α ^ Pm.natDegree :=
      pow_lt_pow_right₀ hv1 (by omega)
    exact absurd hle (not_le.2 hlt)
  obtain ⟨w, hwR, hwv⟩ := exists_r0_valuation_sub_lt_one_of_isAlgebraic A hl ⟨α, hαA⟩ (Algebra.IsAlgebraic.isAlgebraic α)
  refine ⟨⟨w, hwR⟩, ?_⟩
  by_contra hnot
  obtain ⟨u, hu⟩ := inertia_invariant_valuation_uniformizer_bound l hl2 Ω A hA _ hnot
  have hsub : R0 A ≤ A.toSubring := fun x hx => hx.1
  set φ := Subring.inclusion hsub
  set PA := P.map φ
  have hcoe : ∀ y : A.toSubring, ((PA.eval y : A.toSubring) : Ω) = Pm.eval (y : Ω) := by
    intro y
    have : Pm = PA.map A.toSubring.subtype := by
      rw [hPm, Polynomial.map_map]
      rfl
    rw [this, Polynomial.eval_map (p := PA)]
    exact (Polynomial.eval₂_hom (p := PA) A.toSubring.subtype y).symm
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (⟨w, hwR.1⟩ : A.toSubring) ⟨α, hαA⟩ PA
  have hPw : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = (w - α) * (c : Ω) := by
    have h1 : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = Pm.eval w := by
      rw [hPm, Polynomial.eval_map]
      exact (Polynomial.eval₂_hom (R0 A).subtype _).symm
    have h2 := congrArg (fun z : A.toSubring => (z : Ω)) hc
    push_cast [hcoe] at h2
    rw [h1, ← sub_zero (Pm.eval w), ← (show Pm.eval α = 0 from hα)]
    exact h2
  have hsmall : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) < 1 := by
    rw [hPw, map_mul]
    calc A.valuation (w - α) * A.valuation (c : Ω) ≤ A.valuation (w - α) * 1 := by
          gcongr
          exact (A.valuation_le_one_iff _).2 c.2
      _ = A.valuation (w - α) := mul_one _
      _ < 1 := hwv
  have hinv : ((u : R0 A) : Ω) * ((u⁻¹ : (R0 A)ˣ) : R0 A) = 1 := by
    rw [← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
  have hv2 := congrArg A.valuation hinv
  rw [map_mul, map_one, hu] at hv2
  have hle1 : A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 ((u⁻¹ : (R0 A)ˣ) : R0 A).2.1
  have : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) * A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' hle1) hsmall
  rw [hv2] at this
  exact lt_irrefl _ this
