import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `key : f.toRatAlgHom = g.toRatAlgHom`. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `x`. Establish `hx` using `IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) x`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Take `⟨n, hn, -, hy1⟩` from `hy`. Rewrite `hn` using `[Set.mem_singleton_iff]`. Rewrite `hy1` using `[hn]`. Conclude with `h y hy1`.

Consider the case `algebraMap c => rw [AlgHom.commutes, AlgHom.commutes]`. Consider the case `add a b _ _ ha hb => rw [map_add, map_add, ha, hb]`. Consider the case `mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]`. Use extensionality with `x`. Conclude with `congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) key`.
-/
private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have key : f.toRatAlgHom = g.toRatAlgHom := by
    apply AlgHom.ext
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, -, hy1⟩ := hy
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hy1
      exact h y hy1
    | algebraMap c => rw [AlgHom.commutes, AlgHom.commutes]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  ext x
  exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) key

/- English proof (translation)
Use `haveI : IsScalarTower ℚ K K' := inferInstance`. Use `haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'`. Establish `h1` using `IsCyclotomicExtension.finrank K' (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M)))`. Establish `h2` using `IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))`. Rewrite using `[IsGalois.card_aut_eq_finrank]`.

Establish `htow` using `Module.finrank_mul_finrank ℚ K K'`. Rewrite `htow` using `[h1, h2, Nat.totient_mul hc, Nat.totient_prime hq]`. Establish `hM : 0 < M.totient` using `Nat.totient_pos.mpr (NeZero.pos M)`. Conclude with `Nat.eq_of_mul_eq_mul_left hM (by rw [htow, mul_comm])`.
-/
private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Nat.card (K' ≃ₐ[K] K') = q - 1 := by
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have h1 := IsCyclotomicExtension.finrank K' (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M)))
  have h2 := IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
  rw [IsGalois.card_aut_eq_finrank]
  have htow := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2, Nat.totient_mul hc, Nat.totient_prime hq] at htow
  have hM : 0 < M.totient := Nat.totient_pos.mpr (NeZero.pos M)
  exact Nat.eq_of_mul_eq_mul_left hM (by rw [htow, mul_comm])

/- English proof (translation)
Introduce `Ω _ _ M q _ _ K K' _ _ _ _ _ _ _ ι' hq hc τ hτ hgen x`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : Fact q.Prime := ⟨hq⟩`. Use `haveI : IsScalarTower ℚ K K' := inferInstance`. Use `haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'`.

Use `haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'`. Use `haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'`. Take `⟨b, hbgen, hb⟩` from `hgen`. Establish `hb' : ∀ y : Ω, y ^ q = 1 → τ y = y ^ (b : ZMod q).val` using `hb`. Establish `hτM : ∀ y : Ω, y ^ M = 1 → τ y = y` using `hτ`.

Establish `hpm : ∀ {R : Type} [Monoid R] (y : R) (N m n : ℕ), y ^ N = 1 → m ≡ n [MOD N] → y ^ m = y ^ n`. Introduce `R _ y N m n hy h`. Rewrite using `[← Nat.mod_add_div m N, ← Nat.mod_add_div n N, show m % N = n % N from h, pow_add, pow_add, pow_mul, pow_mul, hy, one_pow, one_pow]`. Take `⟨A, hA1, hA0⟩ : ∃ A, A ≡ 1 [MOD q] ∧ A ≡ 0 [MOD M]` from `⟨(Nat.chineseRemainder hc 1 0).1, (Nat.chineseRemainder hc 1 0).2.1, (Nat.chineseRemainder hc 1 0).2.2⟩`. Take `⟨B, hB0, hB1⟩ : ∃ B, B ≡ 0 [MOD q] ∧ B ≡ 1 [MOD M]` from `⟨(Nat.chineseRemainder hc 0 1).1, (Nat.chineseRemainder hc 0 1).2.1, (Nat.chineseRemainder hc 0 1).2.2⟩`.

Take `⟨e, he⟩ : ∃ e, e = A * (b : ZMod q).val + B` from `⟨_, rfl⟩`. Establish `he_q : e ≡ (b : ZMod q).val [MOD q]`. Establish `h` using `(hA1.mul_right (b : ZMod q).val).add hB0`. Rewrite `h` using `[one_mul, add_zero, ← he]`. Then use the resulting hypothesis. Establish `he_M : e ≡ 1 [MOD M]`.

Establish `h` using `(hA0.mul_right (b : ZMod q).val).add hB1`. Rewrite `h` using `[zero_mul, zero_add, ← he]`. Then use the resulting hypothesis. Establish `hτe : ∀ y : Ω, y ^ (q * M) = 1 → τ y = y ^ e`. Introduce `y hy`. Establish `hAB : A + B ≡ 1 [MOD q * M]` using `(Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨by simpa using hA1.add hB0, by simpa using hA0.add hB1⟩`.

Take `⟨cA, hcA⟩` from `(Nat.modEq_zero_iff_dvd.mp hA0)`. Take `⟨cB, hcB⟩` from `(Nat.modEq_zero_iff_dvd.mp hB0)`. Establish `hyA : (y ^ A) ^ q = 1`. Rewrite using `[← pow_mul, show A * q = q * M * cA by rw [hcA]; ring, pow_mul, hy, one_pow]`. Establish `hyB : (y ^ B) ^ M = 1`.

Rewrite using `[← pow_mul, show B * M = q * M * cB by rw [hcB]; ring, pow_mul, hy, one_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hζ` using `IsCyclotomicExtension.zeta_spec (q * M) ℚ K'`. Establish `he_cop : e.Coprime (q * M)`. Apply `Nat.Coprime.mul_right` to reduce the goal to its premises.

Conclude with `he_q.gcd_eq.trans (ZMod.val_coe_unit_coprime b)`. Conclude with `he_M.gcd_eq.trans (Nat.gcd_one_left M)`. Establish `hμ` using `hζ.pow_of_coprime e he_cop`. Establish `hirr` using `Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M))`. Establish `hσ0ζ` using `IsCyclotomicExtension.fromZetaAut_spec hμ hirr`.

Establish `hσ0 : ∀ z : K', z ^ (q * M) = 1 → IsCyclotomicExtension.fromZetaAut hμ hirr z = z ^ e`. Introduce `z hz`. Take `⟨j, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hz`. Rewrite using `[map_pow, hσ0ζ, ← pow_mul, ← pow_mul, mul_comm e j]`. Establish `hσ0K : ∀ y : K, IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y`.

Establish `h` using `cyc_hom_ext M ((IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv.toRingHom.comp (algebraMap K K')) (algebraMap K K') (fun y hy => by show IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y`. Establish `h1 : (algebraMap K K' y) ^ M = 1` using `by rw [← map_pow, hy, map_one]`. Rewrite using `[hσ0 _ (by rw [mul_comm, pow_mul, h1, one_pow]), hpm _ M e 1 h1 he_M, pow_one])`. Conclude with `fun y => RingHom.congr_fun h y`. Set `σ1 : K' ≃ₐ[K] K'` to `AlgEquiv.ofRingEquiv (f := (IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv) hσ0K`.

Establish `hσ1 : ∀ z : K', z ^ (q * M) = 1 → σ1 z = z ^ e` using `fun z hz => hσ0 z hz`. Establish `hcomm : ∀ z : K', τ (ι' z) = ι' (σ1 z)`. Establish `h` using `cyc_hom_ext (q * M) ((τ : Ω ≃ₐ[ℚ] Ω).toRingEquiv.toRingHom.comp ι') (ι'.comp σ1.toRingEquiv.toRingHom) (fun z hz => by show τ (ι' z) = ι' (σ1 z)`. Rewrite using `[hσ1 z hz, map_pow, hτe _ (by rw [← map_pow, hz, map_one])])`. Conclude with `fun z => RingHom.congr_fun h z`.

Establish `hcommi : ∀ i : ℕ, ∀ z : K', (τ ^ i) (ι' z) = ι' ((σ1 ^ i) z)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro z`. Rewrite using `[pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]`.

Consider the case `succ i ih => intro z`. Rewrite using `[pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, ih]`. Establish `hζq : IsPrimitiveRoot (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) q`. Establish `h` using `hζ.pow_of_dvd (NeZero.ne M) (dvd_mul_left M q)`. Rewrite `h` using `[Nat.mul_div_cancel q (NeZero.pos M)]`. Then use the resulting hypothesis.

Establish `hζq1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (q * M) = 1`. Rewrite using `[pow_mul, hζq.pow_eq_one, one_pow]`. Establish `hσpow : ∀ i : ℕ, (σ1 ^ i) (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]`. Consider the case `succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσ1 _ hζq1, map_pow, ih, ← pow_mul, pow_succ]`. Establish `horder : orderOf b = q - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hbgen, Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `hinj : ∀ i ∈ Finset.range (q - 1), ∀ j ∈ Finset.range (q - 1), σ1 ^ i = σ1 ^ j → i = j`.

Introduce `i hi j hj hij`. Establish `h1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ j)`. Rewrite using `[← hσpow, ← hσpow, hij]`. Rewrite `h1` using `[hpm _ q (e ^ i) (e ^ i % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm, hpm _ q (e ^ j) (e ^ j % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm]`. Establish `h2 : e ^ i ≡ e ^ j [MOD q]` using `hζq.pow_inj (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos) h1`.

Establish `h3 : ((e : ZMod q)) = (b : ZMod q)`. Rewrite using `[(ZMod.natCast_eq_natCast_iff _ _ _).mpr he_q, ZMod.natCast_zmod_val]`. Establish `h4 : (b : ZMod q) ^ i = (b : ZMod q) ^ j`. Rewrite using `[← h3, ← Nat.cast_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2]`. Establish `h5 : b ^ i = b ^ j` using `Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h4])`.

Establish `h6` using `pow_eq_pow_iff_modEq.mp h5`. Rewrite `h6` using `[horder]`. Establish `h7 : i % (q - 1) = j % (q - 1)` using `h6`. Rewrite `h7` using `[Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]`. Then use the resulting hypothesis. Establish `himg : (Finset.range (q - 1)).image (fun i => σ1 ^ i) = Finset.univ`.

Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range, ← Nat.card_eq_fintype_card, card_gal M q K K' hq hc]`. Use `show ∏ i ∈ Finset.range (q - 1), (τ ^ i) (ι' x) = _`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, map_prod, ← himg, Finset.prod_image (fun i hi j hj h => hinj i hi j hj h)]`. Conclude with `Finset.prod_congr rfl (fun i _ => hcommi i x)`.
-/
theorem UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (ι' : K' →+* Ω), q.Prime → q.Coprime M → ∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ x : K', nrm q τ (ι' x) = ι' (algebraMap K K' (Algebra.norm K x)) := by
  intro Ω _ _ M q _ _ K K' _ _ _ _ _ _ _ ι' hq hc τ hτ hgen x
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  obtain ⟨b, hbgen, hb⟩ := hgen
  have hb' : ∀ y : Ω, y ^ q = 1 → τ y = y ^ (b : ZMod q).val := hb
  have hτM : ∀ y : Ω, y ^ M = 1 → τ y = y := hτ
  have hpm : ∀ {R : Type} [Monoid R] (y : R) (N m n : ℕ), y ^ N = 1 → m ≡ n [MOD N] → y ^ m = y ^ n := by
    intro R _ y N m n hy h
    rw [← Nat.mod_add_div m N, ← Nat.mod_add_div n N, show m % N = n % N from h, pow_add, pow_add,
      pow_mul, pow_mul, hy, one_pow, one_pow]
  obtain ⟨A, hA1, hA0⟩ : ∃ A, A ≡ 1 [MOD q] ∧ A ≡ 0 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 1 0).1, (Nat.chineseRemainder hc 1 0).2.1, (Nat.chineseRemainder hc 1 0).2.2⟩
  obtain ⟨B, hB0, hB1⟩ : ∃ B, B ≡ 0 [MOD q] ∧ B ≡ 1 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 0 1).1, (Nat.chineseRemainder hc 0 1).2.1, (Nat.chineseRemainder hc 0 1).2.2⟩
  obtain ⟨e, he⟩ : ∃ e, e = A * (b : ZMod q).val + B := ⟨_, rfl⟩
  have he_q : e ≡ (b : ZMod q).val [MOD q] := by
    have h := (hA1.mul_right (b : ZMod q).val).add hB0
    rwa [one_mul, add_zero, ← he] at h
  have he_M : e ≡ 1 [MOD M] := by
    have h := (hA0.mul_right (b : ZMod q).val).add hB1
    rwa [zero_mul, zero_add, ← he] at h
  have hτe : ∀ y : Ω, y ^ (q * M) = 1 → τ y = y ^ e := by
    intro y hy
    have hAB : A + B ≡ 1 [MOD q * M] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨by simpa using hA1.add hB0, by simpa using hA0.add hB1⟩
    obtain ⟨cA, hcA⟩ := (Nat.modEq_zero_iff_dvd.mp hA0)
    obtain ⟨cB, hcB⟩ := (Nat.modEq_zero_iff_dvd.mp hB0)
    have hyA : (y ^ A) ^ q = 1 := by
      rw [← pow_mul, show A * q = q * M * cA by rw [hcA]; ring, pow_mul, hy, one_pow]
    have hyB : (y ^ B) ^ M = 1 := by
      rw [← pow_mul, show B * M = q * M * cB by rw [hcB]; ring, pow_mul, hy, one_pow]
    calc τ y = τ (y ^ A * y ^ B) := by rw [← pow_add, hpm y (q * M) (A + B) 1 hy hAB, pow_one]
      _ = (y ^ A) ^ (b : ZMod q).val * y ^ B := by rw [map_mul, hb' _ hyA, hτM _ hyB]
      _ = y ^ e := by rw [he, ← pow_mul, ← pow_add]
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  have he_cop : e.Coprime (q * M) := by
    apply Nat.Coprime.mul_right
    · exact he_q.gcd_eq.trans (ZMod.val_coe_unit_coprime b)
    · exact he_M.gcd_eq.trans (Nat.gcd_one_left M)
  have hμ := hζ.pow_of_coprime e he_cop
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M))
  have hσ0ζ := IsCyclotomicExtension.fromZetaAut_spec hμ hirr
  have hσ0 : ∀ z : K', z ^ (q * M) = 1 → IsCyclotomicExtension.fromZetaAut hμ hirr z = z ^ e := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, hσ0ζ, ← pow_mul, ← pow_mul, mul_comm e j]
  have hσ0K : ∀ y : K, IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y := by
    have h := cyc_hom_ext M ((IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv.toRingHom.comp (algebraMap K K'))
      (algebraMap K K') (fun y hy => by
        show IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y
        have h1 : (algebraMap K K' y) ^ M = 1 := by rw [← map_pow, hy, map_one]
        rw [hσ0 _ (by rw [mul_comm, pow_mul, h1, one_pow]), hpm _ M e 1 h1 he_M, pow_one])
    exact fun y => RingHom.congr_fun h y
  let σ1 : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := (IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv) hσ0K
  have hσ1 : ∀ z : K', z ^ (q * M) = 1 → σ1 z = z ^ e := fun z hz => hσ0 z hz
  have hcomm : ∀ z : K', τ (ι' z) = ι' (σ1 z) := by
    have h := cyc_hom_ext (q * M) ((τ : Ω ≃ₐ[ℚ] Ω).toRingEquiv.toRingHom.comp ι') (ι'.comp σ1.toRingEquiv.toRingHom)
      (fun z hz => by
        show τ (ι' z) = ι' (σ1 z)
        rw [hσ1 z hz, map_pow, hτe _ (by rw [← map_pow, hz, map_one])])
    exact fun z => RingHom.congr_fun h z
  have hcommi : ∀ i : ℕ, ∀ z : K', (τ ^ i) (ι' z) = ι' ((σ1 ^ i) z) := by
    intro i
    induction i with
    | zero => intro z; rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
    | succ i ih => intro z; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, ih]
  have hζq : IsPrimitiveRoot (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) q := by
    have h := hζ.pow_of_dvd (NeZero.ne M) (dvd_mul_left M q)
    rwa [Nat.mul_div_cancel q (NeZero.pos M)] at h
  have hζq1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (q * M) = 1 := by
    rw [pow_mul, hζq.pow_eq_one, one_pow]
  have hσpow : ∀ i : ℕ, (σ1 ^ i) (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M)
      = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσ1 _ hζq1, map_pow, ih, ← pow_mul, pow_succ]
  have horder : orderOf b = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hbgen, Nat.card_eq_fintype_card, ZMod.card_units]
  have hinj : ∀ i ∈ Finset.range (q - 1), ∀ j ∈ Finset.range (q - 1), σ1 ^ i = σ1 ^ j → i = j := by
    intro i hi j hj hij
    have h1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ j) := by
      rw [← hσpow, ← hσpow, hij]
    rw [hpm _ q (e ^ i) (e ^ i % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm,
      hpm _ q (e ^ j) (e ^ j % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm] at h1
    have h2 : e ^ i ≡ e ^ j [MOD q] := hζq.pow_inj (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos) h1
    have h3 : ((e : ZMod q)) = (b : ZMod q) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr he_q, ZMod.natCast_zmod_val]
    have h4 : (b : ZMod q) ^ i = (b : ZMod q) ^ j := by
      rw [← h3, ← Nat.cast_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2]
    have h5 : b ^ i = b ^ j := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h4])
    have h6 := pow_eq_pow_iff_modEq.mp h5
    rw [horder] at h6
    have h7 : i % (q - 1) = j % (q - 1) := h6
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h7
  have himg : (Finset.range (q - 1)).image (fun i => σ1 ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range,
      ← Nat.card_eq_fintype_card, card_gal M q K K' hq hc]
  show ∏ i ∈ Finset.range (q - 1), (τ ^ i) (ι' x) = _
  rw [Algebra.norm_eq_prod_automorphisms, map_prod, ← himg, Finset.prod_image (fun i hi j hj h => hinj i hi j hj h)]
  exact Finset.prod_congr rfl (fun i _ => hcommi i x)
