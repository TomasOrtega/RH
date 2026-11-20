import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.DecComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ (fun P hP hirr => ?_)` and prove the remaining obligations. Establish `hl : P ∈ Polynomial.lifts (IsLocalRing.residue A)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `IsLocalRing.residue_surjective (P.coeff n)`.

Take `⟨Q, hQ, hdeg, hQm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl hP`. Establish `hQdeg : (Q.map (algebraMap A Ω)).degree ≠ 0`. Rewrite using `[Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A Ω), hdeg]`. Conclude with `(Polynomial.degree_pos_of_irreducible hirr).ne'`. Take `⟨r, hr⟩` from `IsAlgClosed.exists_root (Q.map (algebraMap A Ω)) hQdeg`.

Establish `hint : IsIntegral A r` using `⟨Q, hQm, by rw [← Polynomial.eval_map]; exact hr⟩`. Take `⟨a, rfl⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Use `⟨IsLocalRing.residue A a, ?_⟩` and prove the remaining obligations. Establish `h0 : Q.eval a = 0`. Apply `IsFractionRing.injective A Ω` to reduce the goal to its premises.

Rewrite using `[map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]`. Conclude with `hr`. Rewrite using `[← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, h0, map_zero]`.
-/
private theorem isAlgClosed_residueField_valuationSubring {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun P hP hirr => ?_)
  have hl : P ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact IsLocalRing.residue_surjective (P.coeff n)
  obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hP
  have hQdeg : (Q.map (algebraMap A Ω)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A Ω), hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Q.map (algebraMap A Ω)) hQdeg
  have hint : IsIntegral A r := ⟨Q, hQm, by rw [← Polynomial.eval_map]; exact hr⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have h0 : Q.eval a = 0 := by
    apply IsFractionRing.injective A Ω
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hr
  rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, h0, map_zero]

/- English proof (translation)
Introduce `c`. Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ c ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hy]`.
-/
private theorem pow_prime_pow_mul_eq_self_of_pow_eq_self {K : Type} [Field K] (p m : ℕ) (y : K) (hy : y ^ (p ^ m) = y) :
    ∀ c : ℕ, y ^ (p ^ (m * c)) = y := by
  intro c
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hy]

/- English proof (translation)
Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Establish `hp1 : 1 < p` using `(Fact.out : p.Prime).one_lt`. Establish `hN : m * n ≠ 0` using `Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hn)`. Use `letI : Fintype (GaloisField p (m * n)) := Fintype.ofFinite _`. Set `φ : GaloisField p (m * n) →ₐ[ZMod p] k` to `IsAlgClosed.lift`.

Establish `hφinj : Function.Injective φ` using `φ.toRingHom.injective`. Establish `hcardL : Fintype.card (GaloisField p (m * n)) = p ^ (m * n)`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `GaloisField.card p (m * n) hN`. Establish `hpN : 1 < p ^ (m * n)` using `Nat.one_lt_pow hN hp1`.

Establish `hroot : ∀ z : k, z ^ (p ^ (m * n)) = z → ∃ x, φ x = z`. Introduce `z hz`. Establish `hP0 : (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k) ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero k hpN`. Establish `hmem : ∀ w : k, w ^ (p ^ (m * n)) = w → w ∈ (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.toFinset`. Introduce `w hw`.

Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hP0]`. Simplify using `[hw]`. Establish `hTsub : Finset.univ.image φ ⊆ (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.toFinset`. Introduce `w hw`. Take `⟨x, _, rfl⟩` from `Finset.mem_image.1 hw`.

Apply `hmem` to reduce the goal to its premises. Rewrite using `[← map_pow, ← hcardL, FiniteField.pow_card]`. Establish `hTcard : (Finset.univ.image φ).card = p ^ (m * n)`. Rewrite using `[Finset.card_image_of_injective _ hφinj, Finset.card_univ, hcardL]`. Establish `hle : (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.toFinset.card ≤ (Finset.univ.image φ).card`.

Rewrite using `[hTcard]`. Combine the equalities or inequalities in the displayed calculation. Establish `hEq` using `Finset.eq_of_subset_of_card_le hTsub hle`. Establish `hz' : z ∈ Finset.univ.image φ` using `hEq ▸ hmem z hz`. Take `⟨x, _, hx⟩` from `Finset.mem_image.1 hz'`.

Conclude with `⟨x, hx⟩`. Establish `hstab : ∀ x, ∃ x', φ x' = σ (φ x)`. Introduce `x`. Apply `hroot` to reduce the goal to its premises. Rewrite using `[← map_pow, ← map_pow, ← hcardL, FiniteField.pow_card]`.

Use `choose τf hτf using hstab`. Establish `hσalg : ∀ r : ZMod p, σ (algebraMap (ZMod p) k r) = algebraMap (ZMod p) k r`. Introduce `r`. Take `⟨t, rfl⟩` from `ZMod.natCast_zmod_surjective r`. Simplify using `only [map_natCast]`.

Set `τ : GaloisField p (m * n) →ₐ[ZMod p] GaloisField p (m * n)` to `{ toFun := τf map_one' := hφinj (by simp [hτf]) map_mul' := fun a b => hφinj (by simp [hτf]) map_zero' := hφinj (by simp [hτf]) map_add' := fun a b => hφinj (by simp [hτf]) commutes' := fun r => hφinj (by simp [hτf, hσalg]) }`. Establish `hτ : ∀ x, φ (τ x) = σ (φ x)` using `hτf`. Establish `hiter : ∀ j x, φ ((τ^[j]) x) = (σ^[j]) (φ x)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ j ih => intro x`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]`. Establish `hτn : τ ^ n = 1`.

Use extensionality with `x`. Rewrite using `[AlgHom.coe_pow, AlgHom.one_apply]`. Apply `hφinj` to reduce the goal to its premises. Rewrite using `[hiter, hσ]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : ℕ, FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p (m * n)) ^ a = τ := by`.

Take `⟨a, ha⟩` from `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p (m * n))).2 τ`. Conclude with `⟨a.1, ha⟩`. Establish `hfr : (FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p (m * n))) ^ (a * n) = 1`. Rewrite using `[pow_mul, ha, hτn]`. Establish `hdvd : m * n ∣ a * n`.

Use `orderOf_dvd_of_pow_eq_one hfr` as an intermediate fact. Rewrite `this` using `[FiniteField.orderOf_frobeniusAlgHom, GaloisField.finrank p hN]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `Nat.dvd_of_mul_dvd_mul_right hn hdvd`. Establish `hyN : y ^ (p ^ (m * n)) = y` using `pow_prime_pow_mul_eq_self_of_pow_eq_self p m y hy n`. Take `⟨x0, rfl⟩` from `hroot y hyN`.

Rewrite using `[← hτ, ← ha, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card, map_pow, hc]`. Conclude with `pow_prime_pow_mul_eq_self_of_pow_eq_self p m _ hy c`.
-/
private theorem frobenius_fixed_of_iterate_fixed_pow_prime {k : Type} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (σ : k →+* k) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hσ : ∀ z, (σ^[n]) z = z) (y : k) (hy : y ^ (p ^ m) = y) : σ y = y := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hN : m * n ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.mul_pos hm hn)
  letI : Fintype (GaloisField p (m * n)) := Fintype.ofFinite _
  let φ : GaloisField p (m * n) →ₐ[ZMod p] k := IsAlgClosed.lift
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hcardL : Fintype.card (GaloisField p (m * n)) = p ^ (m * n) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p (m * n) hN
  have hpN : 1 < p ^ (m * n) := Nat.one_lt_pow hN hp1
  have hroot : ∀ z : k, z ^ (p ^ (m * n)) = z → ∃ x, φ x = z := by
    intro z hz
    classical
    have hP0 : (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k hpN
    have hmem : ∀ w : k, w ^ (p ^ (m * n)) = w →
        w ∈ (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.toFinset := by
      intro w hw
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
      simp [hw]
    have hTsub : Finset.univ.image φ ⊆
        (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.toFinset := by
      intro w hw
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hw
      apply hmem
      rw [← map_pow, ← hcardL, FiniteField.pow_card]
    have hTcard : (Finset.univ.image φ).card = p ^ (m * n) := by
      rw [Finset.card_image_of_injective _ hφinj, Finset.card_univ, hcardL]
    have hle : (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.toFinset.card ≤
        (Finset.univ.image φ).card := by
      rw [hTcard]
      calc _ ≤ (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).roots.card :=
            Multiset.toFinset_card_le _
        _ ≤ (Polynomial.X ^ (p ^ (m * n)) - Polynomial.X : Polynomial k).natDegree :=
            Polynomial.card_roots' _
        _ = p ^ (m * n) := FiniteField.X_pow_card_sub_X_natDegree_eq k hpN
    have hEq := Finset.eq_of_subset_of_card_le hTsub hle
    have hz' : z ∈ Finset.univ.image φ := hEq ▸ hmem z hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.1 hz'
    exact ⟨x, hx⟩
  have hstab : ∀ x, ∃ x', φ x' = σ (φ x) := by
    intro x
    apply hroot
    rw [← map_pow, ← map_pow, ← hcardL, FiniteField.pow_card]
  choose τf hτf using hstab
  have hσalg : ∀ r : ZMod p, σ (algebraMap (ZMod p) k r) = algebraMap (ZMod p) k r := by
    intro r
    obtain ⟨t, rfl⟩ := ZMod.natCast_zmod_surjective r
    simp only [map_natCast]
  let τ : GaloisField p (m * n) →ₐ[ZMod p] GaloisField p (m * n) :=
    { toFun := τf
      map_one' := hφinj (by simp [hτf])
      map_mul' := fun a b => hφinj (by simp [hτf])
      map_zero' := hφinj (by simp [hτf])
      map_add' := fun a b => hφinj (by simp [hτf])
      commutes' := fun r => hφinj (by simp [hτf, hσalg]) }
  have hτ : ∀ x, φ (τ x) = σ (φ x) := hτf
  have hiter : ∀ j x, φ ((τ^[j]) x) = (σ^[j]) (φ x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  have hτn : τ ^ n = 1 := by
    ext x
    rw [AlgHom.coe_pow, AlgHom.one_apply]
    apply hφinj
    rw [hiter, hσ]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p (m * n)) ^ a = τ := by
    obtain ⟨a, ha⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p (m * n))).2 τ
    exact ⟨a.1, ha⟩
  have hfr : (FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p (m * n))) ^ (a * n) = 1 := by
    rw [pow_mul, ha, hτn]
  have hdvd : m * n ∣ a * n := by
    have := orderOf_dvd_of_pow_eq_one hfr
    rwa [FiniteField.orderOf_frobeniusAlgHom, GaloisField.finrank p hN] at this
  obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_right hn hdvd
  have hyN : y ^ (p ^ (m * n)) = y := pow_prime_pow_mul_eq_self_of_pow_eq_self p m y hy n
  obtain ⟨x0, rfl⟩ := hroot y hyN
  rw [← hτ, ← ha, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card, map_pow, hc]
  exact pow_prime_pow_mul_eq_self_of_pow_eq_self p m _ hy c

/- English proof (translation)
Rewrite using `[CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]`. Rewrite using `[← map_natCast (IsLocalRing.residue A) p, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Simplify using `using hp`.
-/
private theorem charP_residueField_of_valuation_lt_one {Ω : Type} [Field Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) : CharP (IsLocalRing.ResidueField A) p := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
  rw [← map_natCast (IsLocalRing.residue A) p, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  simpa using hp

/- English proof (translation)
Use `haveI := charP_residueField_of_valuation_lt_one p A hp`. Establish `hpr : p.Prime` using `Fact.out`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω`.

Establish `hxQ : IsAlgebraic ℚ (x : Ω)` using `Algebra.IsAlgebraic.isAlgebraic _`. Establish `hxZ : IsAlgebraic ℤ (x : Ω)` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hxQ`. Take `⟨P, hP0, hPx⟩` from `hxZ`. Use `set Q := P.primPart with hQ`. Establish `hQx : Q.eval₂ (Int.castRingHom Ω) (x : Ω) = 0`.

Establish `hc : (P.content : Ω) ≠ 0`. Rewrite using `[Int.cast_ne_zero]`. Conclude with `fun h => hP0 (Polynomial.content_eq_zero_iff.1 h)`. Establish `h1 : P.eval₂ (Int.castRingHom Ω) (x : Ω) = 0`. Rewrite `hPx` using `[Polynomial.aeval_def]`.

Rewrite using `[← hPx]`. Use `congr 1`. Rewrite `h1` using `[Polynomial.eq_C_content_mul_primPart P, Polynomial.eval₂_mul, Polynomial.eval₂_C]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (by simpa using hc)`. Establish `hQA : Q.eval₂ (Int.castRingHom A) x = 0`.

Apply `Subtype.val_injective` to reduce the goal to its premises. Use `Polynomial.hom_eval₂ Q (Int.castRingHom A) A.subtype x` as an intermediate fact. Rewrite `this` using `[show A.subtype.comp (Int.castRingHom A) = Int.castRingHom Ω from Subsingleton.elim _ _]`. Simplify using `only [ValuationSubring.coe_subtype] at this`. Rewrite using `[this]`.

Simplify using `using hQx`. Use `set r := IsLocalRing.residue A x with hr`. Establish `hQr : Q.eval₂ (Int.castRingHom (IsLocalRing.ResidueField A)) r = 0`. Use `Polynomial.hom_eval₂ Q (Int.castRingHom A) (IsLocalRing.residue A) x` as an intermediate fact. Rewrite `this` using `[show (IsLocalRing.residue A).comp (Int.castRingHom A) = Int.castRingHom (IsLocalRing.ResidueField A) from Subsingleton.elim _ _]`.

Rewrite using `[← this, hQA, map_zero]`. Establish `hQk : Q.map (Int.castRingHom (IsLocalRing.ResidueField A)) ≠ 0`. Introduce `h0`. Establish `hdvd : Polynomial.C (p : ℤ) ∣ Q`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`.

Introduce `i`. Use `congrArg (fun f => Polynomial.coeff f i) h0` as an intermediate fact. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this`. Conclude with `(CharP.intCast_eq_zero_iff (IsLocalRing.ResidueField A) p _).1 this`. Establish `hu` using `Polynomial.isPrimitive_primPart P (p : ℤ) hdvd`.

Rewrite `hu` using `[Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]`. Conclude with `hpr.one_lt.ne' hu`. Establish `hfrob : ∀ s : IsLocalRing.ResidueField A, Q.eval₂ (Int.castRingHom (IsLocalRing.ResidueField A)) s = 0 → Q.eval₂ (Int.castRingHom (IsLocalRing.ResidueField A)) (s ^ p) = 0`. Introduce `s hs`. Use `Polynomial.hom_eval₂ Q (Int.castRingHom (IsLocalRing.ResidueField A)) (frobenius (IsLocalRing.ResidueField A) p) s` as an intermediate fact.

Rewrite `this` using `[show (frobenius (IsLocalRing.ResidueField A) p).comp (Int.castRingHom (IsLocalRing.ResidueField A)) = Int.castRingHom (IsLocalRing.ResidueField A) from Subsingleton.elim _ _, hs, map_zero, frobenius_def]`. Conclude with `this.symm`. Establish `hall : ∀ j : ℕ, r ^ (p ^ j) ∈ {s | (Q.map (Int.castRingHom (IsLocalRing.ResidueField A))).IsRoot s}`. Introduce `j`. Simplify using `only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_map]`.

Proceed by induction on `j with`. Consider the case `zero => simpa using hQr`. Consider the case `succ j ih`. Rewrite using `[pow_succ, pow_mul]`. Conclude with `hfrob _ ih`.

Take `⟨i, j, hij, heq⟩` from `Set.Finite.exists_lt_map_eq_of_forall_mem hall (Polynomial.finite_setOf_isRoot hQk)`. Use `⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩` and prove the remaining obligations. Apply `(iterateFrobenius (IsLocalRing.ResidueField A) p i).injective` to reduce the goal to its premises. Simplify using `only [iterateFrobenius_def]`. Rewrite using `[← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]`.

Conclude with `heq.symm`.
-/
private theorem exists_residue_pow_prime_pow_eq_self {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) (x : A) : ∃ m, 0 < m ∧ (IsLocalRing.residue A x) ^ (p ^ m) = IsLocalRing.residue A x := by
  haveI := charP_residueField_of_valuation_lt_one p A hp
  have hpr : p.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have hxQ : IsAlgebraic ℚ (x : Ω) := Algebra.IsAlgebraic.isAlgebraic _
  have hxZ : IsAlgebraic ℤ (x : Ω) := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hxQ
  obtain ⟨P, hP0, hPx⟩ := hxZ
  set Q := P.primPart with hQ
  have hQx : Q.eval₂ (Int.castRingHom Ω) (x : Ω) = 0 := by
    have hc : (P.content : Ω) ≠ 0 := by
      rw [Int.cast_ne_zero]
      exact fun h => hP0 (Polynomial.content_eq_zero_iff.1 h)
    have h1 : P.eval₂ (Int.castRingHom Ω) (x : Ω) = 0 := by
      rw [Polynomial.aeval_def] at hPx
      rw [← hPx]
      congr 1
    rw [Polynomial.eq_C_content_mul_primPart P, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by simpa using hc)
  have hQA : Q.eval₂ (Int.castRingHom A) x = 0 := by
    apply Subtype.val_injective
    have := Polynomial.hom_eval₂ Q (Int.castRingHom A) A.subtype x
    rw [show A.subtype.comp (Int.castRingHom A) = Int.castRingHom Ω from Subsingleton.elim _ _] at this
    simp only [ValuationSubring.coe_subtype] at this
    rw [this]
    simpa using hQx
  set r := IsLocalRing.residue A x with hr
  have hQr : Q.eval₂ (Int.castRingHom (IsLocalRing.ResidueField A)) r = 0 := by
    have := Polynomial.hom_eval₂ Q (Int.castRingHom A) (IsLocalRing.residue A) x
    rw [show (IsLocalRing.residue A).comp (Int.castRingHom A) = Int.castRingHom (IsLocalRing.ResidueField A) from Subsingleton.elim _ _] at this
    rw [← this, hQA, map_zero]
  have hQk : Q.map (Int.castRingHom (IsLocalRing.ResidueField A)) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun f => Polynomial.coeff f i) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (CharP.intCast_eq_zero_iff (IsLocalRing.ResidueField A) p _).1 this
    have hu := Polynomial.isPrimitive_primPart P (p : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact hpr.one_lt.ne' hu
  have hfrob : ∀ s : IsLocalRing.ResidueField A, Q.eval₂ (Int.castRingHom (IsLocalRing.ResidueField A)) s = 0 → Q.eval₂ (Int.castRingHom (IsLocalRing.ResidueField A)) (s ^ p) = 0 := by
    intro s hs
    have := Polynomial.hom_eval₂ Q (Int.castRingHom (IsLocalRing.ResidueField A)) (frobenius (IsLocalRing.ResidueField A) p) s
    rw [show (frobenius (IsLocalRing.ResidueField A) p).comp (Int.castRingHom (IsLocalRing.ResidueField A)) = Int.castRingHom (IsLocalRing.ResidueField A) from Subsingleton.elim _ _, hs, map_zero, frobenius_def] at this
    exact this.symm
  have hall : ∀ j : ℕ, r ^ (p ^ j) ∈ {s | (Q.map (Int.castRingHom (IsLocalRing.ResidueField A))).IsRoot s} := by
    intro j
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_map]
    induction j with
    | zero => simpa using hQr
    | succ j ih =>
      rw [pow_succ, pow_mul]
      exact hfrob _ ih
  obtain ⟨i, j, hij, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem hall (Polynomial.finite_setOf_isRoot hQk)
  refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
  apply (iterateFrobenius (IsLocalRing.ResidueField A) p i).injective
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  exact heq.symm

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ p _ A hp g hg n hn hgn`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI := isAlgClosed_residueField_valuationSubring A`. Use `haveI := charP_residueField_of_valuation_lt_one p A hp`. Establish `hgD : g ∈ A.decompositionSubgroup F` using `hg`.

Set `g' : A.decompositionSubgroup F` to `⟨g, hgD⟩`. Establish `key : ∀ (h : A.decompositionSubgroup F) (a : A), h • IsLocalRing.residue A a = IsLocalRing.residue A a ↔ A.valuation ((h : G F Ω) (a : Ω) - a) < 1`. Introduce `h a`. Rewrite using `[← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Both sides reduce to the same expression.

Set `σ : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A` to `MulSemiringAction.toRingHom (A.decompositionSubgroup F) _ g'`. Establish `hσ : ∀ z, (σ^[n]) z = z`. Introduce `z`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective z`. Establish `hit : ∀ k z, (σ^[k]) z = (g' ^ k) • z`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `z`. Rewrite using `[Function.iterate_succ_apply', ih, pow_succ', mul_smul]`. Both sides reduce to the same expression. Rewrite using `[hit, key]`. Establish `hI` using `hgn`.

Simplify using `only [Ine] at hI`. Establish `h2` using `hI.2 a (A.valuation_le_one a)`. Simplify `h2` using `[g']`. Establish `hfix : ∀ a : A, σ (IsLocalRing.residue A a) = IsLocalRing.residue A a`. Introduce `a`.

Take `⟨m, hm, hy⟩` from `exists_residue_pow_prime_pow_eq_self (F := F) p A hp a`. Conclude with `frobenius_fixed_of_iterate_fixed_pow_prime p σ n m hn hm hσ _ hy`. Use `show g ∈ Inertia (F := F) A`. Use `⟨hgD, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxA : x ∈ A` using `(A.valuation_le_one_iff x).1 hx`.

Use `(key g' ⟨x, hxA⟩).1 (hfix ⟨x, hxA⟩)` as an intermediate fact. Simplify `this` using `[g']`.
-/
theorem UpperTheory.V.Ws.Rq.powIne :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω),
      A.valuation (p : Ω) < 1 → ∀ g ∈ Dec (F := F) A, ∀ n : ℕ, 0 < n → g ^ n ∈ Ine (F := F) A → g ∈ Ine (F := F) A := by
  intro F Ω _ _ _ _ _ p _ A hp g hg n hn hgn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI := isAlgClosed_residueField_valuationSubring A
  haveI := charP_residueField_of_valuation_lt_one p A hp
  have hgD : g ∈ A.decompositionSubgroup F := hg
  let g' : A.decompositionSubgroup F := ⟨g, hgD⟩
  have key : ∀ (h : A.decompositionSubgroup F) (a : A),
      h • IsLocalRing.residue A a = IsLocalRing.residue A a ↔
        A.valuation ((h : G F Ω) (a : Ω) - a) < 1 := by
    intro h a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rfl
  let σ : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup F) _ g'
  have hσ : ∀ z, (σ^[n]) z = z := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    have hit : ∀ k z, (σ^[k]) z = (g' ^ k) • z := by
      intro k
      induction k with
      | zero => intro z; simp
      | succ k ih =>
        intro z
        rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
        rfl
    rw [hit, key]
    have hI := hgn
    simp only [Ine] at hI
    have h2 := hI.2 a (A.valuation_le_one a)
    simpa [g'] using h2
  have hfix : ∀ a : A, σ (IsLocalRing.residue A a) = IsLocalRing.residue A a := by
    intro a
    obtain ⟨m, hm, hy⟩ := exists_residue_pow_prime_pow_eq_self (F := F) p A hp a
    exact frobenius_fixed_of_iterate_fixed_pow_prime p σ n m hn hm hσ _ hy
  show g ∈ Inertia (F := F) A
  refine ⟨hgD, fun x hx => ?_⟩
  have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
  have := (key g' ⟨x, hxA⟩).1 (hfix ⟨x, hxA⟩)
  simpa [g'] using this
