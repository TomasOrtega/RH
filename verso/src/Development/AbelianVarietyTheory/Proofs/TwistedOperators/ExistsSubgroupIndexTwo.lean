import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletion

open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex

namespace GlobalTheory.QuadraticValuationIndexTwo

/- English proof (translation)
Establish `kb` using `GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ h`. Establish `hinv : ∀ z, σ (σ z) = z` using `fun z => kb.2.2.1 z`. Establish `hfix` using `kb.2.2.2.1`. Establish `hpow : θ ^ 2 = algebraMap B E d` using `h.pow`. Establish `hconj : σ θ = -θ` using `by rw [h.conj, map_neg, map_one, neg_one_mul]`.

Establish `: CharZero E` using `charZero_of_injective_algebraMap (algebraMap B E).injective`. Establish `hθ : θ ≠ 0`. Introduce `h0`. Apply `h.nonpow 0` to reduce the goal to its premises. Apply `(algebraMap B E).injective` to reduce the goal to its premises.

Rewrite using `[← hpow, h0]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Take `⟨a, ha⟩` from `hfix ((y + σ y) / 2) (by`.

Rewrite using `[map_div₀, map_add, hinv, map_ofNat, add_comm])`. Take `⟨b, hb⟩` from `hfix ((y - σ y) / (2 * θ)) (by`. Rewrite using `[map_div₀, map_sub, hinv, map_mul, hconj, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub])`. Establish `hy' : y = algebraMap B E a + algebraMap B E b * θ`. Rewrite using `[← ha, ← hb]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hσy : σ y = algebraMap B E a - algebraMap B E b * θ`. Rewrite using `[hy', map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨a, b, (algebraMap B E).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, hσy, hy']`. Simplify using `only [map_sub, map_mul, map_pow]`. Rewrite using `[← hpow]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨a, b, rfl⟩`. Use `⟨algebraMap B E a + algebraMap B E b * θ, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]`. Simplify using `only [map_sub, map_mul, map_pow]`. Rewrite using `[← hpow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_conj_iff {B E : Type} [Field B] [CharZero B] [Field E] [Algebra B E] {d : B}
    {θ : E} {σ : E ≃ₐ[B] E} (h : IsKum 2 (-1 : B) d θ σ) (x : B) :
    (∃ y : E, y * σ y = algebraMap B E x) ↔ Nm d x := by
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ h
  have hinv : ∀ z, σ (σ z) = z := fun z => kb.2.2.1 z
  have hfix := kb.2.2.2.1
  have hpow : θ ^ 2 = algebraMap B E d := h.pow
  have hconj : σ θ = -θ := by rw [h.conj, map_neg, map_one, neg_one_mul]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap B E).injective
  have hθ : θ ≠ 0 := by
    intro h0
    apply h.nonpow 0
    apply (algebraMap B E).injective
    rw [← hpow, h0]
    simp
  constructor
  · rintro ⟨y, hy⟩

    obtain ⟨a, ha⟩ := hfix ((y + σ y) / 2) (by
      rw [map_div₀, map_add, hinv, map_ofNat, add_comm])
    obtain ⟨b, hb⟩ := hfix ((y - σ y) / (2 * θ)) (by
      rw [map_div₀, map_sub, hinv, map_mul, hconj, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub])
    have hy' : y = algebraMap B E a + algebraMap B E b * θ := by
      rw [← ha, ← hb]
      field_simp
      ring
    have hσy : σ y = algebraMap B E a - algebraMap B E b * θ := by
      rw [hy', map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
      ring
    refine ⟨a, b, (algebraMap B E).injective ?_⟩
    rw [← hy, hσy, hy']
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring
  · rintro ⟨a, b, rfl⟩
    refine ⟨algebraMap B E a + algebraMap B E b * θ, ?_⟩
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring

/- English proof (translation)
Establish `h0 : v.valuation F ((2 : ℕ) : F) ≠ 0` using `(Valuation.ne_zero_iff _).mpr (by norm_num)`. Establish `hle : v.valuation F ((2 : ℕ) : F) ≤ 1`. Use `GlobalTheory.QuadSymbol.NormIndex.map_two_le (v.valuation F)` as an intermediate fact. Simplify using `using this`. Establish `hlog : WithZero.log (v.valuation F ((2 : ℕ) : F)) ≤ 0`.

Rewrite using `[WithZero.log_le_iff_le_exp h0]`. Simplify using `using hle`. Use `⟨(-WithZero.log (v.valuation F ((2 : ℕ) : F))).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]`.
-/
theorem exists_valuation_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℕ, v.valuation F ((2 : ℕ) : F) = WithZero.exp (-(e : ℤ)) := by
  have h0 : v.valuation F ((2 : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr (by norm_num)
  have hle : v.valuation F ((2 : ℕ) : F) ≤ 1 := by
    have := GlobalTheory.QuadSymbol.NormIndex.map_two_le (v.valuation F)
    simpa using this
  have hlog : WithZero.log (v.valuation F ((2 : ℕ) : F)) ≤ 0 := by
    rw [WithZero.log_le_iff_le_exp h0]
    simpa using hle
  refine ⟨(-WithZero.log (v.valuation F ((2 : ℕ) : F))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]

/- English proof (translation)
Use `set K := v.adicCompletion F`. Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap F K).injective`. Establish `: CharZero B` using `charZero_of_injective_algebraMap (algebraMap K B).injective`. Establish `hnp : ∀ r : B, r ^ 2 ≠ d` using `fun r hr => hd ⟨r, by rw [← hr, sq]⟩`. Take `⟨E, _, _, θ, σ, hK⟩` from `GlobalTheory.CNorm.exists_isKum 2 B (-1) d Nat.prime_two (IsPrimitiveRoot.neg_one 0 (by norm_num)) hnp`.

Establish `kb` using `GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ hK`. Establish `: FiniteDimensional B E` using `kb.1`. Set `: Algebra K E` to `((algebraMap B E).comp (algebraMap K B)).toAlgebra`. Establish `: IsScalarTower K B E` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `: FiniteDimensional K E` using `Module.Finite.trans B E`.

Take `⟨e, he⟩` from `exists_valuation_two F v`. Establish `hB` using `GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e B (by norm_num) he`. Establish `hE` using `GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e E (by norm_num) he`. Set `σ' : Eˣ →* Eˣ` to `Units.map (σ : E →+* E).toMonoidHom`. Set `j : Bˣ →* Eˣ` to `Units.map (algebraMap B E).toMonoidHom`.

Establish `hσ' : ∀ y : Eˣ, ((σ' y : Eˣ) : E) = σ (y : E)` using `fun y => rfl`. Establish `hj' : ∀ x : Bˣ, ((j x : Eˣ) : E) = algebraMap B E (x : B)` using `fun x => rfl`. Establish `hj : Function.Injective j` using `fun a b hab => Units.ext ((algebraMap B E).injective (by rw [← hj', ← hj', hab]))`. Establish `hσ'2 : ∀ a, σ'^[2] a = a` using `fun a => Units.ext (kb.2.2.1 (a : E))`. Establish `hfix : GlobalTheory.CNorm.fix σ' = j.range`.

Use extensionality with `x`. Rewrite using `[GlobalTheory.CNorm.mem_fix, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : σ (x : E) = x` using `by rw [← hσ', hx]`.

Take `⟨a, ha⟩` from `kb.2.2.2.1 (x : E) hx'`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `x.ne_zero (by rw [ha, map_zero])`. Conclude with `⟨Units.mk0 a ha0, Units.ext (by rw [hj', Units.val_mk0, ha])⟩`.

Introduce and unpack `⟨b, rfl⟩`. Conclude with `Units.ext (by rw [hσ', hj', AlgEquiv.commutes])`. Establish `hnrm : ∀ y : Eˣ, ((GlobalTheory.CNorm.nrm σ' 2 y : Eˣ) : E) = (y : E) * σ y`. Introduce `y`. Rewrite using `[GlobalTheory.CNorm.nrm_apply, Finset.prod_range_succ, Finset.prod_range_one]`.

Both sides reduce to the same expression. Establish `hker : (GlobalTheory.CNorm.nrm σ' 2).ker ≤ (GlobalTheory.CNorm.dif σ').range`. Introduce `y hy`. Rewrite `hy` using `[MonoidHom.mem_ker]`. Establish `h1 : ∏ i ∈ Finset.range 2, σ^[i] (y : E) = 1`.

Rewrite using `[Finset.prod_range_succ, Finset.prod_range_one]`. Use `congrArg Units.val hy` as an intermediate fact. Rewrite `this` using `[hnrm]`. Conclude with `this`. Take `⟨z, hz0, hz⟩` from `kb.2.2.2.2.1 (y : E) h1`.

Use `⟨Units.mk0 z hz0, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CNorm.dif_apply, Units.val_div_eq_div_val, hσ', Units.val_mk0, hz]`. Establish `hR2 : (GlobalTheory.CNorm.dif σ').range.relIndex (GlobalTheory.CNorm.nrm σ' 2).ker = 1` using `Subgroup.relIndex_eq_one.mpr hker`. Establish `hq : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `v.ne_bot`. Establish `hIE : GlobalTheory.CNorm.pIdx 2 (⊤ : Subgroup Eˣ) ≠ 0`. Rewrite using `[hE.2]`. Conclude with `mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1`. Take `⟨-, -, -, -, heq⟩` from `GlobalTheory.CNorm.herbrand_prime_order 2 Eˣ σ' Nat.prime_two hσ'2 hIE hE.1`.

Rewrite `heq` using `[hfix, hR2, GlobalTheory.CNorm.pIdx_range_of_injective 2 j hj, GlobalTheory.CNorm.pTor_range_of_injective 2 j hj, hE.2, hB.2]`. Establish `hrank : Module.finrank K E = Module.finrank K B * 2`. Rewrite using `[← Module.finrank_mul_finrank K B E, kb.2.1]`. Rewrite `heq` using `[hrank, pow_mul]`. Use `set Q := (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank K B`.

Use `set TE := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Eˣ)`. Use `set TB := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Bˣ)`. Use `set R := (GlobalTheory.CNorm.nrm σ' 2).range.relIndex j.range`. Establish `hX : Q ^ 2 * TE * TB ^ 2 ≠ 0` using `mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1) (pow_ne_zero _ hB.1)`. Establish `hR : R = 2`.

Establish `h4 : (R * 2) * (Q ^ 2 * TE * TB ^ 2) = 4 * (Q ^ 2 * TE * TB ^ 2)`. Establish `e21 : (2 : ℕ) - 1 = 1` using `rfl`. Rewrite `heq` using `[e21, pow_one, one_pow, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX) h4` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `⟨(GlobalTheory.CNorm.nrm σ' 2).range.comap j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.index_comap]`. Conclude with `hR`. Introduce `x`.

Rewrite using `[Subgroup.mem_comap, MonoidHom.mem_range, ← exists_mul_conj_iff hK (x : B)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨(y : E), ?_⟩` and prove the remaining obligations. Rewrite using `[← hnrm, hy, hj']`.

Introduce and unpack `⟨y, hy⟩`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[zero_mul]`. Conclude with `x.ne_zero ((algebraMap B E).injective (by rw [← hy, map_zero]))`.

Use `⟨Units.mk0 y hy0, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hnrm, hj', Units.val_mk0]`. Conclude with `hy`.
-/
theorem exists_subgroup_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    ∃ N : Subgroup Bˣ, N.index = 2 ∧ ∀ x : Bˣ, x ∈ N ↔ Nm d (x : B) := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have hnp : ∀ r : B, r ^ 2 ≠ d := fun r hr => hd ⟨r, by rw [← hr, sq]⟩

  obtain ⟨E, _, _, θ, σ, hK⟩ :=
    GlobalTheory.CNorm.exists_isKum 2 B (-1) d Nat.prime_two (IsPrimitiveRoot.neg_one 0 (by norm_num)) hnp
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ hK
  have : FiniteDimensional B E := kb.1
  let : Algebra K E := ((algebraMap B E).comp (algebraMap K B)).toAlgebra
  have : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FiniteDimensional K E := Module.Finite.trans B E
  obtain ⟨e, he⟩ := exists_valuation_two F v
  have hB := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e B (by norm_num) he
  have hE := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e E (by norm_num) he
  let σ' : Eˣ →* Eˣ := Units.map (σ : E →+* E).toMonoidHom
  let j : Bˣ →* Eˣ := Units.map (algebraMap B E).toMonoidHom
  have hσ' : ∀ y : Eˣ, ((σ' y : Eˣ) : E) = σ (y : E) := fun y => rfl
  have hj' : ∀ x : Bˣ, ((j x : Eˣ) : E) = algebraMap B E (x : B) := fun x => rfl
  have hj : Function.Injective j := fun a b hab =>
    Units.ext ((algebraMap B E).injective (by rw [← hj', ← hj', hab]))
  have hσ'2 : ∀ a, σ'^[2] a = a := fun a => Units.ext (kb.2.2.1 (a : E))

  have hfix : GlobalTheory.CNorm.fix σ' = j.range := by
    ext x
    rw [GlobalTheory.CNorm.mem_fix, MonoidHom.mem_range]
    constructor
    · intro hx
      have hx' : σ (x : E) = x := by rw [← hσ', hx]
      obtain ⟨a, ha⟩ := kb.2.2.2.1 (x : E) hx'
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [ha, map_zero])
      exact ⟨Units.mk0 a ha0, Units.ext (by rw [hj', Units.val_mk0, ha])⟩
    · rintro ⟨b, rfl⟩
      exact Units.ext (by rw [hσ', hj', AlgEquiv.commutes])
  have hnrm : ∀ y : Eˣ, ((GlobalTheory.CNorm.nrm σ' 2 y : Eˣ) : E) = (y : E) * σ y := by
    intro y
    rw [GlobalTheory.CNorm.nrm_apply, Finset.prod_range_succ, Finset.prod_range_one]
    rfl

  have hker : (GlobalTheory.CNorm.nrm σ' 2).ker ≤ (GlobalTheory.CNorm.dif σ').range := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ∏ i ∈ Finset.range 2, σ^[i] (y : E) = 1 := by
      rw [Finset.prod_range_succ, Finset.prod_range_one]
      have := congrArg Units.val hy
      rw [hnrm] at this
      exact this
    obtain ⟨z, hz0, hz⟩ := kb.2.2.2.2.1 (y : E) h1
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [GlobalTheory.CNorm.dif_apply, Units.val_div_eq_div_val, hσ', Units.val_mk0, hz]
  have hR2 : (GlobalTheory.CNorm.dif σ').range.relIndex (GlobalTheory.CNorm.nrm σ' 2).ker = 1 :=
    Subgroup.relIndex_eq_one.mpr hker
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hIE : GlobalTheory.CNorm.pIdx 2 (⊤ : Subgroup Eˣ) ≠ 0 := by
    rw [hE.2]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1

  obtain ⟨-, -, -, -, heq⟩ := GlobalTheory.CNorm.herbrand_prime_order 2 Eˣ σ' Nat.prime_two hσ'2 hIE hE.1
  rw [hfix, hR2, GlobalTheory.CNorm.pIdx_range_of_injective 2 j hj, GlobalTheory.CNorm.pTor_range_of_injective 2 j hj,
    hE.2, hB.2] at heq
  have hrank : Module.finrank K E = Module.finrank K B * 2 := by
    rw [← Module.finrank_mul_finrank K B E, kb.2.1]
  rw [hrank, pow_mul] at heq
  set Q := (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank K B
  set TE := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Eˣ)
  set TB := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Bˣ)
  set R := (GlobalTheory.CNorm.nrm σ' 2).range.relIndex j.range
  have hX : Q ^ 2 * TE * TB ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1)
      (pow_ne_zero _ hB.1)
  have hR : R = 2 := by
    have h4 : (R * 2) * (Q ^ 2 * TE * TB ^ 2) = 4 * (Q ^ 2 * TE * TB ^ 2) := by
      have e21 : (2 : ℕ) - 1 = 1 := rfl
      rw [e21, pow_one, one_pow, one_mul] at heq
      calc (R * 2) * (Q ^ 2 * TE * TB ^ 2) = R * (2 * Q ^ 2 * TE) * TB ^ 2 := by ring
        _ = TE * (2 * Q * TB) ^ 2 := heq
        _ = 4 * (Q ^ 2 * TE * TB ^ 2) := by ring
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX) h4
    omega
  refine ⟨(GlobalTheory.CNorm.nrm σ' 2).range.comap j, ?_, ?_⟩
  · rw [Subgroup.index_comap]
    exact hR
  · intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_range, ← exists_mul_conj_iff hK (x : B)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(y : E), ?_⟩
      rw [← hnrm, hy, hj']
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hy
        exact x.ne_zero ((algebraMap B E).injective (by rw [← hy, map_zero]))
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [hnrm, hj', Units.val_mk0]
      exact hy

/- English proof (translation)
Take `⟨N, hN, hmem⟩` from `exists_subgroup_index_two F v B d hd`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hne : N ≠ ⊤`. Introduce and unpack `rfl`. Rewrite `hN` using `[Subgroup.index_top]`.

Conclude with `absurd hN (by norm_num)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : Bˣ, c ∉ N := by`. Assume the negation of the conclusion as `hall`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Introduce `c _`. Assume the negation of the conclusion as `hc`. Conclude with `hall ⟨c, hc⟩`. Conclude with `⟨c, c.ne_zero, fun h => hc ((hmem c).mpr h)⟩`. Introduce `x y hx hy hnx hny`.

Establish `hx' : Units.mk0 x hx ∉ N` using `fun h => hnx ((hmem _).mp h)`. Establish `hy' : Units.mk0 y hy ∉ N` using `fun h => hny ((hmem _).mp h)`. Establish `: Units.mk0 x hx * Units.mk0 y hy ∈ N` using `(Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hx' hy')`. Conclude with `(hmem _).mp this`.
-/
theorem norm_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
      ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by
  obtain ⟨N, hN, hmem⟩ := exists_subgroup_index_two F v B d hd
  refine ⟨?_, ?_⟩
  ·
    have hne : N ≠ ⊤ := by
      rintro rfl
      rw [Subgroup.index_top] at hN
      exact absurd hN (by norm_num)
    obtain ⟨c, hc⟩ : ∃ c : Bˣ, c ∉ N := by
      by_contra hall
      apply hne
      rw [eq_top_iff]
      intro c _
      by_contra hc
      exact hall ⟨c, hc⟩
    exact ⟨c, c.ne_zero, fun h => hc ((hmem c).mpr h)⟩
  · intro x y hx hy hnx hny
    have hx' : Units.mk0 x hx ∉ N := fun h => hnx ((hmem _).mp h)
    have hy' : Units.mk0 y hy ∉ N := fun h => hny ((hmem _).mp h)
    have : Units.mk0 x hx * Units.mk0 y hy ∈ N :=
      (Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hx' hy')
    exact (hmem _).mp this

end GlobalTheory.QuadraticValuationIndexTwo
