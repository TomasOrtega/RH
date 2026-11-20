import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletionStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain in
/- English proof (translation)
Establish `hval : HeightOneSpectrum.valuation F v (p : F) = v.intValuation (p : 𝓞 F)`. Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := F)]`. Simplify using the standard rewrite rules. Establish `hne : v.intValuation (p : 𝓞 F) ≠ 0` using `v.intValuation_ne_zero _ (by exact_mod_cast hp.ne')`. Establish `hle : v.intValuation (p : 𝓞 F) ≤ 1` using `v.intValuation_le_one _`.

Use `set a := v.intValuation (p : 𝓞 F) with ha`. Establish `hlog : WithZero.log a ≤ 0`. Rewrite using `[← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]`. Conclude with `hle`. Use `⟨(-WithZero.log a).toNat, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hval, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]`. Rewrite using `[← HeightOneSpectrum.intValuation_le_pow_iff_dvd, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]`.
-/
private theorem exists_valuation_natCast_eq_exp_neg_and_dvd {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : 0 < p) :
    ∃ e : ℕ, HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-(e : ℤ)) ∧
      v.asIdeal ^ e ∣ Ideal.span {(p : 𝓞 F)} := by
  have hval : HeightOneSpectrum.valuation F v (p : F) = v.intValuation (p : 𝓞 F) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    simp
  have hne : v.intValuation (p : 𝓞 F) ≠ 0 :=
    v.intValuation_ne_zero _ (by exact_mod_cast hp.ne')
  have hle : v.intValuation (p : 𝓞 F) ≤ 1 := v.intValuation_le_one _
  set a := v.intValuation (p : 𝓞 F) with ha
  have hlog : WithZero.log a ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log a).toNat, ?_, ?_⟩
  · rw [hval, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, Int.toNat_of_nonneg (by omega), neg_neg,
      WithZero.exp_log hne]

open NumberField IsDedekindDomain in
/- English proof (translation)
Use extensionality with `x`. Rewrite using `[_root_.GlobalTheory.CNorm.mem_powSub, Subgroup.mem_comap]`. Unfold `_root_.GlobalTheory.CNorm.pows`. Simplify using `only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, hr⟩`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Rewrite `hr` using `[zero_pow hp.ne']`. Conclude with `(map_ne_zero φ).2 x.ne_zero hr.symm`.

Conclude with `⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩`. Introduce and unpack `⟨y, hy⟩`. Use `⟨(y : L), ?_⟩` and prove the remaining obligations. Use `congrArg Units.val hy` as an intermediate fact. Simplify using `using this`.
-/
private theorem powSub_eq_comap_pows_units_map {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) :
    _root_.GlobalTheory.CNorm.powSub p φ =
      (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).comap (Units.map φ.toMonoidHom) := by
  ext x
  rw [_root_.GlobalTheory.CNorm.mem_powSub, Subgroup.mem_comap]
  unfold _root_.GlobalTheory.CNorm.pows
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  · rintro ⟨y, hy⟩
    refine ⟨(y : L), ?_⟩
    have := congrArg Units.val hy
    simpa using this

open NumberField IsDedekindDomain in
/- English proof (translation)
Establish `hdef : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) = (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).index`. Unfold `_root_.GlobalTheory.CNorm.pIdx`. Conclude with `Subgroup.relIndex_top_right _`. Rewrite `h`, the goal using `[hdef]`. Rewrite using `[powSub_eq_comap_pows_units_map hp, Subgroup.index_comap]`.

Establish `hd` using `Subgroup.relIndex_dvd_index_of_normal (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)) (Units.map φ.toMonoidHom).range`. Conclude with `⟨ne_zero_of_dvd_ne_zero h hd, Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd⟩`.
-/
private theorem powSub_index_ne_zero_and_le_pIdx {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) (h : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) ≠ 0) :
    (_root_.GlobalTheory.CNorm.powSub p φ).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.powSub p φ).index ≤ _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) := by
  have hdef : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) = (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).index := by
    unfold _root_.GlobalTheory.CNorm.pIdx
    exact Subgroup.relIndex_top_right _
  rw [hdef] at h ⊢
  rw [powSub_eq_comap_pows_units_map hp, Subgroup.index_comap]
  have hd := Subgroup.relIndex_dvd_index_of_normal (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ))
    (Units.map φ.toMonoidHom).range
  exact ⟨ne_zero_of_dvd_ne_zero h hd, Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd⟩

open NumberField IsDedekindDomain in
/- English proof (translation)
Unfold `_root_.GlobalTheory.CNorm.pTor`. Establish `hinj : Function.Injective (fun x : {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1} => (⟨(x.1 : L), by`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_nthRoots hp, ← Units.val_pow_eq_pow_val, x.2.2, Units.val_one]⟩ : (Polynomial.nthRoots p (1 : L)).toFinset)) := by`. Introduce `x y hxy`. Conclude with `Subtype.ext (Units.ext (congrArg Subtype.val hxy))`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem pTor_units_le {L : Type} [Field L] {p : ℕ} (hp : 0 < p) :
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup Lˣ) ≤ p := by
  unfold _root_.GlobalTheory.CNorm.pTor
  classical
  have hinj : Function.Injective (fun x : {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1} =>
      (⟨(x.1 : L), by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp, ← Units.val_pow_eq_pow_val, x.2.2,
          Units.val_one]⟩ : (Polynomial.nthRoots p (1 : L)).toFinset)) := by
    intro x y hxy
    exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
  calc Nat.card {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1}
      ≤ Nat.card (Polynomial.nthRoots p (1 : L)).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (Polynomial.nthRoots p (1 : L)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (Polynomial.nthRoots p (1 : L)).card := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

open NumberField IsDedekindDomain in
/- English proof (translation)
Establish `hdvd : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)}`. Use `Finset.prod_dvd_of_coprime ?_ he` and prove the remaining obligations. Introduce `v _ w _ hvw`. Establish `hne : v.asIdeal ≠ w.asIdeal` using `fun h => hvw (HeightOneSpectrum.ext h)`. Conclude with `(Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne)).pow`.

Establish `hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 F)}) = p ^ Module.finrank ℚ F`. Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: (p : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]`. Simplify using the standard rewrite rules.

Establish `h` using `Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)`. Rewrite `h` using `[hnorm, map_prod]`. Simplify using `only [map_pow] at h`. Conclude with `Nat.le_of_dvd (pow_pos hp _) h`.
-/
private theorem prod_absNorm_pow_le_pow_finrank {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {p : ℕ} (hp : 0 < p) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (he : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)}) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ p ^ Module.finrank ℚ F := by
  have hdvd : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ he
    intro v _ w _ hvw
    have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (HeightOneSpectrum.ext h)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne)).pow
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 F)}) = p ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [hnorm, map_prod] at h
  simp only [map_pow] at h
  exact Nat.le_of_dvd (pow_pos hp _) h

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

/- English proof (translation)
Introduce `p F _ _ _ S hp`. Use `choose! e he hdiv using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_natCast_eq_exp_neg_and_dvd v hp`. Establish `hloc : ∀ v : HeightOneSpectrum (𝓞 F), (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≤ p * Ideal.absNorm v.asIdeal ^ e v * p`. Introduce `v`. Take `⟨ht, hrel⟩` from `_root_.GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion p F v (e v) (v.adicCompletion F) hp (he v)`.

Rewrite `hrel` using `[Module.finrank_self, pow_one]`. Establish `hN : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `hne : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (v.adicCompletion F)ˣ) ≠ 0`.

Rewrite using `[hrel]`. Conclude with `mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero _ hN)) ht`. Take `⟨h1, h2⟩` from `powSub_index_ne_zero_and_le_pIdx hp (algebraMap F (v.adicCompletion F)) hne`. Use `⟨h1, h2.trans ?_⟩` and prove the remaining obligations. Rewrite using `[hrel]`.

Conclude with `Nat.mul_le_mul_left _ (pTor_units_le hp)`. Establish `hinf : _root_.GlobalTheory.CNorm.finPow p F S = ⨅ v : S, _root_.GlobalTheory.CNorm.powSub p (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))`. Unfold `_root_.GlobalTheory.CNorm.finPow`. Rewrite using `[iInf_subtype']`. Rewrite using `[hinf]`.

Use `⟨Subgroup.index_iInf_ne_zero fun v => (hloc v).1, (Subgroup.index_iInf_le _).trans ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_coe_sort S (fun v => p * Ideal.absNorm v.asIdeal ^ e v * p)]`. Simplify using `only [Finset.prod_mul_distrib, Finset.prod_const]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ p ^ (2 * S.card) * p ^ Module.finrank ℚ F := Nat.mul_le_mul_left _ (prod_absNorm_pow_le_pow_finrank S hp e fun v _ => hdiv v)`. Use `_ = p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by`. Rewrite using `[IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, ← pow_add]`. Put the polynomial expressions in normal form.
-/
theorem _root_.GlobalTheory.CNorm.index_finPow_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p →
    (_root_.GlobalTheory.CNorm.finPow p F S).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.finPow p F S).index ≤
        p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  intro p F _ _ _ S hp
  choose! e he hdiv using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_natCast_eq_exp_neg_and_dvd v hp
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≤
          p * Ideal.absNorm v.asIdeal ^ e v * p := by
    intro v
    obtain ⟨ht, hrel⟩ :=
      _root_.GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion p F v (e v) (v.adicCompletion F) hp (he v)
    rw [Module.finrank_self, pow_one] at hrel
    have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have hne : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (v.adicCompletion F)ˣ) ≠ 0 := by
      rw [hrel]
      exact mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero _ hN)) ht
    obtain ⟨h1, h2⟩ := powSub_index_ne_zero_and_le_pIdx hp (algebraMap F (v.adicCompletion F)) hne
    refine ⟨h1, h2.trans ?_⟩
    rw [hrel]
    exact Nat.mul_le_mul_left _ (pTor_units_le hp)
  have hinf : _root_.GlobalTheory.CNorm.finPow p F S =
      ⨅ v : S, _root_.GlobalTheory.CNorm.powSub p
        (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
    unfold _root_.GlobalTheory.CNorm.finPow
    rw [iInf_subtype']
  rw [hinf]
  refine ⟨Subgroup.index_iInf_ne_zero fun v => (hloc v).1, (Subgroup.index_iInf_le _).trans ?_⟩
  calc ∏ v : S, (_root_.GlobalTheory.CNorm.powSub p
          (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).index
      ≤ ∏ v : S, (p * Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v * p) :=
        Finset.prod_le_prod' fun v _ => (hloc v).2
    _ = p ^ (2 * S.card) * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
        rw [Finset.prod_coe_sort S (fun v => p * Ideal.absNorm v.asIdeal ^ e v * p)]
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        ring
    _ ≤ p ^ (2 * S.card) * p ^ Module.finrank ℚ F :=
        Nat.mul_le_mul_left _ (prod_absNorm_pow_le_pow_finrank S hp e fun v _ => hdiv v)
    _ = p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
        rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
          IsTotallyComplex.nrRealPlaces_eq_zero, ← pow_add]
        ring_nf

end GlobalTheory.CNorm
