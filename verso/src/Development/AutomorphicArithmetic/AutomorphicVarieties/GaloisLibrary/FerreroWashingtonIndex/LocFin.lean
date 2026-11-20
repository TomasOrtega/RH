import GroundTheory.GlobalFields.HasseNorm
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Take `⟨b, hb⟩` from `IsDedekindDomain.exists_sup_span_eq (I := I * P) (J := I) Ideal.mul_le_left (mul_ne_zero hI hP)`. Take `⟨J, hJ⟩ : I ∣ Ideal.span {b}` from `Ideal.dvd_iff_le.2 (hb ▸ le_sup_right)`. Establish `h1 : P ⊔ J = ⊤`. Rewrite `hb` using `[hJ, ← Ideal.mul_sup]`. Use `mul_left_cancel₀ hI (hb.trans (mul_one I).symm)` as an intermediate fact.

Rewrite `this` using `[Ideal.one_eq_top]`. Then use the resulting hypothesis. Establish `h2 : P ⊔ J.map c = ⊤`. Use `congrArg (Ideal.map c) h1` as an intermediate fact. Rewrite `this` using `[Ideal.map_sup, hc, Ideal.map_top]`. Then use the resulting hypothesis. Establish `h3 : Ideal.span {b * c b} = Ideal.span {a} * (J * J.map c)`.

Use `congrArg (Ideal.map c) hJ` as an intermediate fact. Rewrite `this` using `[Ideal.map_span, Set.image_singleton, Ideal.map_mul]`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, hJ, this, ← h]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : b * c b ∈ Ideal.span {a}` using `(Ideal.span_singleton_le_iff_mem _).1 (h3 ▸ Ideal.mul_le_left)`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton.1 h4`. Use `⟨b, t, ht, fun w hw hPw htw => ?_⟩` and prove the remaining obligations. Rewrite `h3` using `[ht, ← Ideal.span_singleton_mul_span_singleton]`. Establish `h5` using `mul_left_cancel₀ (by simpa using ha) h3`. Establish `h6 : J * J.map c ≤ w` using `h5 ▸ (Ideal.span_singleton_le_iff_mem _).2 htw`.

Break down `hw.mul_le.1 h6 with h7 | h7` into its components or cases. Conclude with `hw.ne_top (top_le_iff.1 (h1 ▸ sup_le hPw h7))`. Conclude with `hw.ne_top (top_le_iff.1 (h2 ▸ sup_le hPw h7))`.
-/
private theorem ideal_step {R : Type} [CommRing R] [IsDedekindDomain R] (c : R ≃+* R) (P I : Ideal R) (a : R)
    (hP : P ≠ 0) (hI : I ≠ 0) (ha : a ≠ 0) (hc : P.map c = P) (h : I * I.map c = Ideal.span {a}) :
    ∃ b t : R, b * c b = a * t ∧ ∀ w : Ideal R, w.IsPrime → P ≤ w → t ∉ w := by
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := I * P) (J := I) Ideal.mul_le_left (mul_ne_zero hI hP)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {b} := Ideal.dvd_iff_le.2 (hb ▸ le_sup_right)
  have h1 : P ⊔ J = ⊤ := by
    rw [hJ, ← Ideal.mul_sup] at hb
    have := mul_left_cancel₀ hI (hb.trans (mul_one I).symm)
    rwa [Ideal.one_eq_top] at this
  have h2 : P ⊔ J.map c = ⊤ := by
    have := congrArg (Ideal.map c) h1
    rwa [Ideal.map_sup, hc, Ideal.map_top] at this
  have h3 : Ideal.span {b * c b} = Ideal.span {a} * (J * J.map c) := by
    have := congrArg (Ideal.map c) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul] at this
    rw [← Ideal.span_singleton_mul_span_singleton, hJ, this, ← h]; ring
  have h4 : b * c b ∈ Ideal.span {a} :=
    (Ideal.span_singleton_le_iff_mem _).1 (h3 ▸ Ideal.mul_le_left)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 h4
  refine ⟨b, t, ht, fun w hw hPw htw => ?_⟩
  rw [ht, ← Ideal.span_singleton_mul_span_singleton] at h3
  have h5 := mul_left_cancel₀ (by simpa using ha) h3
  have h6 : J * J.map c ≤ w := h5 ▸ (Ideal.span_singleton_le_iff_mem _).2 htw
  rcases hw.mul_le.1 h6 with h7 | h7
  · exact hw.ne_top (top_le_iff.1 (h1 ▸ sup_le hPw h7))
  · exact hw.ne_top (top_le_iff.1 (h2 ▸ sup_le hPw h7))

/- English proof (translation)
Establish `hcard : Fintype.card (K ≃ₐ[maximalRealSubfield K] K) = 2`. Rewrite using `[← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← IsCMField.zpowers_complexConj_eq_top, Nat.card_zpowers, IsCMField.orderOf_complexConj]`. Establish `hne` using `(IsCMField.complexConj_ne_one K).symm`. Establish `huniv : (Finset.univ : Finset (K ≃ₐ[maximalRealSubfield K] K)) = {1, IsCMField.complexConj K}` using `(Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm`. Rewrite using `[Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]`.

Both sides reduce to the same expression.
-/
private theorem norm_cm (K : Type) [Field K] [NumberField K] [IsCMField K] (b : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) b) = b * IsCMField.complexConj K b := by
  classical
  have hcard : Fintype.card (K ≃ₐ[maximalRealSubfield K] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← IsCMField.zpowers_complexConj_eq_top, Nat.card_zpowers,
      IsCMField.orderOf_complexConj]
  have hne := (IsCMField.complexConj_ne_one K).symm
  have huniv : (Finset.univ : Finset (K ≃ₐ[maximalRealSubfield K] K)) = {1, IsCMField.complexConj K} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

/- English proof (translation)
Introduce `K _ _ _ x a I hunr hax hI v`. Establish `haK : (a : K) ≠ 0` using `by rw [hax]; simp`. Establish `ha : a ≠ 0` using `fun h => haK (by rw [h]; rfl)`. Take `⟨w⟩` from `GroundTheory.Global.nonempty_placesOver K v`. Establish `hw : w.1.asIdeal.LiesOver v.asIdeal` using `inferInstance`.

Establish `hP : v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) ≠ 0` using `fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)`. Establish `hc : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))).map (RingOfIntegers.mapRingEquiv (cE K)) = v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))`. Establish `: ((RingOfIntegers.mapRingEquiv (cE K) : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K).comp (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)`. Use extensionality with `y`. Conclude with `(IsCMField.complexConj K).commutes (y : maximalRealSubfield K)`.

Rewrite using `[← Ideal.map_coe, Ideal.map_map, this]`. Take `⟨b, t, hbt, ht⟩` from `ideal_step (RingOfIntegers.mapRingEquiv (cE K)) _ I.1 a hP (nonZeroDivisors.ne_zero I.2) ha hc hI`. Establish `htw : t ∉ w.1.asIdeal` using `ht _ w.1.isPrime (Ideal.map_le_iff_le_comap.2 hw.over.le)`. Establish `ht0 : t ≠ 0` using `fun h => htw (h ▸ zero_mem _)`. Establish `hb0 : (b : K) ≠ 0`.

Introduce `h`. Establish `: b = 0` using `by simpa using h`. Rewrite `hbt` using `[this, zero_mul]`. Conclude with `mul_ne_zero ha ht0 hbt.symm`. Use `set n : (maximalRealSubfield K)ˣ := Units.map (Algebra.norm (maximalRealSubfield K)) (Units.mk0 (b : K) hb0) with hn`.

Establish `hy : algebraMap (maximalRealSubfield K) K ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = (t : K)`. Establish `h1 : algebraMap (maximalRealSubfield K) K n = (a : K) * t` using `(norm_cm K b).trans (congrArg (fun z : 𝓞 K => (z : K)) hbt)`. Rewrite using `[Units.val_mul, map_mul, h1, Units.val_inv_eq_inv_val, map_inv₀, ← hax]`. Clear the denominators using the available nonvanishing facts. Establish `hv : v.valuation (maximalRealSubfield K) ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = 1`.

Establish `h1` using `HeightOneSpectrum.valuation_liesOver K v w.1 ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K)`. Rewrite `h1` using `[hy, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w.1).2 htw]`. Conclude with `(pow_eq_one_iff.1 h1).resolve_right (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot)`. Establish `h1 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) n) ∈ (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range`. Rewrite using `[hn, ← GroundTheory.Global.ideleNorm_diagonal, GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm]`.

Conclude with `⟨_, rfl⟩`. Establish `h2 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) (n * x⁻¹)) ∈ (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range`. Use `Subgroup.map_le_range _ (GroundTheory.Global.IdeleNorm.integerUnitsOver K v) ?_` and prove the remaining obligations. Rewrite using `[GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hunr w.1)]`. Use `HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 ?_` and prove the remaining obligations.

Rewrite using `[GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans hv`. Establish `h3` using `mul_mem (inv_mem h2) h1`. Rewrite `h3` using `[← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.FW.locFin :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ) (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → (a : K) = algebraMap (maximalRealSubfield K) K x → (I * idMap (cE K) I).1 = Ideal.span {a} → ∀ v, GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
  intro K _ _ _ x a I hunr hax hI v
  have haK : (a : K) ≠ 0 := by rw [hax]; simp
  have ha : a ≠ 0 := fun h => haK (by rw [h]; rfl)
  obtain ⟨w⟩ := GroundTheory.Global.nonempty_placesOver K v
  have hw : w.1.asIdeal.LiesOver v.asIdeal := inferInstance
  have hP : v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  have hc : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))).map (RingOfIntegers.mapRingEquiv (cE K)) =
      v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) := by
    have : ((RingOfIntegers.mapRingEquiv (cE K) : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K).comp (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
      ext y
      exact (IsCMField.complexConj K).commutes (y : maximalRealSubfield K)
    rw [← Ideal.map_coe, Ideal.map_map, this]
  obtain ⟨b, t, hbt, ht⟩ := ideal_step (RingOfIntegers.mapRingEquiv (cE K)) _ I.1 a hP (nonZeroDivisors.ne_zero I.2) ha hc hI
  have htw : t ∉ w.1.asIdeal := ht _ w.1.isPrime (Ideal.map_le_iff_le_comap.2 hw.over.le)
  have ht0 : t ≠ 0 := fun h => htw (h ▸ zero_mem _)
  have hb0 : (b : K) ≠ 0 := by
    intro h
    have : b = 0 := by simpa using h
    rw [this, zero_mul] at hbt
    exact mul_ne_zero ha ht0 hbt.symm
  set n : (maximalRealSubfield K)ˣ := Units.map (Algebra.norm (maximalRealSubfield K)) (Units.mk0 (b : K) hb0) with hn
  have hy : algebraMap (maximalRealSubfield K) K ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = (t : K) := by
    have h1 : algebraMap (maximalRealSubfield K) K n = (a : K) * t :=
      (norm_cm K b).trans (congrArg (fun z : 𝓞 K => (z : K)) hbt)
    rw [Units.val_mul, map_mul, h1, Units.val_inv_eq_inv_val, map_inv₀, ← hax]
    field_simp
  have hv : v.valuation (maximalRealSubfield K) ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = 1 := by
    have h1 := HeightOneSpectrum.valuation_liesOver K v w.1 ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K)
    rw [hy, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w.1).2 htw] at h1
    exact (pow_eq_one_iff.1 h1).resolve_right (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot)
  have h1 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) n) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    rw [hn, ← GroundTheory.Global.ideleNorm_diagonal, GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm]
    exact ⟨_, rfl⟩
  have h2 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) (n * x⁻¹)) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    refine Subgroup.map_le_range _ (GroundTheory.Global.IdeleNorm.integerUnitsOver K v) ?_
    rw [GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hunr w.1)]
    refine HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 ?_
    rw [GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans hv
  have h3 := mul_mem (inv_mem h2) h1
  rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right] at h3
