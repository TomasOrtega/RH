import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValPlRes
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (O F L) in

noncomputable def hoEquiv : HeightOneSpectrum (integralClosure O L) ≃
    {Q : Ideal (integralClosure O L) // Q.IsMaximal} where
  toFun v := ⟨v.asIdeal, v.isMaximal⟩
  invFun Q := (exists_heightOne O F L Q.1 Q.2).choose
  left_inv v := by
    apply HeightOneSpectrum.ext
    exact (exists_heightOne O F L v.asIdeal v.isMaximal).choose_spec
  right_inv Q := Subtype.ext (exists_heightOne O F L Q.1 Q.2).choose_spec

include F in

/- English proof (translation)
Use `haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O F L (integralClosure O L)`. Establish `hinj : Function.Injective (algebraMap O L)`. Rewrite using `[IsScalarTower.algebraMap_eq O F L]`. Conclude with `(algebraMap F L).injective.comp (IsFractionRing.injective O F)`. Establish `hinjB : Function.Injective (algebraMap O (integralClosure O L))`.

Introduce `x y hxy`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[IsScalarTower.algebraMap_apply O (integralClosure O L) L x, IsScalarTower.algebraMap_apply O (integralClosure O L) L y, hxy]`. Use `haveI : NoZeroSMulDivisors O (integralClosure O L) := by`. Use `⟨fun {c x} h => ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[Algebra.smul_def, mul_eq_zero]`. Conclude with `h.imp_left (fun h' => hinjB (h'.trans (map_zero _).symm))`. Establish `hN` using `ReciprocityTheory.MultiplicativeHeights.Closed.normOrd O (integralClosure O L) b hb`. Establish `hne : Algebra.norm O b ≠ 0`. Introduce `h0`.

Rewrite `hN` using `[h0, IsDiscreteValuationRing.addVal_zero]`. Conclude with `ENat.top_ne_coe _ hN`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ`. Establish `hn` using `IsDiscreteValuationRing.addVal_def _ u hϖ n hu`. Rewrite `hN` using `[hn]`.

Establish `hnN : n = ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}, Q.1.inertiaDeg O * Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))`. Conclude with `hN` after adjusting the coercions. Establish `hsum : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) = n`. Rewrite using `[hnN]`. Conclude with `finsum_comp_equiv (hoEquiv O F L) (f := fun Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal} => Q.1.inertiaDeg O * Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))`.

Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L := IsIntegralClosure.isLocalization O F L (integralClosure O L)`. Use `⟨u, u.isUnit, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.norm_localization O (nonZeroDivisors O) b, hu, hsum, mul_comm (u : O)]`.
-/
theorem norm_integral (b : integralClosure O L) (hb : b ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F (algebraMap (integralClosure O L) L b) = algebraMap O F
        (ϖ ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
          * u) := by
  haveI : Module.Finite O (integralClosure O L) :=
    IsIntegralClosure.finite O F L (integralClosure O L)
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  have hinjB : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x,
      IsScalarTower.algebraMap_apply O (integralClosure O L) L y, hxy]
  haveI : NoZeroSMulDivisors O (integralClosure O L) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h' => hinjB (h'.trans (map_zero _).symm))
  have hN := ReciprocityTheory.MultiplicativeHeights.Closed.normOrd O (integralClosure O L) b hb
  have hne : Algebra.norm O b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hN
    exact ENat.top_ne_coe _ hN
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hn := IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  rw [hn] at hN
  have hnN : n = ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}, Q.1.inertiaDeg O *
      Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
    exact_mod_cast hN
  have hsum : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) = n := by
    rw [hnN]
    exact finsum_comp_equiv (hoEquiv O F L)
      (f := fun Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal} => Q.1.inertiaDeg O *
        Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L :=
    IsIntegralClosure.isLocalization O F L (integralClosure O L)
  refine ⟨u, u.isUnit, ?_⟩
  rw [Algebra.norm_localization O (nonZeroDivisors O) b, hu, hsum, mul_comm (u : O)]

/- English proof (translation)
Use `haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by`. Establish `hinj : Function.Injective (algebraMap O L)`. Rewrite using `[IsScalarTower.algebraMap_eq O F L]`. Conclude with `(algebraMap F L).injective.comp (IsFractionRing.injective O F)`. Take `⟨b, hbdef⟩ : ∃ b : (integralClosure O L), b = algebraMap O (integralClosure O L) ϖ` from `⟨_, rfl⟩`.

Establish `hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ`. Rewrite using `[hbdef]`. Conclude with `(IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm`. Establish `hb : b ≠ 0`. Introduce `h0`.

Establish `h00 : algebraMap O L ϖ = 0` using `by rw [← hbL, h0, map_zero]`. Conclude with `hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))`. Establish `hmem : ϖ ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit`. Establish `hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b}`. Introduce `v`.

Establish `h1` using `((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem`. Rewrite `h1` using `[← hbL, addv_count v b hb]`. Establish `h2 : 0 < Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))`. Break down `Nat.eq_zero_or_pos (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h` into its components or cases. Rewrite `h1` using `[h, Nat.cast_zero]`.

Conclude with `absurd h1 (lt_irrefl 0)`. Conclude with `h`. Conclude with `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)`. Establish `hspan : Ideal.span {b} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hb`. Establish `hfin` using `Ideal.finite_factors hspan`. Establish `huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} = Set.univ` using `Set.eq_univ_of_forall hdvd`. Rewrite `hfin` using `[huniv]`. Conclude with `Set.finite_univ_iff.1 hfin`.

Use `haveI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))`. Take `⟨b1, b2, hb2m, hyb⟩` from `IsFractionRing.div_surjective (A := (integralClosure O L)) y`. Establish `hb2 : b2 ≠ 0` using `nonZeroDivisors.ne_zero hb2m`. Establish `hb1 : b1 ≠ 0`. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Rewrite using `[← hyb, h, map_zero, zero_div]`. Establish `hb2L : algebraMap (integralClosure O L) L b2 ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).2 hb2`. Establish `hyb2 : y * algebraMap (integralClosure O L) L b2 = algebraMap (integralClosure O L) L b1`. Rewrite using `[← hyb, div_mul_cancel₀ _ hb2L]`.

Establish `ha : algebraMap O F ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O F)).2 hϖ.ne_zero`. Take `⟨u1, hu1, h1⟩` from `norm_integral (F := F) b1 hb1 hϖ`. Take `⟨u2, hu2, h2⟩` from `norm_integral (F := F) b2 hb2 hϖ`. Establish `hmul : Algebra.norm F y * Algebra.norm F (algebraMap (integralClosure O L) L b2) = Algebra.norm F (algebraMap (integralClosure O L) L b1)`. Rewrite using `[← map_mul, hyb2]`.

Rewrite `hmul` using `[h1, h2]`. Simplify using `only [map_mul, map_pow] at hmul`. Establish `hk : ∀ v : HeightOneSpectrum (integralClosure O L), WithTop.untopD 0 (addv L v y) = ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) - ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : …`. Introduce `v`. Establish `hm` using `(addv L v).map_mul y (algebraMap (integralClosure O L) L b2)`.

Rewrite `hm` using `[hyb2, addv_count v b1 hb1, addv_count v b2 hb2]`. Take `⟨k, hk⟩` from `WithTop.ne_top_iff_exists.1 (mt (addv L v).top_iff.1 hy)`. Rewrite `hm`, the goal using `[← hk]`. Establish `hm' : ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) = k + ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ)`. Conclude with `hm` after adjusting the coercions.

Rewrite using `[WithTop.untopD_coe]`. Use linear arithmetic over natural numbers and integers. Establish `hz : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) = (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1} …`. Simplify using `only [hk]`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`.

Use `push_cast`. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨u1 * ((hu2.unit⁻¹ : Oˣ) : O), hu1.mul (hu2.unit⁻¹).isUnit, ?_⟩` and prove the remaining obligations. Establish `hU : algebraMap O F u2 * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O) = 1`. Rewrite using `[← map_mul, hu2.mul_val_inv, map_one]`. Establish `haS : (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) ≠ 0` using `pow_ne_zero _ ha`. Rewrite using `[hz, zpow_sub₀ ha, zpow_natCast, zpow_natCast, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ haS, hU, one_mul, mul_one]`. Use `_ = (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) * algebraMap O F u1 * (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L …`. Rewrite using `[hmul]`. Use `_ = _ := by`.

Rewrite using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_eq_heightOne (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
          (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) * algebraMap O F u := by
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have hinj : Function.Injective (algebraMap O L) := by
      rw [IsScalarTower.algebraMap_eq O F L]
      exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
    obtain ⟨b, hbdef⟩ : ∃ b : (integralClosure O L), b = algebraMap O (integralClosure O L) ϖ := ⟨_, rfl⟩
    have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
      rw [hbdef]
      exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
    have hb : b ≠ 0 := by
      intro h0
      have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
      exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
    have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
    have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
      intro v
      have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
      rw [← hbL, addv_count v b hb] at h1
      have h2 : 0 < Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
        rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
        · rw [h, Nat.cast_zero] at h1
          exact absurd h1 (lt_irrefl 0)
        · exact h
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
    have hspan : Ideal.span {b} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hb
    have hfin := Ideal.finite_factors hspan
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} = Set.univ :=
      Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  haveI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  obtain ⟨b1, b2, hb2m, hyb⟩ := IsFractionRing.div_surjective (A := (integralClosure O L)) y
  have hb2 : b2 ≠ 0 := nonZeroDivisors.ne_zero hb2m
  have hb1 : b1 ≠ 0 := by
    intro h
    apply hy
    rw [← hyb, h, map_zero, zero_div]
  have hb2L : algebraMap (integralClosure O L) L b2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).2 hb2
  have hyb2 : y * algebraMap (integralClosure O L) L b2 = algebraMap (integralClosure O L) L b1 := by
    rw [← hyb, div_mul_cancel₀ _ hb2L]
  have ha : algebraMap O F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O F)).2 hϖ.ne_zero
  obtain ⟨u1, hu1, h1⟩ := norm_integral (F := F) b1 hb1 hϖ
  obtain ⟨u2, hu2, h2⟩ := norm_integral (F := F) b2 hb2 hϖ
  have hmul : Algebra.norm F y * Algebra.norm F (algebraMap (integralClosure O L) L b2) =
      Algebra.norm F (algebraMap (integralClosure O L) L b1) := by
    rw [← map_mul, hyb2]
  rw [h1, h2] at hmul
  simp only [map_mul, map_pow] at hmul
  have hk : ∀ v : HeightOneSpectrum (integralClosure O L),
      WithTop.untopD 0 (addv L v y) = ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) - ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
    intro v
    have hm := (addv L v).map_mul y (algebraMap (integralClosure O L) L b2)
    rw [hyb2, addv_count v b1 hb1, addv_count v b2 hb2] at hm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (mt (addv L v).top_iff.1 hy)
    rw [← hk] at hm ⊢
    have hm' : ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) = k + ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
      exact_mod_cast hm
    rw [WithTop.untopD_coe]
    omega
  have hz : (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
      (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) =
        (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) : ℕ) : ℤ) - (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) : ℕ) : ℤ) := by
    simp only [hk]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  refine ⟨u1 * ((hu2.unit⁻¹ : Oˣ) : O), hu1.mul (hu2.unit⁻¹).isUnit, ?_⟩
  have hU : algebraMap O F u2 * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, hu2.mul_val_inv, map_one]
  have haS : (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) ≠ 0 := pow_ne_zero _ ha
  rw [hz, zpow_sub₀ ha, zpow_natCast, zpow_natCast, map_mul]
  calc Algebra.norm F y
      = Algebra.norm F y * ((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) * algebraMap O F u2) *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ haS, hU, one_mul, mul_one]
    _ = (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) * algebraMap O F u1 *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [hmul]
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

/- English proof (translation)
Take `⟨u, hu, h⟩` from `norm_eq_heightOne (F := F) y hy hϖ`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Use `congr 2`. Take `⟨e, he⟩` from `placesOver_bij (O := O) (F := F) (L := L)`.

Rewrite using `[← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `v`. Rewrite using `[he v]`. Use `congr 1`.

Conclude with `congrArg (fun n : ℕ => (n : ℤ)) (resDeg_addv (F := F) v).symm`.
-/
theorem norm_eq_places (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L),
          (letI := resAlg (F := F) w
           (Module.finrank (ResidueField ((vRing w).comap (algebraMap F L)))
             (ResidueField (vRing w)) : ℤ)) * WithTop.untopD 0 (w y)) * algebraMap O F u := by
  obtain ⟨u, hu, h⟩ := norm_eq_heightOne (F := F) y hy hϖ
  refine ⟨u, hu, ?_⟩
  rw [h]
  congr 2
  obtain ⟨e, he⟩ := placesOver_bij (O := O) (F := F) (L := L)
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e]
  apply finsum_congr
  intro v
  rw [he v]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℤ)) (resDeg_addv (F := F) v).symm

variable (O L) in
include F in

/- English proof (translation)
Take `⟨e, -⟩` from `placesOver_bij (O := O) (F := F) (L := L)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hinj : Function.Injective (algebraMap O L)`. Rewrite using `[IsScalarTower.algebraMap_eq O F L]`. Conclude with `(algebraMap F L).injective.comp (IsFractionRing.injective O F)`.

Take `⟨b, hbdef⟩ : ∃ b : integralClosure O L, b = algebraMap O (integralClosure O L) ϖ` from `⟨_, rfl⟩`. Establish `hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ`. Rewrite using `[hbdef]`. Conclude with `(IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm`. Establish `hb : b ≠ 0`.

Introduce `h0`. Establish `h00 : algebraMap O L ϖ = 0` using `by rw [← hbL, h0, map_zero]`. Conclude with `hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))`. Establish `hmem : ϖ ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit`. Establish `hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b}`.

Introduce `v`. Establish `h1` using `((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem`. Rewrite `h1` using `[← hbL, addv_count v b hb]`. Establish `h2 : 0 < Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))`. Break down `Nat.eq_zero_or_pos (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h` into its components or cases.

Rewrite `h1` using `[h, Nat.cast_zero]`. Conclude with `absurd h1 (lt_irrefl 0)`. Conclude with `h`. Conclude with `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)`. Establish `hspan : Ideal.span {b} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hb`. Establish `hfin` using `Ideal.finite_factors hspan`. Establish `hfin' : Finite (HeightOneSpectrum (integralClosure O L))`. Establish `huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} = Set.univ` using `Set.eq_univ_of_forall hdvd`.

Rewrite `hfin` using `[huniv]`. Conclude with `Set.finite_univ_iff.1 hfin`. Conclude with `Set.finite_coe_iff.1 (Finite.of_equiv _ e)`.
-/
theorem placesOver_finite : (PlacesOver O L).Finite := by
  obtain ⟨e, -⟩ := placesOver_bij (O := O) (F := F) (L := L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  obtain ⟨b, hbdef⟩ : ∃ b : integralClosure O L, b = algebraMap O (integralClosure O L) ϖ :=
    ⟨_, rfl⟩
  have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
    rw [hbdef]
    exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
  have hb : b ≠ 0 := by
    intro h0
    have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
    exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
    intro v
    have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
    rw [← hbL, addv_count v b hb] at h1
    have h2 : 0 < Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
      rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
      · rw [h, Nat.cast_zero] at h1
        exact absurd h1 (lt_irrefl 0)
      · exact h
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
  have hspan : Ideal.span {b} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb
  have hfin := Ideal.finite_factors hspan
  have hfin' : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} =
        Set.univ := Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e)

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
