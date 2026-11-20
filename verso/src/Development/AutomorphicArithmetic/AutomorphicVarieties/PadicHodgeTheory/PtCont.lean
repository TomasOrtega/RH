import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralOfNormBounded
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l])` using `(lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem ptc_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha`.
-/
private theorem ptc_norm_lt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (y : R →ₐ[ℤ_[l]] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field x a ha`.
-/
private theorem ptc_field {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    {K : Type} [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K) (a : R) (ha : a ∈ maximalIdeal R) :
    IsIntegral ℤ_[l] (x a) ∧ ∃ n : ℕ, ∃ b, IsIntegral ℤ_[l] b ∧ x a ^ n = (l : K) * b :=
  _root_.UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field x a ha

/- English proof (translation)
Take `⟨c, hc, hm⟩` from `hR a`. Use `(ptc_field x _ hm).1.add (hc.map x)` as an intermediate fact. Simplify using `using this`.
-/
private theorem ptc_field' {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R)
    {K : Type} [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K) (a : R) : IsIntegral ℤ_[l] (x a) := by
  obtain ⟨c, hc, hm⟩ := hR a
  have := (ptc_field x _ hm).1.add (hc.map x)
  simpa using this

/- English proof (translation)
Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B`. Use `haveI : IsNoetherianRing x.range := isNoetherianRing_of_surjective R _ x.rangeRestrict.toRingHom x.rangeRestrict_surjective`. Establish `hfin : ∀ m : MaximalSpectrum B, Module.Finite ℤ_[l] (integralClosure ℤ_[l] (B ⧸ m.asIdeal))` using `fun m => by haveI := m.isMaximal`. Use `letI := Ideal.Quotient.field m.asIdeal`. Conclude with `IsIntegralClosure.finite ℤ_[l] ℚ_[l] (B ⧸ m.asIdeal) _`.

Establish `hint : ∀ (m : MaximalSpectrum B) (z : x.range), ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp x.range.val) z ∈ integralClosure ℤ_[l] (B ⧸ m.asIdeal)`. Introduce and unpack `m ⟨_, a, rfl⟩`. Use `haveI := m.isMaximal`. Use `letI := Ideal.Quotient.field m.asIdeal`. Conclude with `ptc_field' hR ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp x) a`.

Set `g : x.range →ₐ[ℤ_[l]] ∀ m : MaximalSpectrum B, integralClosure ℤ_[l] (B ⧸ m.asIdeal)` to `Pi.algHom _ _ fun m => AlgHom.codRestrict _ _ (hint m)`. Use `haveI : Module.Finite ℤ_[l] g.range := Module.Finite.of_injective g.range.val.toLinearMap Subtype.val_injective`. Use `Module.finite_of_surjective_of_ker_le_nilradical g.rangeRestrict g.rangeRestrict_surjective ?_ (IsNoetherian.noetherian _)` and prove the remaining obligations. Introduce `z hz`. Establish `hz' : g z = 0` using `congrArg Subtype.val hz`.

Establish `hj : (z : B) ∈ Ideal.jacobson (⊥ : Ideal B)`. Rewrite using `[Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `I ⟨-, hI⟩`. Use `congrArg Subtype.val (congrFun hz' ⟨I, hI⟩)` as an intermediate fact. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this`.

Take `⟨n, hn⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := B)`. Use `⟨n, Subtype.ext ?_⟩` and prove the remaining obligations. Use `Ideal.pow_mem_pow hj n` as an intermediate fact. Rewrite `this` using `[hn]`. Simplify using `using this`.
-/
private theorem ptc_finite {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra ℤ_[l] R] (hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (x : R →ₐ[ℤ_[l]] B) : Module.Finite ℤ_[l] x.range := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : IsNoetherianRing x.range := isNoetherianRing_of_surjective R _ x.rangeRestrict.toRingHom
    x.rangeRestrict_surjective
  have hfin : ∀ m : MaximalSpectrum B, Module.Finite ℤ_[l] (integralClosure ℤ_[l] (B ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] (B ⧸ m.asIdeal) _
  have hint : ∀ (m : MaximalSpectrum B) (z : x.range),
      ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp x.range.val) z ∈ integralClosure ℤ_[l] (B ⧸ m.asIdeal) := by
    rintro m ⟨_, a, rfl⟩
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact ptc_field' hR ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp x) a
  let g : x.range →ₐ[ℤ_[l]] ∀ m : MaximalSpectrum B, integralClosure ℤ_[l] (B ⧸ m.asIdeal) :=
    Pi.algHom _ _ fun m => AlgHom.codRestrict _ _ (hint m)
  haveI : Module.Finite ℤ_[l] g.range :=
    Module.Finite.of_injective g.range.val.toLinearMap Subtype.val_injective
  refine Module.finite_of_surjective_of_ker_le_nilradical g.rangeRestrict g.rangeRestrict_surjective ?_
    (IsNoetherian.noetherian _)
  intro z hz
  have hz' : g z = 0 := congrArg Subtype.val hz
  have hj : (z : B) ∈ Ideal.jacobson (⊥ : Ideal B) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro I ⟨-, hI⟩
    have := congrArg Subtype.val (congrFun hz' ⟨I, hI⟩)
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  refine ⟨n, Subtype.ext ?_⟩
  have := Ideal.pow_mem_pow hj n
  rw [hn] at this
  simpa using this

/- English proof (translation)
Establish `h1 : (maximalIdeal R).map y ≤ (Ideal.span {(l : A)}).radical`. Rewrite using `[Ideal.radical_eq_sInf, le_sInf_iff]`. Introduce and unpack `P ⟨hP, hPp⟩`. Establish `hc : (P.comap (algebraMap ℤ_[l] A)).IsMaximal`. Establish `: maximalIdeal ℤ_[l] ≤ P.comap (algebraMap ℤ_[l] A)`.

Rewrite using `[PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]`. Use `show algebraMap ℤ_[l] A l ∈ P`. Rewrite using `[map_natCast]`. Conclude with `hP (Ideal.subset_span rfl)`. Rewrite using `[← (maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]`.

Use `infer_instance`. Use `haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hc`. Use `eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective y hy (K := P))` as an intermediate fact. Rewrite using `[Ideal.map_le_iff_le_comap, this]`. Take `⟨N, hN⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg h1 (Ideal.FG.map (IsNoetherian.noetherian _) y)`.

Use `⟨N, fun k a ha => ?_⟩` and prove the remaining obligations. Establish `h2` using `Ideal.mem_map_of_mem y ha`. Rewrite `h2` using `[Ideal.map_pow, pow_mul]`. Establish `h3` using `Ideal.pow_right_mono hN k h2`. Rewrite `h3` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Take `⟨b, hb⟩` from `h3`. Conclude with `⟨b, by rw [hb, Algebra.smul_def, map_pow, map_natCast]⟩`.
-/
private theorem ptc_pow {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Type} [CommRing A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (y : R →+* A) (hy : Function.Surjective y) :
    ∃ N : ℕ, ∀ k : ℕ, ∀ a ∈ maximalIdeal R ^ (N * k), ∃ b : A, y a = (l : ℤ_[l]) ^ k • b := by
  have h1 : (maximalIdeal R).map y ≤ (Ideal.span {(l : A)}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨hP, hPp⟩
    have hc : (P.comap (algebraMap ℤ_[l] A)).IsMaximal := by
      have : maximalIdeal ℤ_[l] ≤ P.comap (algebraMap ℤ_[l] A) := by
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
        show algebraMap ℤ_[l] A l ∈ P
        rw [map_natCast]
        exact hP (Ideal.subset_span rfl)
      rw [← (maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]
      infer_instance
    haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hc
    have := eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective y hy (K := P))
    rw [Ideal.map_le_iff_le_comap, this]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (Ideal.FG.map (IsNoetherian.noetherian _) y)
  refine ⟨N, fun k a ha => ?_⟩
  have h2 := Ideal.mem_map_of_mem y ha
  rw [Ideal.map_pow, pow_mul] at h2
  have h3 := Ideal.pow_right_mono hN k h2
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
  obtain ⟨b, hb⟩ := h3
  exact ⟨b, by rw [hb, Algebra.smul_def, map_pow, map_natCast]⟩

/- English proof (translation)
Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ_[l]) (M := A)`. Use `⟨∑ i, ‖φ (s i)‖, fun b => ?_⟩` and prove the remaining obligations. Establish `hb : b ∈ Submodule.span ℤ_[l] (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hb`. Rewrite using `[map_sum]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (c i))`.
-/
private theorem ptc_bdd {l : ℕ} [Fact l.Prime] {A : Type} [AddCommGroup A] [Module ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (φ : A →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, ∀ b, ‖φ b‖ ≤ C := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := A)
  refine ⟨∑ i, ‖φ (s i)‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hb
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, Algebra.smul_def, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (c i))

/- English proof (translation)
Take `⟨N, hN⟩` from `ptc_pow (l := l) y hy`. Take `⟨C, hC⟩` from `ptc_bdd φ`. Use `continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Establish `hl : ‖((l : ℕ) : ℚ_[l])‖ < 1` using `Padic.norm_p_lt_one`. Establish `ht` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const C`.

Rewrite `ht` using `[zero_mul]`. Take `⟨k, hk⟩` from `(ht.eventually (gt_mem_nhds hε)).exists`. Use `filter_upwards [(hf (N * k)).eventually_eq g] with g' hg'`. Take `⟨b, hb⟩` from `hN k _ (Ideal.Quotient.eq.1 hg')`. Rewrite using `[dist_eq_norm, ← map_sub, ← map_sub, hb, map_smul, Algebra.smul_def, map_pow, map_natCast, norm_mul, norm_pow]`.

Conclude with `lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hC b) (by positivity)) hk`.
-/
private theorem ptc_cont {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Type} [CommRing A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (y : R →+* A) (hy : Function.Surjective y) (φ : A →ₗ[ℤ_[l]] ℚ_[l])
    {X : Type} [TopologicalSpace X] (f : X → R) (hf : AdicCont (maximalIdeal R) f) :
    Continuous fun g => φ (y (f g)) := by
  obtain ⟨N, hN⟩ := ptc_pow (l := l) y hy
  obtain ⟨C, hC⟩ := ptc_bdd φ
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hl : ‖((l : ℕ) : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const C
  rw [zero_mul] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  filter_upwards [(hf (N * k)).eventually_eq g] with g' hg'
  obtain ⟨b, hb⟩ := hN k _ (Ideal.Quotient.eq.1 hg')
  rw [dist_eq_norm, ← map_sub, ← map_sub, hb, map_smul, Algebra.smul_def, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hC b) (by positivity)) hk

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ R _ _ _ B _ _ _ _ _ _ _ x`. Use `letI : Algebra ℤ_[l] R := ((algebraMap O R).comp (algebraMap ℤ_[l] O)).toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] O R := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R` using `fun a => by`. Take `⟨c, hc⟩` from `IsCO.res_surj (O := O) a`.

Conclude with `⟨_, (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) c).algebraMap, hc⟩`. Set `x' : R →ₐ[ℤ_[l]] B` to `x.restrictScalars ℤ_[l]`. Use `⟨fun X _ f hf => ?_, fun hB => ?_⟩` and prove the remaining obligations. Use `haveI := ptc_finite hR x'`. Use `letI : TopologicalSpace B := moduleTopology ℚ_[l] B`.

Use `haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩`. Use `haveI : ContinuousAdd B := IsModuleTopology.toContinuousAdd ℚ_[l] B`. Set `e` to `(Module.finBasis ℚ_[l] B).equivFun`. Establish `he : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`. Establish `h1 : Continuous fun g => e (x (f g))` using `continuous_pi fun i => ptc_cont x'.rangeRestrict.toRingHom x'.rangeRestrict_surjective ((((LinearMap.proj i).comp e.toLinearMap).restrictScalars ℤ_[l]).comp x'.range.val.toLinearMap) f hf`.

Establish `h2` using `he.comp h1`. Simplify `h2` using `[QCont, Function.comp_def]`. Use `letI := hB.toField`. Conclude with `⟨ptc_field' hR x', fun a ha => (ptc_field x' a ha).2⟩`.
-/
theorem UpperTheory.V.Loc.ptCont :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (x : R →ₐ[O] B), (∀ (X : Type) [TopologicalSpace X] (f : X → R), AdicCont (maximalIdeal R) f → QCont l fun g => x (f g)) ∧ (IsField B → (∀ a, IsIntegral ℤ_[l] (x a)) ∧ ∀ a ∈ maximalIdeal R, ∃ n : ℕ, ∃ b, IsIntegral ℤ_[l] b ∧ x a ^ n = (l : B) * b) := by
  intro l _ O _ _ _ _ _ _ _ R _ _ _ B _ _ _ _ _ _ _ x
  letI : Algebra ℤ_[l] R := ((algebraMap O R).comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R := fun a => by
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    exact ⟨_, (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) c).algebraMap, hc⟩
  let x' : R →ₐ[ℤ_[l]] B := x.restrictScalars ℤ_[l]
  refine ⟨fun X _ f hf => ?_, fun hB => ?_⟩
  · haveI := ptc_finite hR x'
    letI : TopologicalSpace B := moduleTopology ℚ_[l] B
    haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
    haveI : ContinuousAdd B := IsModuleTopology.toContinuousAdd ℚ_[l] B
    let e := (Module.finBasis ℚ_[l] B).equivFun
    have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    have h1 : Continuous fun g => e (x (f g)) := continuous_pi fun i =>
      ptc_cont x'.rangeRestrict.toRingHom x'.rangeRestrict_surjective
        ((((LinearMap.proj i).comp e.toLinearMap).restrictScalars ℤ_[l]).comp x'.range.val.toLinearMap) f hf
    have h2 := he.comp h1
    simpa [QCont, Function.comp_def] using h2
  · letI := hB.toField
    exact ⟨ptc_field' hR x', fun a ha => (ptc_field x' a ha).2⟩
