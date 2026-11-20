import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.ProdNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.IntCrit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfTwoHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetShalikaRigidityHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPlaceCompletionIsoImports
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

open scoped WithZero

namespace UpperTheory.V.Z.Int

/- English proof (translation)
Rewrite using `[(Valued.hasBasis_nhds_zero A ℤᵐ⁰).tendsto_right_iff]`. Introduce `γ _`. Establish `h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0` using `by simp`. Take `⟨N, hN⟩` from `exists_pow_lt₀ h (Units.mk0 _ h0)`. Use `filter_upwards [Filter.eventually_ge_atTop N] with k hk`.

Rewrite using `[Valuation.restrict_lt_iff_lt_embedding, map_pow]`. Conclude with `(pow_le_pow_right_of_le_one' h.le hk).trans_lt hN`.
-/
private theorem pow_tendsto {A : Type} [Field A] [Valued A ℤᵐ⁰] {x : A} (h : Valued.v x < 1) :
    Filter.Tendsto (fun k : ℕ => x ^ k) Filter.atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero A ℤᵐ⁰).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h (Units.mk0 _ h0)
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact (pow_le_pow_right_of_le_one' h.le hk).trans_lt hN

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun k : ℕ => (i x) ^ k) Filter.atTop (nhds 0)`. Establish `h2` using `(hi.tendsto 0).comp (pow_tendsto h)`. Simplify `h2` using `[Function.comp_def]`. Establish `h3` using `(Valued.hasBasis_nhds_zero C ℤᵐ⁰).mem_of_mem (i := 1) trivial`. Take `⟨k, hk⟩` from `(h1.eventually h3).exists`.

Assume the negation of the conclusion as `hc`. Establish `h4 : Valued.v ((i x) ^ k) < 1`. Establish `h5` using `hk`. Rewrite `h5` using `[Valuation.restrict_lt_iff_lt_embedding]`. Simplify using `using h5`.

Rewrite `h4` using `[map_pow]`. Conclude with `absurd h4 (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))`.
-/
private theorem map_lt_one {A C : Type} [Field A] [Field C] [Valued A ℤᵐ⁰] [Valued C ℤᵐ⁰] (i : A ≃+* C)
    (hi : Continuous i) {x : A} (h : Valued.v x < 1) : Valued.v (i x) < 1 := by
  have h1 : Filter.Tendsto (fun k : ℕ => (i x) ^ k) Filter.atTop (nhds 0) := by
    have h2 := (hi.tendsto 0).comp (pow_tendsto h)
    simpa [Function.comp_def] using h2
  have h3 := (Valued.hasBasis_nhds_zero C ℤᵐ⁰).mem_of_mem (i := 1) trivial
  obtain ⟨k, hk⟩ := (h1.eventually h3).exists
  by_contra hc
  have h4 : Valued.v ((i x) ^ k) < 1 := by
    have h5 := hk
    rw [Valuation.restrict_lt_iff_lt_embedding] at h5
    simpa using h5
  rw [map_pow] at h4
  exact absurd h4 (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hc'` using `not_le.1 hc`. Establish `h0 : x ≠ 0` using `fun e => by simp [e] at hc'`. Establish `h1 : Valued.v x⁻¹ < 1`. Rewrite using `[map_inv₀]`.

Conclude with `inv_lt_one_of_one_lt₀ hc'`. Establish `h2` using `map_lt_one i hi h1`. Rewrite `h2` using `[map_inv₀, map_inv₀]`. Establish `h3 : Valued.v (i x) ≠ 0` using `by simpa using h0`. Conclude with `absurd h2 (not_lt.2 ((one_le_inv₀ (zero_lt_iff.2 h3)).2 h))`.
-/
private theorem le_one_of_map {A C : Type} [Field A] [Field C] [Valued A ℤᵐ⁰] [Valued C ℤᵐ⁰] (i : A ≃+* C)
    (hi : Continuous i) {x : A} (h : Valued.v (i x) ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hc
  have hc' := not_le.1 hc
  have h0 : x ≠ 0 := fun e => by simp [e] at hc'
  have h1 : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hc'
  have h2 := map_lt_one i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h3 : Valued.v (i x) ≠ 0 := by simpa using h0
  exact absurd h2 (not_lt.2 ((one_le_inv₀ (zero_lt_iff.2 h3)).2 h))

/- English proof (translation)
Establish `hx` using `le_one_of_map i hi h.le`. Use `lt_of_le_of_ne hx fun e => ?_` and prove the remaining obligations. Establish `hip : Valued.v (i p) ≠ 0` using `by simpa using hp0`. Take `⟨k, hk⟩` from `exists_pow_lt₀ h (Units.mk0 _ hip)`. Establish `h1 : Valued.v (i (x ^ k / p)) ≤ 1`.

Rewrite using `[map_div₀, map_div₀, map_pow, map_pow]`. Conclude with `div_le_one_of_le₀ hk.le zero_le'`. Establish `h2` using `le_one_of_map i hi h1`. Rewrite `h2` using `[map_div₀, map_pow, e, one_pow]`. Establish `h3 : Valued.v p ≠ 0` using `by simpa using hp0`.

Rewrite `h2` using `[one_div]`. Conclude with `absurd hp (not_lt.2 ((inv_le_one₀ (zero_lt_iff.2 h3)).1 h2))`.
-/
private theorem lt_one_of_map {A C : Type} [Field A] [Field C] [Valued A ℤᵐ⁰] [Valued C ℤᵐ⁰] (i : A ≃+* C)
    (hi : Continuous i) {p : A} (hp0 : p ≠ 0) (hp : Valued.v p < 1) {x : A} (h : Valued.v (i x) < 1) :
    Valued.v x < 1 := by
  have hx := le_one_of_map i hi h.le
  refine lt_of_le_of_ne hx fun e => ?_
  have hip : Valued.v (i p) ≠ 0 := by simpa using hp0
  obtain ⟨k, hk⟩ := exists_pow_lt₀ h (Units.mk0 _ hip)
  have h1 : Valued.v (i (x ^ k / p)) ≤ 1 := by
    rw [map_div₀, map_div₀, map_pow, map_pow]
    exact div_le_one_of_le₀ hk.le zero_le'
  have h2 := le_one_of_map i hi h1
  rw [map_div₀, map_pow, e, one_pow] at h2
  have h3 : Valued.v p ≠ 0 := by simpa using hp0
  rw [one_div] at h2
  exact absurd hp (not_lt.2 ((inv_le_one₀ (zero_lt_iff.2 h3)).1 h2))

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hc'` using `not_le.1 hc`. Establish `h0 : x ≠ 0` using `fun e => by simp [e] at hc'`. Establish `h1 : Valued.v (i x⁻¹) < 1`. Rewrite using `[map_inv₀, map_inv₀]`.

Conclude with `inv_lt_one_of_one_lt₀ hc'`. Establish `h2` using `lt_one_of_map i hi hp0 hp h1`. Rewrite `h2` using `[map_inv₀]`. Establish `h3 : Valued.v x ≠ 0` using `by simpa using h0`. Conclude with `absurd h (not_le.2 ((inv_lt_one₀ (zero_lt_iff.2 h3)).1 h2))`.
-/
private theorem map_le_one {A C : Type} [Field A] [Field C] [Valued A ℤᵐ⁰] [Valued C ℤᵐ⁰] (i : A ≃+* C)
    (hi : Continuous i) {p : A} (hp0 : p ≠ 0) (hp : Valued.v p < 1) {x : A} (h : Valued.v x ≤ 1) :
    Valued.v (i x) ≤ 1 := by
  by_contra hc
  have hc' := not_le.1 hc
  have h0 : x ≠ 0 := fun e => by simp [e] at hc'
  have h1 : Valued.v (i x⁻¹) < 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hc'
  have h2 := lt_one_of_map i hi hp0 hp h1
  rw [map_inv₀] at h2
  have h3 : Valued.v x ≠ 0 := by simpa using h0
  exact absurd h (not_le.2 ((inv_lt_one₀ (zero_lt_iff.2 h3)).1 h2))

/- English proof (translation)
Use `open GroundTheory.Global.SemiLocal in`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Establish `hp0 : algebraMap (𝓞 F) (v.adicCompletion F) a ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Simplify using `using ha0`.

Establish `hp` using `(valued_algebraMap_int_lt_one_iff v a).2 ha`. Establish `hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))`. Rewrite using `[hl.over]`. Set `g` to `Ideal.quotientMap w.asIdeal (algebraMap (𝓞 F) (𝓞 K)) hle`. Use `letI := Ideal.Quotient.field v.asIdeal`.

Establish `hinj : Function.Injective g` using `g.injective`. Establish `hsurj : Function.Surjective g`. Introduce `y`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `e1 : Valued.v (i (i.symm (algebraMap (𝓞 K) (w.adicCompletion K) y))) ≤ 1`.

Simplify using `using valued_algebraMap_int_le_one w y`. Take `⟨r, hr⟩` from `exists_int_valued_sub_lt_one v _ (le_one_of_map i hi e1)`. Use `⟨Ideal.Quotient.mk _ r, ?_⟩` and prove the remaining obligations. Establish `e2` using `map_lt_one i hi hr`. Rewrite `e2` using `[map_sub, RingEquiv.apply_symm_apply, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), hloc]`.

Establish `e3 : algebraMap K (w.adicCompletion K) (algebraMap F K (r : F)) = algebraMap (𝓞 K) (w.adicCompletion K) (algebraMap (𝓞 F) (𝓞 K) r)`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) K (w.adicCompletion K)]`. Both sides reduce to the same expression. Rewrite `e2` using `[e3, ← map_sub, valued_algebraMap_int_lt_one_iff]`. Rewrite using `[Ideal.quotientMap_mk]`.

Conclude with `(Ideal.Quotient.eq.2 e2).symm`. Conclude with `(Nat.card_eq_of_bijective g ⟨hinj, hsurj⟩).symm`.
-/
private theorem normV_eq_of_iso {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [hl : w.asIdeal.LiesOver v.asIdeal]
    (i : v.adicCompletion F ≃+* w.adicCompletion K) (hi : Continuous i)
    (hloc : ∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) : normV w = normV v := by
  open GroundTheory.Global.SemiLocal in
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0 : algebraMap (𝓞 F) (v.adicCompletion F) a ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    simpa using ha0
  have hp := (valued_algebraMap_int_lt_one_iff v a).2 ha
  have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [hl.over]
  let g := Ideal.quotientMap w.asIdeal (algebraMap (𝓞 F) (𝓞 K)) hle
  letI := Ideal.Quotient.field v.asIdeal
  have hinj : Function.Injective g := g.injective
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have e1 : Valued.v (i (i.symm (algebraMap (𝓞 K) (w.adicCompletion K) y))) ≤ 1 := by
      simpa using valued_algebraMap_int_le_one w y
    obtain ⟨r, hr⟩ := exists_int_valued_sub_lt_one v _ (le_one_of_map i hi e1)
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    have e2 := map_lt_one i hi hr
    rw [map_sub, RingEquiv.apply_symm_apply, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), hloc] at e2
    have e3 : algebraMap K (w.adicCompletion K) (algebraMap F K (r : F)) =
        algebraMap (𝓞 K) (w.adicCompletion K) (algebraMap (𝓞 F) (𝓞 K) r) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K (w.adicCompletion K)]
      rfl
    rw [e3, ← map_sub, valued_algebraMap_int_lt_one_iff] at e2
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 e2).symm
  exact (Nat.card_eq_of_bijective g ⟨hinj, hsurj⟩).symm

/- English proof (translation)
Establish `hW : ∀ lo hi : ℤ, (∀ i, lo ≤ m i ∧ m i ≤ hi) → ∀ τ, Within n (inf τ) lo hi`. Introduce `lo hi hb τ z hz`. Rewrite `hz` using `[hinf]`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hz`. Conclude with `⟨m i, rfl, (hb i).1, (hb i).2⟩`.

Take `⟨c, hc⟩` from `(Set.finite_range m).bddBelow`. Take `⟨d, hd⟩` from `(Set.finite_range m).bddAbove`. Establish `hp : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℤ), ∏ τ ∈ Ov ι u, nu ι (τ (unif u : K)) ^ a = nu ι (normV u : ℂ) ^ a`. Introduce `l _ ι a`. Rewrite using `[Finset.prod_zpow, (prodNorm l ι K u).2]`.

Introduce `b hb`. Use `⟨fun a ha => UpperTheory.V.Lib.isIntegral_of_norm_le _ fun l _ ι => ?_, fun a ha => UpperTheory.V.Lib.isIntegral_of_norm_le _ fun l _ ι => ?_⟩` and prove the remaining obligations. Establish `h1` using `(h l ι (fun _ => -a) (fun _ => d) (fun τ => hW (-a) d (fun i => ⟨ha i, hd ⟨i, rfl⟩⟩) τ) b hb).2`. Unfold `Bnd at h1`. Simplify using `only [neg_neg] at h1`.

Rewrite `h1` using `[hp]`. Simplify `h1` using `[nu, mul_comm]`. Establish `h1` using `(h l ι (fun _ => c) (fun _ => a) (fun τ => hW c a (fun i => ⟨hc ⟨i, rfl⟩, ha i⟩) τ) b hb).1`. Unfold `Bnd at h1`. Rewrite `h1` using `[hp]`.

Simplify `h1` using `[nu, mul_comm]`.
-/
private theorem slopesIn_of_slope {K : Type} [Field K] [NumberField K] {n : ℕ} (m : Fin n → ℤ)
    (u : HeightOneSpectrum (𝓞 K)) (inf : (K →+* ℂ) → Multiset ℂ) (hinf : ∀ τ, inf τ = infOf m)
    (B : Multiset ℂˣ) (h : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), Slope ι n u inf B) :
    SlopesIn (normV u) m (algSat n (normV u) B) := by
  have hW : ∀ lo hi : ℤ, (∀ i, lo ≤ m i ∧ m i ≤ hi) → ∀ τ, Within n (inf τ) lo hi := by
    intro lo hi hb τ z hz
    rw [hinf] at hz
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, rfl, (hb i).1, (hb i).2⟩
  obtain ⟨c, hc⟩ := (Set.finite_range m).bddBelow
  obtain ⟨d, hd⟩ := (Set.finite_range m).bddAbove
  have hp : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℤ),
      ∏ τ ∈ Ov ι u, nu ι (τ (unif u : K)) ^ a = nu ι (normV u : ℂ) ^ a := by
    intro l _ ι a
    rw [Finset.prod_zpow, (prodNorm l ι K u).2]
  intro b hb
  refine ⟨fun a ha => UpperTheory.V.Lib.isIntegral_of_norm_le _ fun l _ ι => ?_,
    fun a ha => UpperTheory.V.Lib.isIntegral_of_norm_le _ fun l _ ι => ?_⟩
  · have h1 := (h l ι (fun _ => -a) (fun _ => d)
      (fun τ => hW (-a) d (fun i => ⟨ha i, hd ⟨i, rfl⟩⟩) τ) b hb).2
    unfold Bnd at h1
    simp only [neg_neg] at h1
    rw [hp] at h1
    simpa [nu, mul_comm] using h1
  · have h1 := (h l ι (fun _ => c) (fun _ => a)
      (fun τ => hW c a (fun i => ⟨hc ⟨i, rfl⟩, ha i⟩) τ) b hb).1
    unfold Bnd at h1
    rw [hp] at h1
    simpa [nu, mul_comm] using h1

end UpperTheory.V.Z.Int

/- English proof (translation)
Introduce `hQL hS E _ _ _ n hn m hm π hinf ⟨χ, hpol⟩ w B hB`. Establish `hAF` using `GlobalTheory.automorphicFormsFiniteGL`. Establish `hJS` using `GlobalTheory.JSW.jacquetShalikaRigidity_holds`. Establish `hGK` using `GlobalTheory.GelfandKazhdanTop.gelfandKazhdanDual_of_jacquetShalika (PositivityTheory.JacquetShalikaLocal.jacquetShalika_of hJS) hAF`. Establish `hic : ∀ τ, (CG.mk π).infChar τ = infOf m` using `fun τ => CG.HasInfChar.infChar_eq (hinf τ)`.

Establish `hreg : (CG.mk π).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Rewrite using `[hic]`. Use `⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `add_left_cancel e` after adjusting the coercions. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hz`.

Conclude with `⟨m i, add_comm _ _⟩`. Take `⟨Q, hQ1, hQ2, hQ3, hQ4⟩` from `(GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split hAF E (AlgebraicClosure E) 2 n π w).nonempty`. Take `⟨P, hP⟩` from `hQL E Q.K Q.two n hn π hQ3`. Take `⟨⟨χ', hχ'⟩, -⟩` from `GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight hAF hJS hGK E Q.K 2 n hn π χ P hP ⟨hreg, hpol, trivial⟩`. Establish `hin : GlobalTheory.GalCut.InScope .good 2 P χ'` using `⟨hχ'.1, hχ'.2.1, hQ4 P hP⟩`.

Establish `hA` using `ReciprocityTheory.Gal.isPlaceOver_placeOf (AlgebraicClosure E) w`. Take `⟨w', h', i, hi⟩` from `GlobalTheory.T.exists_place_completion_iso E (AlgebraicClosure E) Q.K w _ hA (hQ1 _ hA)`. Establish `hund : w'.under (𝓞 E) = w`. Use `GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'` as an intermediate fact. Use `ext1`.

Conclude with `this.over.symm`. Establish `hlo` using `GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'`. Establish `hq` using `normV_eq_of_iso w w' i hi.cont hi.loc`. Establish `hsat : (CG.mk P).HasSat w' B`. Establish `h1` using `hP.sat w' 1 B (by rw [hund, pow_one, hq]) (by rw [hund]; exact hB)`.

Simplify using `using h1`. Establish `hinf' : ∀ τ, (CG.mk P).infChar τ = infOf m` using `fun τ => by rw [hP.inf, hic]`. Establish `hfin` using `slopesIn_of_slope m w' _ hinf' B fun l _ ι => hS l ι Q.K 2 n Nat.prime_two hn P χ' hin w' (hQ2 w' hund) B hsat`. Rewrite `hfin` using `[hq]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.Int.slopeAllOf :
    GlobalTheory.GalCut.QuadLift → UpperTheory.V.Z.Int.SlopeOn .good → UpperTheory.V.Z.Int.SlopeAll := by
  intro hQL hS E _ _ _ n hn m hm π hinf ⟨χ, hpol⟩ w B hB
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  have hJS := GlobalTheory.JSW.jacquetShalikaRigidity_holds
  have hGK := GlobalTheory.GelfandKazhdanTop.gelfandKazhdanDual_of_jacquetShalika (PositivityTheory.JacquetShalikaLocal.jacquetShalika_of hJS) hAF
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := (GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split hAF E (AlgebraicClosure E) 2 n π w).nonempty
  obtain ⟨P, hP⟩ := hQL E Q.K Q.two n hn π hQ3
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight hAF hJS hGK E Q.K 2 n hn π χ P hP ⟨hreg, hpol, trivial⟩
  have hin : GlobalTheory.GalCut.InScope .good 2 P χ' := ⟨hχ'.1, hχ'.2.1, hQ4 P hP⟩
  have hA := ReciprocityTheory.Gal.isPlaceOver_placeOf (AlgebraicClosure E) w
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso E (AlgebraicClosure E) Q.K w _ hA (hQ1 _ hA)
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  have hlo := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
  have hq := normV_eq_of_iso w w' i hi.cont hi.loc
  have hsat : (CG.mk P).HasSat w' B := by
    have h1 := hP.sat w' 1 B (by rw [hund, pow_one, hq]) (by rw [hund]; exact hB)
    simpa using h1
  have hinf' : ∀ τ, (CG.mk P).infChar τ = infOf m := fun τ => by rw [hP.inf, hic]
  have hfin := slopesIn_of_slope m w' _ hinf' B fun l _ ι =>
    hS l ι Q.K 2 n Nat.prime_two hn P χ' hin w' (hQ2 w' hund) B hsat
  rwa [hq] at hfin
