import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ResOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
open UpperTheory.V.W (Plc Lp resP)

/- English proof (translation)
Use `haveI := IsAlgClosure.isAlgClosed (R := ℚ) (K := Ω)`. Establish `hi : IsIntegral ℚ (j' x)` using `(Algebra.IsIntegral.isIntegral (R := ℚ) x).map j'.toRatAlgHom`. Take `⟨y, hy⟩` from `hi.mem_range_algHom_of_minpoly_splits (K := Ω) (IsAlgClosed.splits _) j.toRatAlgHom`. Conclude with `⟨y, hy⟩`.
-/
private theorem emb_le {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j j' : Ω →+* ℂ) (x : Ω) : ∃ y, j y = j' x := by
  haveI := IsAlgClosure.isAlgClosed (R := ℚ) (K := Ω)
  have hi : IsIntegral ℚ (j' x) := (Algebra.IsIntegral.isIntegral (R := ℚ) x).map j'.toRatAlgHom
  obtain ⟨y, hy⟩ := hi.mem_range_algHom_of_minpoly_splits (K := Ω) (IsAlgClosed.splits _) j.toRatAlgHom
  exact ⟨y, hy⟩

/- English proof (translation)
Establish `hr : j.fieldRange = j'.fieldRange`. Use extensionality with `z`. Simplify using `only [RingHom.mem_fieldRange]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `emb_le j' j x`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `emb_le j j' x`. Set `e : Ω ≃+* Ω` to `j.rangeRestrictFieldEquiv.trans ((RingEquiv.subfieldCongr hr).trans j'.rangeRestrictFieldEquiv.symm)`. Use `⟨AlgEquiv.ofRingEquiv (f := e) (fun q => by simp), fun x => ?_⟩` and prove the remaining obligations.

Establish `h1` using `j'.rangeRestrictFieldEquiv.apply_symm_apply (RingEquiv.subfieldCongr hr (j.rangeRestrictFieldEquiv x))`. Conclude with `congrArg Subtype.val h1`.
-/
private theorem emb_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j j' : Ω →+* ℂ) :
    ∃ τ : G ℚ Ω, ∀ x, j' (τ x) = j x := by
  have hr : j.fieldRange = j'.fieldRange := by
    ext z
    simp only [RingHom.mem_fieldRange]
    constructor
    · rintro ⟨x, rfl⟩
      exact emb_le j' j x
    · rintro ⟨x, rfl⟩
      exact emb_le j j' x
  let e : Ω ≃+* Ω := j.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr hr).trans j'.rangeRestrictFieldEquiv.symm)
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun q => by simp), fun x => ?_⟩
  have h1 := j'.rangeRestrictFieldEquiv.apply_symm_apply
    (RingEquiv.subfieldCongr hr (j.rangeRestrictFieldEquiv x))
  exact congrArg Subtype.val h1

/- English proof (translation)
Take `⟨j, hj⟩` from `h`. Take `⟨j', hj'⟩` from `h'`. Take `⟨τ, hτ⟩` from `emb_eq j j'`. Establish `h1 : c' * τ = τ * c`. Use extensionality with `x`.

Apply `j'.injective` to reduce the goal to its premises. Use `show j' (c' (τ x)) = j' (τ (c x))`. Rewrite using `[hj', hτ, hτ, hj]`. Establish `key : c' = τ * c * τ⁻¹`. Rewrite using `[← h1, mul_inv_cancel_right]`.

Rewrite using `[key, map_mul, map_mul, mul_comm (χ τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`.
-/
private theorem cc_val {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {χ : G ℚ Ω →* (Qbar l)ˣ} {c c' : G ℚ Ω}
    (h : Sd.IsCC c) (h' : Sd.IsCC c') : χ c' = χ c := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨j', hj'⟩ := h'
  obtain ⟨τ, hτ⟩ := emb_eq j j'
  have h1 : c' * τ = τ * c := by
    ext x
    apply j'.injective
    show j' (c' (τ x)) = j' (τ (c x))
    rw [hj', hτ, hτ, hj]
  have key : c' = τ * c * τ⁻¹ := by
    rw [← h1, mul_inv_cancel_right]
  rw [key, map_mul, map_mul, mul_comm (χ τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

/- English proof (translation)
Unfold `cycBar`. Rewrite using `[MonoidHom.coe_comp]`. Use `Continuous.comp (Continuous.units_map _ ?_) (continuous_cycZ F Ω l)` and prove the remaining obligations. Conclude with `(continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val`.
-/
private theorem cont_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) := by
  unfold cycBar
  rw [MonoidHom.coe_comp]
  refine Continuous.comp (Continuous.units_map _ ?_) (continuous_cycZ F Ω l)
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val

/- English proof (translation)
Rewrite using `[continuous_def]`. Introduce `U _`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `x hx`. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (γ.ker : Set Γ), ?_, h.preimage (continuous_const.mul continuous_id), ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Establish `hk : γ (x⁻¹ * y) = 1` using `hy`. Establish `: γ y = γ x`. Rewrite `hk` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `hk.symm`.

Use `show γ y ∈ U`. Rewrite using `[this]`. Conclude with `hx`. Use `show γ (x⁻¹ * x) = 1`. Simplify using the standard rewrite rules.
-/
private theorem cont_of_ker {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B] [TopologicalSpace B]
    (γ : Γ →* B) (h : IsOpen (γ.ker : Set Γ)) : Continuous γ := by
  rw [continuous_def]
  intro U _
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (γ.ker : Set Γ), ?_, h.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro y hy
    have hk : γ (x⁻¹ * y) = 1 := hy
    have : γ y = γ x := by
      rw [map_mul, map_inv, inv_mul_eq_one] at hk
      exact hk.symm
    show γ y ∈ U
    rw [this]
    exact hx
  · show γ (x⁻¹ * x) = 1
    simp

/- English proof (translation)
Use `haveI : Finite (G ℚ Ω ⧸ χ.ker) := χ.ker.quotient_finite_of_isOpen h`. Use `haveI : χ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Use `⟨χ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `χ.ker.pow_index_mem g`.
-/
private theorem exists_exp {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (χ : G ℚ Ω →* (Qbar l)ˣ)
    (h : IsOpen (χ.ker : Set (G ℚ Ω))) : ∃ n : ℕ, 0 < n ∧ ∀ g, χ g ^ n = 1 := by
  haveI : Finite (G ℚ Ω ⧸ χ.ker) := χ.ker.quotient_finite_of_isOpen h
  haveI : χ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨χ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun g => ?_⟩
  rw [← map_pow]
  exact χ.ker.pow_index_mem g

/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Use `push_cast`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hl ((A.valuation_le_one_iff _).mpr (natCast_mem A m))`.
-/
private theorem val_of_dvd {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) {l M : ℕ} (h : l ∣ M)
    (hl : A.valuation (l : Ω) < 1) : A.valuation (M : Ω) < 1 := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [map_mul]
  exact mul_lt_one_of_lt_of_le hl ((A.valuation_le_one_iff _).mpr (natCast_mem A m))

/- English proof (translation)
Set `p : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L) → Prop` to `fun w u => u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))`. Set `e : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L)` to `fun w => @Classical.epsilon _ ⟨w⟩ (p w)`. Establish `he : ∀ w, (e w).under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))` using `fun w => Classical.epsilon_spec (p := p w) ⟨w, rfl⟩`. Establish `hcongr : ∀ u w, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → e u = e w`. Introduce `u w h`.

Establish `hp : p u = p w`. Use function extensionality and compare the values at `v`. Simplify using `only [p, h]`. Use `show @Classical.epsilon _ ⟨u⟩ (p u) = @Classical.epsilon _ ⟨w⟩ (p w)`. Rewrite using `[hp]`.

Use `⟨{w | w = e w}, fun w hw => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hmem : w = e w`. Take `⟨u, hu, hus⟩` from `hU.split w hw`. Use `⟨u, hu, hus, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`.

Use `⟨fun _ h2 => hu ?_, fun _ => hmem⟩` and prove the remaining obligations. Rewrite using `[h2, hcongr u w hus, ← hmem]`. Use `⟨e w, fun h => hmem h.symm, he w, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨fun h => absurd h hmem, fun h => absurd (hcongr (e w) w (he w)).symm h⟩`.
-/
private theorem exists_type {L : Type} [Field L] [NumberField L] [IsCMField L] {M : ℕ} (hU : Z.Sym.UnrSplit L M) :
    ∃ Φ : Set (HeightOneSpectrum (𝓞 L)), Tw.IsType (Lp L) M Φ := by
  let p : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L) → Prop := fun w u =>
    u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  let e : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L) := fun w =>
    @Classical.epsilon _ ⟨w⟩ (p w)
  have he : ∀ w, (e w).under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := fun w =>
    Classical.epsilon_spec (p := p w) ⟨w, rfl⟩
  have hcongr : ∀ u w, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → e u = e w := by
    intro u w h
    have hp : p u = p w := by
      funext v
      simp only [p, h]
    show @Classical.epsilon _ ⟨u⟩ (p u) = @Classical.epsilon _ ⟨w⟩ (p w)
    rw [hp]
  refine ⟨{w | w = e w}, fun w hw => ?_⟩
  by_cases hmem : w = e w
  · obtain ⟨u, hu, hus⟩ := hU.split w hw
    refine ⟨u, hu, hus, ?_⟩
    simp only [Set.mem_setOf_eq]
    refine ⟨fun _ h2 => hu ?_, fun _ => hmem⟩
    rw [h2, hcongr u w hus, ← hmem]
  · refine ⟨e w, fun h => hmem h.symm, he w, ?_⟩
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => absurd h hmem, fun h => absurd (hcongr (e w) w (he w)).symm h⟩

/- English proof (translation)
Introduce `g hg`. Distinguish the cases in `hA : A = ⊤`. Use `haveI : IsAlgClosure (Lp L) Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans (Lp L) L Ω⟩`. Rewrite `hg` using `[((Base.places (Lp L) Ω l A).2.1 hA).1, Subgroup.mem_bot]`. Rewrite using `[hg]`.

Conclude with `Subgroup.one_mem _`. Take `⟨w, hw⟩` from `(Base.places L Ω l A).1 hA`. Establish `hin : CF.resTo (Lp L) L Ω g ∈ Ideal.inertia Gal(L/Lp L) w.asIdeal`. Rewrite using `[← CF.ineAbs (Lp L) L Ω A w hw]`. Conclude with `Subgroup.mem_map_of_mem _ hg`.

Establish `hcard` using `CF.ineCard.1 (Lp L) L w`. Use `haveI := hU w`. Rewrite `hcard` using `[Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, Subgroup.card_eq_one]`. Rewrite `hin` using `[hcard, Subgroup.mem_bot]`. Establish `hk : g ∈ (CF.resTo (Lp L) L Ω).ker` using `hin`.

Rewrite `hk` using `[← CF.range_relIncl]`. Conclude with `hk`.
-/
private theorem ine_range {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime]
    (hU : ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal) (A : ValuationSubring Ω) :
    Ine (F := Lp L) A ≤ (resP L Ω).range := by
  intro g hg
  by_cases hA : A = ⊤
  · haveI : IsAlgClosure (Lp L) Ω :=
      ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans (Lp L) L Ω⟩
    rw [((Base.places (Lp L) Ω l A).2.1 hA).1, Subgroup.mem_bot] at hg
    rw [hg]
    exact Subgroup.one_mem _
  · obtain ⟨w, hw⟩ := (Base.places L Ω l A).1 hA
    have hin : CF.resTo (Lp L) L Ω g ∈ Ideal.inertia Gal(L/Lp L) w.asIdeal := by
      rw [← CF.ineAbs (Lp L) L Ω A w hw]
      exact Subgroup.mem_map_of_mem _ hg
    have hcard := CF.ineCard.1 (Lp L) L w
    haveI := hU w
    rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, Subgroup.card_eq_one] at hcard
    rw [hcard, Subgroup.mem_bot] at hin
    have hk : g ∈ (CF.resTo (Lp L) L Ω).ker := hin
    rw [← CF.range_relIncl] at hk
    exact hk

/- English proof (translation)
Take `⟨j, hj⟩` from `hc`. Use `show ∀ x : Lp L, c (algebraMap (Lp L) Ω x) = algebraMap (Lp L) Ω x`. Introduce `x`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hj]`.

Conclude with `x.2 (j.comp (algebraMap L Ω))`.
-/
private theorem cc_real {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∈ galOf ℚ (Lp L) Ω := by
  obtain ⟨j, hj⟩ := hc
  show ∀ x : Lp L, c (algebraMap (Lp L) Ω x) = algebraMap (Lp L) Ω x
  intro x
  apply j.injective
  rw [hj]
  exact x.2 (j.comp (algebraMap L Ω))

/- English proof (translation)
Take `⟨j, hj⟩` from `hc`. Introduce `hmem`. Establish `hfix : ∀ x : L, c (algebraMap L Ω x) = algebraMap L Ω x` using `hmem`. Establish `hreal : ComplexEmbedding.IsReal (j.comp (algebraMap L Ω))`. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `show (starRingEnd ℂ) (j (algebraMap L Ω x)) = j (algebraMap L Ω x)`. Rewrite using `[← hj, hfix x]`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) (InfinitePlace.isReal_mk_iff.mpr hreal)`.
-/
private theorem cc_not_mem {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [Algebra L Ω]
    {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ L Ω := by
  obtain ⟨j, hj⟩ := hc
  intro hmem
  have hfix : ∀ x : L, c (algebraMap L Ω x) = algebraMap L Ω x := hmem
  have hreal : ComplexEmbedding.IsReal (j.comp (algebraMap L Ω)) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    show (starRingEnd ℂ) (j (algebraMap L Ω x)) = j (algebraMap L Ω x)
    rw [← hj, hfix x]
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _))
    (InfinitePlace.isReal_mk_iff.mpr hreal)

/- English proof (translation)
Introduce `hTWM hAlg L Ω _ _ _ _ _ _ _ l _ hl2 ι c hc M hM0 hlM hU χ a hχo hχc hχM`. Use `haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩`. Use `haveI : IsAlgClosure (Lp L) Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) (Lp L)⟩`. Establish `h2 : Module.finrank (Lp L) L = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hM3 : 3 ≤ M`.

Establish `h2l : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hlM' : l ≤ M` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hlM`. Use linear arithmetic over natural numbers and integers. Establish `hχcont : Continuous χ` using `cont_of_ker χ hχo`. Take `⟨n, hn, hχn⟩` from `exists_exp χ hχo`.

Take `⟨Φ, hΦ⟩` from `exists_type hU`. Set `ν : G (Lp L) Ω →* (Qbar l)ˣ` to `cycBar (Lp L) Ω l ^ a * χ.comp (galEmb ℚ (Lp L) Ω)`. Establish `hν : ∀ s, ν s = cycBar (Lp L) Ω l s ^ a * χ (galEmb ℚ (Lp L) Ω s)` using `fun s => rfl`. Establish `hνc : Continuous ν` using `((cont_cyc _ Ω l).zpow a).mul (hχcont.comp (continuous_restrictScalarsHom ℚ (Lp L) Ω))`. Establish `hνconj : ∀ g : G (Lp L) Ω, IsConjEl g → ν g = 1`.

Introduce `g hg`. Take `⟨j, hj⟩` from `hg`. Establish `hcc : Sd.IsCC (galEmb ℚ (Lp L) Ω g)` using `⟨j, hj⟩`. Establish `e1 : χ (galEmb ℚ (Lp L) Ω g) = (-1) ^ a` using `(cc_val hc hcc).trans hχc`. Establish `e0` using `IsConjOm.cyc (E := Lp L) (Ω := Ω) (l := l) (σ := MulSemiringAction.toRingAut (G (Lp L) Ω) Ω g) ⟨j, hj⟩`.

Establish `e2 : cycBar (Lp L) Ω l g = -1`. Unfold `cycBar cycZ`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, e0]`. Use `ext`. Simplify using the standard rewrite rules.

Rewrite using `[hν, e1, e2, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]`. Establish `hνunr : ∀ (v : HeightOneSpectrum (𝓞 (Lp L))) (A : ValuationSubring Ω), IsPlaceOver A v → ↑M ∉ v.asIdeal → ∀ s ∈ Ine A, ν s = 1`. Introduce `v A hA hMv s hs`. Establish `hAM : ¬ A.valuation (M : Ω) < 1` using `fun h => hMv ((Pr.natCast_place hA M).1 h)`. Establish `hAl : ¬ A.valuation (l : Ω) < 1` using `fun h => hAM (val_of_dvd A hlM h)`.

Establish `hcy : cycZ (Lp L) Ω l s = 1` using `(Base.places (Lp L) Ω l A).2.2.2 hAl hs`. Establish `hcb : cycBar (Lp L) Ω l s = 1`. Unfold `cycBar`. Rewrite using `[MonoidHom.comp_apply, hcy, map_one]`. Take `⟨t, rfl⟩` from `ine_range l hU.unr A hs`.

Establish `ht : t ∈ Ine A` using `hs`. Rewrite using `[hν, hcb, one_zpow, one_mul]`. Conclude with `hχM A hAM t ht`. Take `⟨κ, hκc, hV, k, hk, hκ⟩` from `hTWM (Lp L) L Ω inferInstance h2 l M hM3 Φ hΦ ν hνc hνconj hνunr`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : c ∈ (galEmb ℚ (Lp L) Ω).range := by`.

Rewrite using `[range_galEmb]`. Conclude with `cc_real hc`. Establish `hgn : g ∉ (resG (Lp L) L Ω).range`. Introduce and unpack `⟨t, rfl⟩`. Apply `cc_not_mem (L := L) hc` to reduce the goal to its premises.

Rewrite using `[← hg]`. Conclude with `galEmb_mem ℚ L Ω t`. Establish `hinj : ∀ x y : G (Lp L) Ω, galEmb ℚ (Lp L) Ω x = galEmb ℚ (Lp L) Ω y → x = y` using `fun x y h => AlgEquiv.ext fun z => DFunLike.congr_fun h z`. Establish `hconj : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ → resG (Lp L) L Ω s' = g * resG (Lp L) L Ω s * g⁻¹`. Introduce `s s' h`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_inv, hg]`. Conclude with `h`. Establish `hnorm : (resG (Lp L) L Ω).range.Normal` using `Subgroup.normal_of_index_eq_two (by rw [(Tw.resOpen (Lp L) L Ω).2, h2])`. Establish `hloc : ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w → (M : 𝓞 L) ∈ w.asIdeal → ∃ b : ℤ, ∀ s ∈ Ine A, κ s ^ (k * n) = (cycBar L Ω l s ^ b) ^ (k * n)`.

Introduce `w A hA hMw`. Distinguish the cases in `hw : w ∈ Φ`. Use `⟨a, fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨w', hne, hund, hiff⟩` from `hΦ w hMw`. Establish `hw' : w' ∉ Φ` using `hiff.1 hw`.

Take `⟨A', hA', hcA⟩` from `Tw.conjPlace (Lp L) L Ω h2 g hgn w w' A hA hne hund`. Take `⟨s', hs'⟩ : g * resG (Lp L) L Ω s * g⁻¹ ∈ (resG (Lp L) L Ω).range` from `hnorm.conj_mem _ ⟨s, rfl⟩ g`. Establish `hs'I : s' ∈ Ine A'` using `(hcA s s' hs').1 hs`. Establish `e1 : κ s' ^ k = 1` using `(hκ w' A' hA' s' hs'I).2 hw'`. Establish `e2 : κ s * κ s' = cycBar L Ω l s ^ a * χ (galEmb ℚ L Ω s)` using `(hV g hgn).1 s s' hs'`.

Establish `e3 : κ s = cycBar L Ω l s ^ a * χ (galEmb ℚ L Ω s) * (κ s')⁻¹` using `eq_mul_inv_of_mul_eq e2`. Establish `e4 : χ (galEmb ℚ L Ω s) ^ n = 1` using `hχn _`. Rewrite using `[e3, mul_pow, mul_pow, inv_pow, pow_mul (κ s') k n, e1, one_pow, inv_one, mul_one, mul_comm k n, pow_mul (χ _) n k, e4, one_pow, mul_one]`. Use `⟨0, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e1 : κ s ^ k = 1` using `(hκ w A hA s hs).2 hw`.

Rewrite using `[zpow_zero, one_pow, pow_mul, e1, one_pow]`. Establish `hMl : ∀ w : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal`. Introduce `w hlw`. Take `⟨m, hm⟩` from `hlM`. Rewrite using `[hm, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hlw`. Use `⟨κ, ?_, fun s s' h => (hV g hgn).1 s s' (hconj s s' h), ?_, ?_⟩` and prove the remaining obligations. Take `⟨χ', hc', art, a', e1, e2, e3⟩` from `(hAlg L Ω l ι).1 κ hκc (by`. Introduce `w hlw`. Take `⟨A, hA⟩` from `ReciprocityTheory.Gal.exists_isPlaceOver Ω w`.

Take `⟨b, hb⟩` from `hloc w A hA (hMl w hlw)`. Use `⟨A, hA, b, k * n, Nat.mul_pos hk hn, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, hb s hs, ← mul_pow, zpow_neg, mul_inv_cancel, one_pow])`. Conclude with `⟨hc', art, χ', a', e1, e2, e3⟩`. Introduce `A hAM s hs`.

Distinguish the cases in `hAt : A = ⊤`. Rewrite `hs` using `[((Base.places L Ω l A).2.1 hAt).1]`. Rewrite using `[Subgroup.mem_bot.1 hs, map_one]`. Take `⟨w, hw⟩` from `(Base.places L Ω l A).1 hAt`. Conclude with `(hκ w A hw s hs).1 (fun h => hAM ((Pr.natCast_place hw M).2 h))`.

Introduce `A hAl`. Take `⟨w, hw⟩` from `(Base.places L Ω l A).1 (fun h => ((Base.places L Ω l A).2.1 h).2 hAl)`. Establish `hMw : (M : 𝓞 L) ∈ w.asIdeal` using `(Pr.natCast_place hw M).1 (val_of_dvd A hlM hAl)`. Take `⟨b, hb⟩` from `hloc w A hw hMw`. Conclude with `⟨b, k * n, Nat.mul_pos hk hn, hb⟩`.
-/
theorem UpperTheory.V.Z.Sym.Pl.twEx :
    UpperTheory.V.Z.Sym.Pl.LemTWM → UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Z.Sym.TwEx := by
  intro hTWM hAlg L Ω _ _ _ _ _ _ _ l _ hl2 ι c hc M hM0 hlM hU χ a hχo hχc hχM
  haveI : IsAlgClosure L Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : IsAlgClosure (Lp L) Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) (Lp L)⟩
  have h2 : Module.finrank (Lp L) L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hM3 : 3 ≤ M := by
    have h2l : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hlM' : l ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hlM
    omega
  have hχcont : Continuous χ := cont_of_ker χ hχo
  obtain ⟨n, hn, hχn⟩ := exists_exp χ hχo
  obtain ⟨Φ, hΦ⟩ := exists_type hU
  let ν : G (Lp L) Ω →* (Qbar l)ˣ := cycBar (Lp L) Ω l ^ a * χ.comp (galEmb ℚ (Lp L) Ω)
  have hν : ∀ s, ν s = cycBar (Lp L) Ω l s ^ a * χ (galEmb ℚ (Lp L) Ω s) := fun s => rfl
  have hνc : Continuous ν :=
    ((cont_cyc _ Ω l).zpow a).mul (hχcont.comp (continuous_restrictScalarsHom ℚ (Lp L) Ω))
  have hνconj : ∀ g : G (Lp L) Ω, IsConjEl g → ν g = 1 := by
    intro g hg
    obtain ⟨j, hj⟩ := hg
    have hcc : Sd.IsCC (galEmb ℚ (Lp L) Ω g) := ⟨j, hj⟩
    have e1 : χ (galEmb ℚ (Lp L) Ω g) = (-1) ^ a := (cc_val hc hcc).trans hχc
    have e0 := IsConjOm.cyc (E := Lp L) (Ω := Ω) (l := l)
      (σ := MulSemiringAction.toRingAut (G (Lp L) Ω) Ω g) ⟨j, hj⟩
    have e2 : cycBar (Lp L) Ω l g = -1 := by
      unfold cycBar cycZ
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e0]
      ext
      simp
    rw [hν, e1, e2, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  have hνunr : ∀ (v : HeightOneSpectrum (𝓞 (Lp L))) (A : ValuationSubring Ω),
      IsPlaceOver A v → ↑M ∉ v.asIdeal → ∀ s ∈ Ine A, ν s = 1 := by
    intro v A hA hMv s hs
    have hAM : ¬ A.valuation (M : Ω) < 1 := fun h => hMv ((Pr.natCast_place hA M).1 h)
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h => hAM (val_of_dvd A hlM h)
    have hcy : cycZ (Lp L) Ω l s = 1 := (Base.places (Lp L) Ω l A).2.2.2 hAl hs
    have hcb : cycBar (Lp L) Ω l s = 1 := by
      unfold cycBar
      rw [MonoidHom.comp_apply, hcy, map_one]
    obtain ⟨t, rfl⟩ := ine_range l hU.unr A hs
    have ht : t ∈ Ine A := hs
    rw [hν, hcb, one_zpow, one_mul]
    exact hχM A hAM t ht
  obtain ⟨κ, hκc, hV, k, hk, hκ⟩ :=
    hTWM (Lp L) L Ω inferInstance h2 l M hM3 Φ hΦ ν hνc hνconj hνunr
  obtain ⟨g, hg⟩ : c ∈ (galEmb ℚ (Lp L) Ω).range := by
    rw [range_galEmb]
    exact cc_real hc
  have hgn : g ∉ (resG (Lp L) L Ω).range := by
    rintro ⟨t, rfl⟩
    apply cc_not_mem (L := L) hc
    rw [← hg]
    exact galEmb_mem ℚ L Ω t
  have hinj : ∀ x y : G (Lp L) Ω, galEmb ℚ (Lp L) Ω x = galEmb ℚ (Lp L) Ω y → x = y :=
    fun x y h => AlgEquiv.ext fun z => DFunLike.congr_fun h z
  have hconj : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ →
      resG (Lp L) L Ω s' = g * resG (Lp L) L Ω s * g⁻¹ := by
    intro s s' h
    apply hinj
    rw [map_mul, map_mul, map_inv, hg]
    exact h
  have hnorm : (resG (Lp L) L Ω).range.Normal :=
    Subgroup.normal_of_index_eq_two (by rw [(Tw.resOpen (Lp L) L Ω).2, h2])
  have hloc : ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w →
      (M : 𝓞 L) ∈ w.asIdeal → ∃ b : ℤ, ∀ s ∈ Ine A,
        κ s ^ (k * n) = (cycBar L Ω l s ^ b) ^ (k * n) := by
    intro w A hA hMw
    by_cases hw : w ∈ Φ
    · refine ⟨a, fun s hs => ?_⟩
      obtain ⟨w', hne, hund, hiff⟩ := hΦ w hMw
      have hw' : w' ∉ Φ := hiff.1 hw
      obtain ⟨A', hA', hcA⟩ := Tw.conjPlace (Lp L) L Ω h2 g hgn w w' A hA hne hund
      obtain ⟨s', hs'⟩ : g * resG (Lp L) L Ω s * g⁻¹ ∈ (resG (Lp L) L Ω).range :=
        hnorm.conj_mem _ ⟨s, rfl⟩ g
      have hs'I : s' ∈ Ine A' := (hcA s s' hs').1 hs
      have e1 : κ s' ^ k = 1 := (hκ w' A' hA' s' hs'I).2 hw'
      have e2 : κ s * κ s' = cycBar L Ω l s ^ a * χ (galEmb ℚ L Ω s) := (hV g hgn).1 s s' hs'
      have e3 : κ s = cycBar L Ω l s ^ a * χ (galEmb ℚ L Ω s) * (κ s')⁻¹ :=
        eq_mul_inv_of_mul_eq e2
      have e4 : χ (galEmb ℚ L Ω s) ^ n = 1 := hχn _
      rw [e3, mul_pow, mul_pow, inv_pow, pow_mul (κ s') k n, e1, one_pow, inv_one, mul_one,
        mul_comm k n, pow_mul (χ _) n k, e4, one_pow, mul_one]
    · refine ⟨0, fun s hs => ?_⟩
      have e1 : κ s ^ k = 1 := (hκ w A hA s hs).2 hw
      rw [zpow_zero, one_pow, pow_mul, e1, one_pow]
  have hMl : ∀ w : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal := by
    intro w hlw
    obtain ⟨m, hm⟩ := hlM
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hlw
  refine ⟨κ, ?_, fun s s' h => (hV g hgn).1 s s' (hconj s s' h), ?_, ?_⟩
  · obtain ⟨χ', hc', art, a', e1, e2, e3⟩ := (hAlg L Ω l ι).1 κ hκc (by
      intro w hlw
      obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
      obtain ⟨b, hb⟩ := hloc w A hA (hMl w hlw)
      refine ⟨A, hA, b, k * n, Nat.mul_pos hk hn, fun s hs => ?_⟩
      rw [mul_pow, hb s hs, ← mul_pow, zpow_neg, mul_inv_cancel, one_pow])
    exact ⟨hc', art, χ', a', e1, e2, e3⟩
  · intro A hAM s hs
    by_cases hAt : A = ⊤
    · rw [((Base.places L Ω l A).2.1 hAt).1] at hs
      rw [Subgroup.mem_bot.1 hs, map_one]
    · obtain ⟨w, hw⟩ := (Base.places L Ω l A).1 hAt
      exact (hκ w A hw s hs).1 (fun h => hAM ((Pr.natCast_place hw M).2 h))
  · intro A hAl
    obtain ⟨w, hw⟩ := (Base.places L Ω l A).1 (fun h => ((Base.places L Ω l A).2.1 h).2 hAl)
    have hMw : (M : 𝓞 L) ∈ w.asIdeal := (Pr.natCast_place hw M).1 (val_of_dvd A hlM hAl)
    obtain ⟨b, hb⟩ := hloc w A hw hMw
    exact ⟨b, k * n, Nat.mul_pos hk hn, hb⟩
