import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)
open scoped Pointwise

section SlopeTestRemainingChoices

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

/- English proof (translation)
Introduce `x` and use `by have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff have hv : ∀ y, (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := fun y => by rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective] rw [h …`.
-/
private theorem place_conj {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v := fun x => by
  have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff
  have hv : ∀ y, (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective]
  rw [hv, AlgEquiv.commutes]
  exact h x

/- English proof (translation)
Establish `hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A` using `fun x => by`. Establish `h : IsIntegral A (algebraMap E Ω (x : E))` using `(x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `f : 𝓞 E →+* A` to `((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A hint`. Set `P : Ideal (𝓞 E)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hP : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P` using `fun x => (A.valuation_lt_one_iff (f x)).symm`. Establish `hu : v.asIdeal = P.under (𝓞 F)`. Use extensionality with `x`.

Rewrite using `[← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F E Ω]`. Both sides reduce to the same expression. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hu, h]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Conclude with `⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩`.
-/
private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 E), IsPlaceOver A w ∧ w.under (𝓞 F) = v := by
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap E Ω (x : E)) := (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A hint
  let P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 F) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F E Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `L Ω _ _ _ _ _ _ A v hA hD w hw`. Assume the negation of the conclusion as `hs`. Establish `huniq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = v → u = w` using `fun u hu => by`. Assume the negation of the conclusion as `h`. Conclude with `hs ⟨u, h, hu.trans hw.symm⟩`.

Use `haveI : Normal (Lp L) Ω := IsAlgClosure.normal _ _`. Set `t : G (Lp L) Ω` to `(IsCMField.complexConj L).liftNormal Ω`. Establish `ht : ∀ y : L, t (algebraMap L Ω y) = algebraMap L Ω (IsCMField.complexConj L y)` using `fun y => AlgEquiv.liftNormal_commutes _ Ω y`. Take `⟨u, hu, hu'⟩` from `place_between (E := L) hA`. Take `⟨u', hu1, hu1'⟩` from `place_between (E := L) (place_conj hA t)`.

Rewrite `hu` using `[huniq u hu']`. Rewrite `hu1` using `[huniq u' hu1']`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (F := L) hu hu1`. Establish `hg' : resP L Ω g • A = t⁻¹ • A` using `hg`. Establish `hm : t * resP L Ω g ∈ Dec (F` using `Lp L) A := by show (t * resP L Ω g) • A = A`.

Rewrite using `[mul_smul, hg', smul_inv_smul]`. Take `⟨k, hk⟩` from `(Subgroup.mul_mem_cancel_right _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD hm)`. Apply `IsCMField.complexConj_ne_one L` to reduce the goal to its premises. Use extensionality with `y`. Apply `(algebraMap L Ω).injective` to reduce the goal to its premises.

Rewrite using `[← ht, ← hk]`. Conclude with `k.commutes y`.
-/
theorem UpperTheory.isSplitAt_of_decomposition_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Dec (F := Lp L) A ≤ (resP L Ω).range → ∀ w : Plc L, w.under (𝓞 (Lp L)) = v → IsSplitAt w := by
  intro L Ω _ _ _ _ _ _ A v hA hD w hw
  by_contra hs
  have huniq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = v → u = w := fun u hu => by
    by_contra h
    exact hs ⟨u, h, hu.trans hw.symm⟩
  haveI : Normal (Lp L) Ω := IsAlgClosure.normal _ _
  let t : G (Lp L) Ω := (IsCMField.complexConj L).liftNormal Ω
  have ht : ∀ y : L, t (algebraMap L Ω y) = algebraMap L Ω (IsCMField.complexConj L y) := fun y =>
    AlgEquiv.liftNormal_commutes _ Ω y
  obtain ⟨u, hu, hu'⟩ := place_between (E := L) hA
  obtain ⟨u', hu1, hu1'⟩ := place_between (E := L) (place_conj hA t)
  rw [huniq u hu'] at hu
  rw [huniq u' hu1'] at hu1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := L) hu hu1
  have hg' : resP L Ω g • A = t⁻¹ • A := hg
  have hm : t * resP L Ω g ∈ Dec (F := Lp L) A := by
    show (t * resP L Ω g) • A = A
    rw [mul_smul, hg', smul_inv_smul]
  obtain ⟨k, hk⟩ := (Subgroup.mul_mem_cancel_right _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD hm)
  apply IsCMField.complexConj_ne_one L
  ext y
  apply (algebraMap L Ω).injective
  rw [← ht, ← hk]
  exact k.commutes y
