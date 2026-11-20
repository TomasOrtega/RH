import Mathlib
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace PositivityTheory.FamInh

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

omit [IsAlgClosure K Ω] in

/- English proof (translation)
Set `P : Ideal (𝓞 L)` to `(primeBelow (F := L) A).under (𝓞 L)`. Establish `hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P` using `fun x => Iff.rfl`. Establish `hu : v.asIdeal = P.under (𝓞 K)`. Use extensionality with `x`. Rewrite using `[← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]`.

Both sides reduce to the same expression. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[hu, h]`.

Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Conclude with `⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩`.
-/
theorem exists_place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let P : Ideal (𝓞 L) := (primeBelow (F := L) A).under (𝓞 L)
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x => Iff.rfl
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩

/- English proof (translation)
Use `⟨hσ, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨s, t, hs, ht, hs1, e⟩` from `exists_den K A hx`. Establish `hσx : A.valuation (σ x) ≤ 1`. Rewrite using `[A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hσ, ← A.valuation_le_one_iff]`. Conclude with `hx`.

Establish `he' : σ s * σ x = σ t` using `by rw [← map_mul, e]`. Establish `key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x`. Rewrite using `[← he', ← e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : A.valuation (s * (σ x - x)) < 1`.

Rewrite using `[key]`. Apply `Valuation.map_sub_lt _ (h t ht)` to reduce the goal to its premises. Rewrite using `[Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hv` using `[Valuation.map_mul, hs1, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := K) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den K A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hσ, ← A.valuation_le_one_iff]
    exact hx
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    apply Valuation.map_sub_lt _ (h t ht)
    rw [Valuation.map_mul]
    calc A.valuation (σ s - s) * A.valuation (σ x) ≤ A.valuation (σ s - s) * 1 := mul_le_mul_right hσx _
      _ < 1 := by rw [mul_one]; exact h s hs
  rwa [Valuation.map_mul, hs1, one_mul] at hv

variable [IsGalois K L]

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
/- English proof (translation)
The claim follows from `AlgEquiv.restrictNormal_commutes σ L (x : L)`.
-/
theorem coe_res_smul (σ : G K Ω) (x : 𝓞 L) :
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) :=
  AlgEquiv.restrictNormal_commutes σ L (x : L)

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
/- English proof (translation)
Use extensionality with `x`. Apply `(algebraMap L Ω).injective` to reduce the goal to its premises. Conclude with `(AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x).trans (g.commutes x)`.
-/
theorem res_restrictScalars (g : Ω ≃ₐ[L] Ω) : AlgEquiv.restrictNormalHom L (g.restrictScalars K : G K Ω) = 1 := by
  ext x
  apply (algebraMap L Ω).injective
  exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x).trans (g.commutes x)

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff]`. Use extensionality with `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ← hw, ← hw, coe_res_smul, valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ)]`.
-/
theorem res_mem_stabilizer (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ← hw, ← hw, coe_res_smul,
    valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ)]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (x.isIntegral_coe.map ((algebraMap L Ω).toIntAlgHom)))`.
-/
theorem val_int_le_one (A : ValuationSubring Ω) (x : 𝓞 L) : A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A
    (x.isIntegral_coe.map ((algebraMap L Ω).toIntAlgHom)))

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
/- English proof (translation)
Introduce `x`. Use `show _ ∈ w.asIdeal`. Rewrite using `[← hw]`. Use `hσ.2 _ (val_int_le_one A x)` as an intermediate fact. Rewrite `this` using `[← coe_res_smul, ← map_sub]`.

Conclude with `this`.
-/
theorem res_mem_inertia (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Ine (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
  intro x
  show _ ∈ w.asIdeal
  rw [← hw]
  have := hσ.2 _ (val_int_le_one A x)
  rw [← coe_res_smul, ← map_sub] at this
  exact this

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
/- English proof (translation)
Introduce `x`. Rewrite using `[← hw, ← h.over]`. Use `hσ.2 _ (val_int_le_one A x)` as an intermediate fact. Rewrite `this` using `[← coe_res_smul, ← map_pow, ← map_sub]`. Conclude with `this`.
-/
theorem res_isArithFrobAt {v : HeightOneSpectrum (𝓞 K)} (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal]
    {σ : G K Ω} (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  intro x
  rw [← hw, ← h.over]
  have := hσ.2 _ (val_int_le_one A x)
  rw [← coe_res_smul, ← map_pow, ← map_sub] at this
  exact this

/- English proof (translation)
Take `⟨σ0, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ`. Establish `h1 : ∀ x : 𝓞 L, (σ0 • A).valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ w.asIdeal`. Introduce `x`. Rewrite using `[smul_valuation_lt_one_iff, ← coe_res_smul, hw, map_inv, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, MulAction.mem_stabilizer_iff.1 hτ]`. Take `⟨g, hg⟩` from `exists_smul_eq_of_over (F := L) h1 hw`.

Use `⟨g.restrictScalars K * σ0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_Dec, mul_smul]`. Conclude with `hg`. Rewrite using `[map_mul, res_restrictScalars, one_mul]`.
-/
theorem exists_lift_dec (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ∃ σ ∈ Dec (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ0, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  have h1 : ∀ x : 𝓞 L, (σ0 • A).valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    rw [smul_valuation_lt_one_iff, ← coe_res_smul, hw, map_inv, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      MulAction.mem_stabilizer_iff.1 hτ]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (F := L) h1 hw
  refine ⟨g.restrictScalars K * σ0, ?_, ?_⟩
  · rw [mem_Dec, mul_smul]
    exact hg
  · rw [map_mul, res_restrictScalars, one_mul]

def intAut (L : Type) [Field L] [NumberField L] [Algebra L Ω] (σ : G K Ω) : IntCl L Ω ≃+* IntCl L Ω where
  toFun b := ⟨σ b, ((isIntegral_int_of_isIntegral b.2).map (σ.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨σ.symm b, ((isIntegral_int_of_isIntegral b.2).map (σ.symm.toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (σ.symm_apply_apply _)
  right_inv b := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_add' a b := Subtype.ext (map_add σ _ _)

/- English proof (translation)
Take `⟨σ, hσ, rfl⟩` from `exists_lift_dec hw (Ideal.inertia_le_stabilizer _ hτ)`. Use `letI : TopologicalSpace (IntCl L Ω) := ⊥`. Use `haveI : DiscreteTopology (IntCl L Ω) := ⟨rfl⟩`. Use `haveI := continuousSMul_intCl L Ω`. Use `haveI := isInvariant_intCl L Ω`.

Use `set Q := primeBelow (F := L) A with hQ`. Use `haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hw).symm⟩`. Establish `hmap : Q = Q.map (intAut L σ : IntCl L Ω →+* IntCl L Ω)`. Rewrite using `[Ideal.map_comap_of_equiv]`. Use extensionality with `b`.

Rewrite using `[Ideal.mem_comap, mem_primeBelow, mem_primeBelow]`. Conclude with `(valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ) (b : Ω)).symm`. Set `φ : (IntCl L Ω ⧸ Q) ≃ₐ[𝓞 L ⧸ w.asIdeal] (IntCl L Ω ⧸ Q)` to `AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intAut L σ) hmap) (by`. Introduce `r`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective r`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk Q (intAut L σ (algebraMap (𝓞 L) (IntCl L Ω) x)) = Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl L Ω) x)`. Rewrite using `[Ideal.Quotient.eq, mem_primeBelow]`. Establish `h1` using `(hw _).2 (hτ x)`. Express the relevant statement in the definitionally equal form `A.valuation (σ (algebraMap L Ω (x : L)) - algebraMap L Ω (x : L)) < 1`. Rewrite using `[← coe_res_smul, ← map_sub]`.

Conclude with `h1)`. Take `⟨⟨ρ, hρQ⟩, hρ⟩` from `Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[L] Ω) w.asIdeal Q φ`. Establish `hρQ' : ρ • Q = Q` using `hρQ`. Establish `hcong : ∀ b : IntCl L Ω, A.valuation (σ (b : Ω) - ρ (b : Ω)) < 1`. Introduce `b`.

Establish `h1 : Ideal.Quotient.mk Q (ρ • b) = Ideal.Quotient.mk Q (intAut L σ b)` using `DFunLike.congr_fun hρ (Ideal.Quotient.mk Q b)`. Conclude with `Ideal.Quotient.eq.1 h1.symm`. Establish `hdec : ρ • A = A`. Use `eq_of_valuation_lt_one_iff L fun b hb => ?_` and prove the remaining obligations. Set `b' : IntCl L Ω` to `⟨b, hb.tower_top⟩`.

Express the relevant statement in the definitionally equal form `b' ∈ primeBelow (F := L) (ρ • A) ↔ b' ∈ Q`. Rewrite using `[primeBelow_smul, hρQ']`. Establish `hρD : (ρ.restrictScalars K : G K Ω) ∈ Dec (F` using `K) A := hdec`. Use `⟨(ρ.restrictScalars K)⁻¹ * σ, mem_Ine_of_integral ((Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hρD) hσ) fun b hb => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← valuation_apply_lt_one_iff hρD, map_sub, AlgEquiv.mul_apply, mul_inv_apply]`.

Conclude with `hcong ⟨b, hb.tower_top⟩`. Rewrite using `[map_mul, map_inv, res_restrictScalars, inv_one, one_mul]`.
-/
theorem exists_lift_ine (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L} (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L)) :
    ∃ σ ∈ Ine (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσ, rfl⟩ := exists_lift_dec hw (Ideal.inertia_le_stabilizer _ hτ)
  letI : TopologicalSpace (IntCl L Ω) := ⊥
  haveI : DiscreteTopology (IntCl L Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl L Ω
  haveI := isInvariant_intCl L Ω
  set Q := primeBelow (F := L) A with hQ
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hw).symm⟩
  have hmap : Q = Q.map (intAut L σ : IntCl L Ω →+* IntCl L Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ) (b : Ω)).symm
  let φ : (IntCl L Ω ⧸ Q) ≃ₐ[𝓞 L ⧸ w.asIdeal] (IntCl L Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intAut L σ) hmap) (by
      intro r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (intAut L σ (algebraMap (𝓞 L) (IntCl L Ω) x)) =
        Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl L Ω) x)
      rw [Ideal.Quotient.eq, mem_primeBelow]
      have h1 := (hw _).2 (hτ x)
      change A.valuation (σ (algebraMap L Ω (x : L)) - algebraMap L Ω (x : L)) < 1
      rw [← coe_res_smul, ← map_sub]
      exact h1)
  obtain ⟨⟨ρ, hρQ⟩, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[L] Ω) w.asIdeal Q φ
  have hρQ' : ρ • Q = Q := hρQ
  have hcong : ∀ b : IntCl L Ω, A.valuation (σ (b : Ω) - ρ (b : Ω)) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ • b) = Ideal.Quotient.mk Q (intAut L σ b) :=
      DFunLike.congr_fun hρ (Ideal.Quotient.mk Q b)
    exact Ideal.Quotient.eq.1 h1.symm
  have hdec : ρ • A = A := by
    refine eq_of_valuation_lt_one_iff L fun b hb => ?_
    let b' : IntCl L Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := L) (ρ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρQ']
  have hρD : (ρ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hdec
  refine ⟨(ρ.restrictScalars K)⁻¹ * σ, mem_Ine_of_integral
    ((Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hρD) hσ) fun b hb => ?_, ?_⟩
  · rw [← valuation_apply_lt_one_iff hρD, map_sub, AlgEquiv.mul_apply, mul_inv_apply]
    exact hcong ⟨b, hb.tower_top⟩
  · rw [map_mul, map_inv, res_restrictScalars, inv_one, one_mul]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in

/- English proof (translation)
Establish `: v.asIdeal.IsMaximal` using `v.isMaximal`. Establish `: Finite (𝓞 K ⧸ v.asIdeal)` using `Ring.HasFiniteQuotients.finiteQuotient v.ne_bot`. Rewrite using `[← Subgroup.card_eq_one, Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L)]`.
-/
theorem inertia_eq_bot_iff (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ ↔ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [← Subgroup.card_eq_one, Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L)]

end PositivityTheory.FamInh

end
