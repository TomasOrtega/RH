import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Tw
open scoped Pointwise

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

omit [NumberField L] in
/- English proof (translation)
Establish `hb : IsIntegral ℤ (algebraMap L Ω (x : L))` using `x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom`. Establish `h : IsIntegral A (algebraMap L Ω (x : L))` using `hb.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
private theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have hb : IsIntegral ℤ (algebraMap L Ω (x : L)) := x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom
  have h : IsIntegral A (algebraMap L Ω (x : L)) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

/- English proof (translation)
Set `f : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (int_mem A)`. Set `P : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P` using `fun x => (A.valuation_lt_one_iff (f x)).symm`. Establish `hu : v.asIdeal = P.under (𝓞 K)`. Use extensionality with `x`.

Rewrite using `[← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]`. Both sides reduce to the same expression. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hu, h]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Conclude with `⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩`.
-/
private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (int_mem A)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
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
Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `w.isMaximal` as an intermediate fact. Use `(w.under (𝓞 K)).isMaximal` as an intermediate fact. Use `show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]`.
-/
private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

omit [NumberField K] in
/- English proof (translation)
Establish `e : σ x = (σ x - x ^ q) + x ^ q` using `by ring`. Establish `h1` using `hσ.2 x hx`. Prove the components needed by the constructor for the conclusion. Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ h1.le (by rw [map_pow]; exact pow_le_one₀ zero_le hx)`.

Introduce `h`. Rewrite using `[e]`. Conclude with `Valuation.map_add_lt _ h1 (by rw [map_pow]; exact pow_lt_one₀ zero_le h hq)`.
-/
private theorem frob_val {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 ∧ (A.valuation x < 1 → A.valuation (σ x) < 1) := by
  have e : σ x = (σ x - x ^ q) + x ^ q := by ring
  have h1 := hσ.2 x hx
  constructor
  · rw [e]
    exact Valuation.map_add_le _ h1.le (by rw [map_pow]; exact pow_le_one₀ zero_le hx)
  · intro h
    rw [e]
    exact Valuation.map_add_lt _ h1 (by rw [map_pow]; exact pow_lt_one₀ zero_le h hq)

omit [NumberField K] in
/- English proof (translation)
Use `⟨mul_mem hσ.1 hσ.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hσ.2 x hx`. Establish `h2` using `(frob_val hq hσ h1.le).2 h1`. Establish `hxq : A.valuation (x ^ q) ≤ 1` using `by rw [map_pow]; exact pow_le_one₀ zero_le hx`. Establish `h3` using `hσ.2 (x ^ q) hxq`.

Establish `e : (σ * σ) x - x ^ q ^ 2 = σ (σ x - x ^ q) + (σ (x ^ q) - (x ^ q) ^ q)`. Rewrite using `[AlgEquiv.mul_apply, map_sub, sq, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Valuation.map_add_lt _ h2 h3`.
-/
private theorem frob_sq {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) :
    IsFrob A (q ^ 2) (σ * σ) := by
  refine ⟨mul_mem hσ.1 hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  have h2 := (frob_val hq hσ h1.le).2 h1
  have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
  have h3 := hσ.2 (x ^ q) hxq
  have e : (σ * σ) x - x ^ q ^ 2 = σ (σ x - x ^ q) + (σ (x ^ q) - (x ^ q) ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub, sq, pow_mul]; ring
  rw [e]
  exact Valuation.map_add_lt _ h2 h3

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hU hA σ hσ hn`. Take `⟨w, hw, hwv⟩` from `place_between (L := L) hA`. Establish `: Algebra.IsQuadraticExtension F L` using `⟨h2⟩`. Establish `: IsGalois F L` using `inferInstance`. Establish `hq : normV v ≠ 0` using `(lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'`.

Establish `hu : w.under (𝓞 F) = v` using `HeightOneSpectrum.ext hwv.over.symm`. Use `set c : L ≃ₐ[F] L := AlgEquiv.restrictNormalHom L σ with hc`. Establish `hcx : ∀ x : L, algebraMap L Ω (c x) = σ (algebraMap L Ω x)` using `fun x => AlgEquiv.restrictNormal_commutes σ L x`. Establish `hc1 : c ≠ 1` using `fun h => hn ⟨{ σ with commutes' := fun x => by`. Use `hcx x` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `this.symm }, rfl⟩`. Use `w.isMaximal` as an intermediate fact. Establish `hcw : c • w.asIdeal = w.asIdeal`. Establish `hmax : (c • w.asIdeal).IsMaximal`.

Conclude with `Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ c)`. Use `hmax.eq_of_le w.isPrime.ne_top ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hy |> fun h => (⟨c⁻¹ • y, h, smul_inv_smul c y⟩ : ∃ x ∈ w.asIdeal, c • x = y)`. Rewrite `hx`, the goal using `[← hw]`.

Establish `e : algebraMap L Ω ((c • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L))` using `hcx x`. Rewrite using `[e]`. Conclude with `(frob_val hq hσ hx.le).2 hx`. Establish `huniq : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver v.asIdeal → P = w.asIdeal`. Introduce `P _ _`.

Take `⟨g, hg⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[F] L)`. Establish `hcard : Nat.card (L ≃ₐ[F] L) = 2` using `by rw [IsGalois.card_aut_eq_finrank, h2]`. Distinguish the cases in `hg1 : g = 1`. Rewrite using `[← hg, hg1, one_smul]`. Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard`.

Rewrite using `[← hg, hy g hg1, ← hy c hc1, hcw]`. Establish `hf : w.asIdeal.inertiaDeg (𝓞 F) = 2`. Use `v.isPrime` as an intermediate fact. Use `letI : Unique (v.asIdeal.primesOver (𝓞 L)) := ⟨⟨⟨w.asIdeal, w.isPrime, hwv⟩⟩, fun P => Subtype.ext (huniq P.1 P.2.1 P.2.2)⟩`. Establish `hs` using `Ideal.sum_ramification_inertia_eq_card (p := v.asIdeal) (S := 𝓞 L) (G := L ≃ₐ[F] L)`.

Rewrite `hs` using `[Fintype.sum_unique, IsGalois.card_aut_eq_finrank, h2]`. Establish `he` using `hU w hu`. Rewrite `he` using `[hu, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]`. Express the relevant statement in the definitionally equal form `w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2 at hs`. Rewrite `hs` using `[he, one_mul]`. Then use the resulting hypothesis.

Use `⟨w, fun u => ⟨fun h => HeightOneSpectrum.ext (huniq _ u.isPrime ⟨by rw [← h]; rfl⟩), fun h => h ▸ hu⟩, hw, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h3` using `frob_sq hq hσ`. Rewrite `h3` using `[← ht]`. Rewrite using `[normV_under (K := F), hu, hf]`. Conclude with `⟨h3.1, h3.2⟩`.
-/
theorem UpperTheory.V.Af.Tw.frobInert :
    UpperTheory.V.Af.Tw.FrobInert := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hU hA σ hσ hn
  obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA
  have : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  have : IsGalois F L := inferInstance
  have hq : normV v ≠ 0 := (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hu : w.under (𝓞 F) = v := HeightOneSpectrum.ext hwv.over.symm
  set c : L ≃ₐ[F] L := AlgEquiv.restrictNormalHom L σ with hc
  have hcx : ∀ x : L, algebraMap L Ω (c x) = σ (algebraMap L Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes σ L x
  have hc1 : c ≠ 1 := fun h => hn ⟨{ σ with
    commutes' := fun x => by
      have := hcx x
      rw [h] at this
      exact this.symm }, rfl⟩
  have := w.isMaximal
  have hcw : c • w.asIdeal = w.asIdeal := by
    have hmax : (c • w.asIdeal).IsMaximal := by
      exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ c)
    refine hmax.eq_of_le w.isPrime.ne_top ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hy |> fun h => (⟨c⁻¹ • y, h, smul_inv_smul c y⟩ : ∃ x ∈ w.asIdeal, c • x = y)
    rw [← hw] at hx ⊢
    have e : algebraMap L Ω ((c • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) := hcx x
    rw [e]
    exact (frob_val hq hσ hx.le).2 hx
  have huniq : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver v.asIdeal → P = w.asIdeal := by
    intro P _ _
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[F] L)
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    by_cases hg1 : g = 1
    · rw [← hg, hg1, one_smul]
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
      rw [← hg, hy g hg1, ← hy c hc1, hcw]
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 2 := by
    have := v.isPrime
    letI : Unique (v.asIdeal.primesOver (𝓞 L)) :=
      ⟨⟨⟨w.asIdeal, w.isPrime, hwv⟩⟩, fun P => Subtype.ext (huniq P.1 P.2.1 P.2.2)⟩
    have hs := Ideal.sum_ramification_inertia_eq_card (p := v.asIdeal) (S := 𝓞 L) (G := L ≃ₐ[F] L)
    rw [Fintype.sum_unique, IsGalois.card_aut_eq_finrank, h2] at hs
    have he := hU w hu
    rw [hu, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2 at hs
    rwa [he, one_mul] at hs
  refine ⟨w, fun u => ⟨fun h => HeightOneSpectrum.ext (huniq _ u.isPrime ⟨by rw [← h]; rfl⟩), fun h => h ▸ hu⟩,
    hw, fun t ht => ?_⟩
  have h3 := frob_sq hq hσ
  rw [← ht] at h3
  rw [normV_under (K := F), hu, hf]
  exact ⟨h3.1, h3.2⟩
