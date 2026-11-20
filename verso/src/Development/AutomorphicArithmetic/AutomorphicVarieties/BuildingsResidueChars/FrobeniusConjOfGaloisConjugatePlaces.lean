import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
open scoped Pointwise

/- English proof (translation)
Use `show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)`. Use `Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv` and prove the remaining obligations. Conclude with `(Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K) (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm`.
-/
private theorem normV_pre {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

/- English proof (translation)
Use `⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← val_lt_one hA, map_sub, apply_conjGal, map_pow]`. Conclude with `hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))`.
-/
private theorem isFrob_conj {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

/- English proof (translation)
Establish `h' : w'.asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K)` using `congrArg HeightOneSpectrum.asIdeal h`. Use `w.isPrime` as an intermediate fact. Use `w'.isPrime` as an intermediate fact. Establish `: w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K))` using `⟨rfl⟩`. Establish `: w'.asIdeal.LiesOver (w.asIdeal.under (𝓞 K))` using `⟨h'.symm⟩`.

Take `⟨g, hg⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (w.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal (M ≃ₐ[K] M)`. Use `⟨g, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩` and prove the remaining obligations. Rewrite using `[mem_preplace, ← hg]`. Conclude with `Ideal.smul_mem_pointwise_smul_iff (a := g) (x := x)`.
-/
private theorem exists_pre {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (w w' : HeightOneSpectrum (𝓞 M)) (h : w'.under (𝓞 K) = w.under (𝓞 K)) :
    ∃ g : M ≃ₐ[K] M, preplace g.toRingEquiv w' = w := by
  have h' : w'.asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K) := congrArg HeightOneSpectrum.asIdeal h
  have := w.isPrime
  have := w'.isPrime
  have : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨rfl⟩
  have : w'.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨h'.symm⟩
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal (M ≃ₐ[K] M)
  refine ⟨g, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [mem_preplace, ← hg]
  exact Ideal.smul_mem_pointwise_smul_iff (a := g) (x := x)

/- English proof (translation)
Introduce `K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r w w' h`. Take `⟨g, rfl⟩` from `exists_pre w w' h`. Use `⟨(normV_pre _ _).symm, fun B hB A' hA' => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `exists_isLift (Ω := Ω) g.toRingEquiv`. Set `s : G K Ω` to `AlgEquiv.ofRingEquiv (f := σ) fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply K M Ω, hσ]`. Conclude with `congrArg (algebraMap M Ω) (g.commutes x)`. Establish `key : ∀ t : G M Ω, r (resG K M Ω t) = r s * r (resG K M Ω (conjGal hσ t)) * (r s)⁻¹` using `fun t => by`. Rewrite using `[eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul]`. Use `congr 1`.

Conclude with `AlgEquiv.ext fun x => (apply_conjGal hσ t x).symm`. Establish `hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom` using `fun _ => Iff.rfl`. Take `⟨h1, h2⟩` from `hB _ (isPlaceOver_preplace hσ hA hA')`. Use `⟨fun t ht => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `e : r (resG K M Ω (conjGal hσ t)) = 1` using `h1 _ (conjGal_mem_Ine hσ hA ht)`.

Rewrite using `[MonoidHom.comp_apply, key, e, mul_one, mul_inv_cancel]`. Establish `e` using `h2 (conjGal hσ t) (by rw [normV_pre]; exact isFrob_conj hσ hA ht)`. Rewrite using `[← e, ← map_inv (conjGal hσ), MonoidHom.comp_apply, MonoidHom.comp_apply, key t⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv (r s), Matrix.charpoly_units_conj]`.
-/
theorem UpperTheory.frobenius_conj_of_galois_conjugate_places :
    UpperTheory.V.Af.Sol.FrobConj := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r w w' h
  obtain ⟨g, rfl⟩ := exists_pre w w' h
  refine ⟨(normV_pre _ _).symm, fun B hB A' hA' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isLift (Ω := Ω) g.toRingEquiv
  let s : G K Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, hσ]
    exact congrArg (algebraMap M Ω) (g.commutes x)
  have key : ∀ t : G M Ω, r (resG K M Ω t) = r s * r (resG K M Ω (conjGal hσ t)) * (r s)⁻¹ := fun t => by
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul]
    congr 1
    exact AlgEquiv.ext fun x => (apply_conjGal hσ t x).symm
  have hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom := fun _ => Iff.rfl
  obtain ⟨h1, h2⟩ := hB _ (isPlaceOver_preplace hσ hA hA')
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have e : r (resG K M Ω (conjGal hσ t)) = 1 := h1 _ (conjGal_mem_Ine hσ hA ht)
    rw [MonoidHom.comp_apply, key, e, mul_one, mul_inv_cancel]
  · have e := h2 (conjGal hσ t) (by rw [normV_pre]; exact isFrob_conj hσ hA ht)
    rw [← e, ← map_inv (conjGal hσ), MonoidHom.comp_apply, MonoidHom.comp_apply, key t⁻¹,
      Units.val_mul, Units.val_mul, Matrix.coe_units_inv (r s), Matrix.charpoly_units_conj]
