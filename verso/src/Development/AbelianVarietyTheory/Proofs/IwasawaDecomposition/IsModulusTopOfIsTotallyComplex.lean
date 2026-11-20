import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.Mem.Chr GlobalTheory.Mem.LocTriv GlobalTheory.RayFromArtin
open scoped nonZeroDivisors

namespace GlobalTheory.UnramModulus

/- English proof (translation)
Set `f : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x => (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)`. Establish `hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1` using `fun x => A.valuation_lt_one_iff (f x)`. Use `⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]`.

Both sides reduce to the same expression. Rewrite using `[hf]`. Use `hσ.2 _ (valuation_int_le_one A x)` as an intermediate fact. Rewrite `this` using `[← σ.restrictNormal_commutes L, ← map_sub]`. Conclude with `this`.
-/
theorem inInertia_restrict {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (L : Type) [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G K Ω}
    (hσ : σ ∈ Ine (F := K) A) : GlobalTheory.NT.InInertia L v (AlgEquiv.restrictNormalHom L σ) := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  refine ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩
  · ext x
    rw [Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  · rw [hf]
    have := hσ.2 _ (valuation_int_le_one A x)
    rw [← σ.restrictNormal_commutes L, ← map_sub] at this
    exact this

/- English proof (translation)
Introduce and unpack `b ⟨hb, -, hb'⟩`. Set `c : Ideles K` to `Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (infPart b)`. Establish `e : b = c * finPartI K b` using `Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)`. Rewrite using `[e]`. Use `mul_mem (hi ⟨_, hb', rfl⟩) ?_` and prove the remaining obligations.

Use `(U.isClosed_of_isOpen ho).mem_of_tendsto (tendsto_part (a := finPartI K b) hb fun _ => rfl) (Filter.Eventually.of_forall fun S => ?_)` and prove the remaining obligations. Conclude with `Subgroup.prod_mem _ fun v _ => hu v _ (hb v)`.
-/
theorem rayIdl_le {K : Type} [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) {U : Subgroup (Ideles K)}
    (ho : IsOpen (U : Set (Ideles K))) (hi : infConn K ≤ U)
    (hu : ∀ v x, IsUnitAt v x → localIdele K v x ∈ U) : rayIdl 𝔪 ≤ U := by
  rintro b ⟨hb, -, hb'⟩
  let c : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (infPart b)
  have e : b = c * finPartI K b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [e]
  refine mul_mem (hi ⟨_, hb', rfl⟩) ?_
  refine (U.isClosed_of_isOpen ho).mem_of_tendsto
    (tendsto_part (a := finPartI K b) hb fun _ => rfl) (Filter.Eventually.of_forall fun S => ?_)
  exact Subgroup.prod_mem _ fun v _ => hu v _ (hb v)

/- English proof (translation)
Set `Ω` to `AlgebraicClosure K`. Take `⟨art, ha⟩` from `H K Ω`. Set `j : M →ₐ[K] Ω` to `IsAlgClosed.lift`. Set `: Algebra M Ω` to `j.toRingHom.toAlgebra`. Establish `: IsScalarTower K M Ω` using `IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`.

Set `: CommGroup (M ≃ₐ[K] M)` to `{ (inferInstance : Group (M ≃ₐ[K] M)) with mul_comm := mul_comm' }`. Set `φ : G K Ω →* (M ≃ₐ[K] M)` to `AlgEquiv.restrictNormalHom M`. Establish `hφ : Continuous φ`. Use `continuous_of_isOpen_ker' φ ?_` and prove the remaining obligations. Establish `: FiniteDimensional K j.fieldRange` using `j.equivFieldRange.toLinearEquiv.finiteDimensional`.

Use `Subgroup.isOpen_mono (fun σ hσ => ?_) j.fieldRange.fixingSubgroup_isOpen` and prove the remaining obligations. Use extensionality with `x`. Apply `(algebraMap M Ω).injective` to reduce the goal to its premises. Conclude with `(σ.restrictNormal_commutes M x).trans (hσ ⟨_, x, rfl⟩)`. Set `θ : Ideles K →* (M ≃ₐ[K] M)` to `(liftAb φ hφ).comp art`.

Establish `hθ : Continuous θ` using `(continuous_liftAb φ hφ).comp ha.quot.continuous`. Establish `ho : IsOpen (θ.ker : Set (Ideles K))` using `(isOpen_discrete {1}).preimage hθ`. Establish `hk : (diagUnits K).range ⊔ infConn K ≤ θ.ker` using `fun x hx => by`. Establish `hk : x ∈ art.ker`. Rewrite using `[ha.ker]`.

Conclude with `Subgroup.le_topologicalClosure _ hx`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]`. Establish `hr : rayGrp ⊤ ≤ θ.ker`. Use `sup_le (le_sup_left.trans hk) (rayIdl_le ⊤ ho (le_sup_right.trans hk) fun v x hx => ?_)` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω v`.

Take `⟨τ, hτ, e⟩` from `(ha.ine v A hA _).1 ⟨x, hx, rfl⟩`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, ← e, liftAb_toAb]`. Conclude with `hM v _ (inInertia_restrict M hA hτ)`. Set `ψ : idealsPrimeTo (⊤ : Ideal (𝓞 K)) →* (M ≃ₐ[K] M)` to `(θ.comp (unifIdl ⊤))⁻¹`. Establish `hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn M 𝔭 ∧ GlobalTheory.NT.IsFrob M 𝔭 (ψ (primeElt ⊤ 𝔭 h))` using `fun v hv => by`.

Use `⟨hM v, ?_⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω v`. Take `⟨σ, hσ, e'⟩` from `(ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩`. Establish `: ψ (primeElt ⊤ v hv) = AlgEquiv.restrictNormalHom M σ`. Rewrite using `[MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, MonoidHom.comp_apply, ← e', liftAb_toAb, map_inv, inv_inv]`.

Rewrite using `[this]`. Conclude with `isFrob_restrict M hA hσ`. Use `⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr' => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `GlobalTheory.NT.exists_isFrob M 𝔭`. Rewrite using `[GlobalTheory.NT.heckeVal_of_unramIn M χ (hM 𝔭) hσ]`.

Conclude with `Units.ne_zero _`. Establish `ha0 : Ideal.span {α} ≠ ⊥` using `by simpa using hr'.1`. Establish `hb0 : Ideal.span {β} ≠ ⊥` using `by simpa using hr'.2.1`. Take `⟨A, hA'⟩` from `exists_integral ⊤ _ ha0 hr'.2.2.1`. Take `⟨B, hB'⟩` from `exists_integral ⊤ _ hb0 hr'.2.2.2.1`.

Rewrite using `[heckeIdeal_eq M ⊤ ψ hψ χ _ ha0 A hA', heckeIdeal_eq M ⊤ ψ hψ χ _ hb0 B hB']`. Establish `h1 : B⁻¹ * A ∈ (rayPrincipal ⊤).subgroupOf (idealsPrimeTo (⊤ : Ideal (𝓞 K)))`. Rewrite using `[Subgroup.mem_subgroupOf]`. Establish `haK : (α : K) ≠ 0` using `by exact_mod_cast hr'.1`. Establish `hbK : (β : K) ≠ 0` using `by exact_mod_cast hr'.2.1`.

Use `⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr', by simp [hbK]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]`. Use `congr 1`.

Conclude with `mul_div_cancel₀ _ hbK`. Establish `h2 : ψ (B⁻¹ * A) = 1`. Rewrite using `[MonoidHom.inv_apply, inv_eq_one]`. Conclude with `hr ((unifIdl_mem_rayGrp_iff top_ne_bot _).2 h1)`. Rewrite `h2` using `[map_mul, map_inv, inv_mul_eq_one]`.

Rewrite using `[h2]`.
-/
theorem isModulus_top (H : GlobalTheory.Published.GlobalArtinReciprocity) (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭)
    (χ : (M ≃ₐ[K] M) →* ℂˣ) : GlobalTheory.NT.IsModulus M χ ⊤ := by
  let Ω := AlgebraicClosure K
  obtain ⟨art, ha⟩ := H K Ω
  let j : M →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra M Ω := j.toRingHom.toAlgebra
  have : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : CommGroup (M ≃ₐ[K] M) := { (inferInstance : Group (M ≃ₐ[K] M)) with mul_comm := mul_comm' }
  let φ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hφ : Continuous φ := by
    refine continuous_of_isOpen_ker' φ ?_
    have : FiniteDimensional K j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun σ hσ => ?_) j.fieldRange.fixingSubgroup_isOpen
    ext x
    apply (algebraMap M Ω).injective
    exact (σ.restrictNormal_commutes M x).trans (hσ ⟨_, x, rfl⟩)
  let θ : Ideles K →* (M ≃ₐ[K] M) := (liftAb φ hφ).comp art
  have hθ : Continuous θ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (θ.ker : Set (Ideles K)) := (isOpen_discrete {1}).preimage hθ
  have hk : (diagUnits K).range ⊔ infConn K ≤ θ.ker := fun x hx => by
    have hk : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have hr : rayGrp ⊤ ≤ θ.ker := by
    refine sup_le (le_sup_left.trans hk) (rayIdl_le ⊤ ho (le_sup_right.trans hk) fun v x hx => ?_)
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨τ, hτ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← e, liftAb_toAb]
    exact hM v _ (inInertia_restrict M hA hτ)
  let ψ : idealsPrimeTo (⊤ : Ideal (𝓞 K)) →* (M ≃ₐ[K] M) := (θ.comp (unifIdl ⊤))⁻¹
  have hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn M 𝔭 ∧ GlobalTheory.NT.IsFrob M 𝔭 (ψ (primeElt ⊤ 𝔭 h)) := fun v hv => by
    refine ⟨hM v, ?_⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ, e'⟩ := (ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩
    have : ψ (primeElt ⊤ v hv) = AlgEquiv.restrictNormalHom M σ := by
      rw [MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, MonoidHom.comp_apply,
        ← e', liftAb_toAb, map_inv, inv_inv]
    rw [this]
    exact isFrob_restrict M hA hσ
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr' => ?_⟩
  · obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob M 𝔭
    rw [GlobalTheory.NT.heckeVal_of_unramIn M χ (hM 𝔭) hσ]
    exact Units.ne_zero _
  · have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr'.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr'.2.1
    obtain ⟨A, hA'⟩ := exists_integral ⊤ _ ha0 hr'.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral ⊤ _ hb0 hr'.2.2.2.1
    rw [heckeIdeal_eq M ⊤ ψ hψ χ _ ha0 A hA', heckeIdeal_eq M ⊤ ψ hψ χ _ hb0 B hB']
    have h1 : B⁻¹ * A ∈ (rayPrincipal ⊤).subgroupOf (idealsPrimeTo (⊤ : Ideal (𝓞 K))) := by
      rw [Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast hr'.1
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hr'.2.1
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr', by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    have h2 : ψ (B⁻¹ * A) = 1 := by
      rw [MonoidHom.inv_apply, inv_eq_one]
      exact hr ((unifIdl_mem_rayGrp_iff top_ne_bot _).2 h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]

/- English proof (translation)
Introduce `H K M _ _ _ _ _ _ _ hM χ` and use `isModulus_top H K M hM χ`.
-/
theorem isModulus_top_of_isTotallyComplex : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (K M : Type) [Field K]
    [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M],
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭) → ∀ χ : (M ≃ₐ[K] M) →* ℂˣ, GlobalTheory.NT.IsModulus M χ ⊤ :=
  fun H K M _ _ _ _ _ _ _ hM χ => isModulus_top H K M hM χ

end GlobalTheory.UnramModulus

end
