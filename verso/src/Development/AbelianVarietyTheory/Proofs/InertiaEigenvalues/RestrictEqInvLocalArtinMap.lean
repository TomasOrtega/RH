import Mathlib
import GroundTheory.LocalFields.MainTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfPowEqSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
open GroundTheory.LocalField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompare

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg`. Establish `hN` using `GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha`. Take `⟨θ, -, -, hl⟩` from `GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι`. Set `ψ : Weil h →* GalLoc w` to `θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))`. Establish `hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ` using `fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩`.

Establish `e2 : ψ σ = g`. Establish `e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ`. Use `hl (θ.symm g)` as an intermediate fact. Rewrite `this` using `[θ.apply_symm_apply]`. Conclude with `Subtype.ext (this.eq hg)`.

Use `show θ _ = g`. Rewrite using `[← e, θ.apply_symm_apply]`. Set `r` to `(AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ`. Establish `hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L] (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)), restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ)` using `fun τ L _ hL => restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)`. Establish `hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L], a τ ∈ (normUnits (w.adicCompletion E) L).range → restrictAb L (le_maximalAbelianExtension L) (r τ) = 1` using `fun τ L _ hL hx => by`.

Use `(hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx` as an intermediate fact. Rewrite using `[hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]`. Conclude with `this`. Set `a' : Weil h →* (w.adicCompletion E)ˣ` to `invMonoidHom.comp a`. Establish `ha' : Function.Surjective a'` using `inv_surjective.comp ha.surj`.

Establish `hker : a'.ker ≤ r.ker` using `fun τ hτ => by`. Establish `h1 : a τ = 1` using `inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)`. Use `MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `hnorm τ L (h1 ▸ Subgroup.one_mem _)`.

Set `b` to `a'.liftOfSurjective ha' ⟨r, hker⟩`. Establish `hb : ∀ τ, b (a τ)⁻¹ = r τ` using `fun τ => MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ`. Establish `hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w)`. Use `eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `ha' π`.

Establish `h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1` using `by rw [map_inv]; exact hπ`. Rewrite `h1` using `[ha.ord_eq, deg_inv, neg_neg]`. Establish `hF` using `(GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)`. Express the relevant statement in the definitionally equal form `restrictAb _ _ (b (a τ)⁻¹) = _`. Rewrite using `[hb, hr]`.

Use `(restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_` and prove the remaining obligations. Rewrite using `[unramifiedDegree_eq_ofAdd_one_iff]`. Introduce and unpack `ξ ⟨n, hn, hξ⟩`. Establish `hq : Nat.card 𝓀[w.adicCompletion E] = normV w` using `resCard_eq_normV w`. Rewrite `hξ`, the goal using `[hq]`.

Use `hF ξ n (Nat.pos_of_ne_zero hn) ?_` and prove the remaining obligations. Establish `h2 : normV w ^ n = normV w ^ n - 1 + 1` using `(Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (one_lt_normV w)))).symm`. Rewrite using `[h2, pow_succ, hξ, one_mul]`. Take `⟨τ, rfl⟩` from `ha' x`. Express the relevant statement in the definitionally equal form `restrictAb _ _ (b (a τ)⁻¹) = _`.

Rewrite using `[hb]`. Conclude with `hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)`. Rewrite using `[← map_inv, ← hbφ, hb, ← e2]`. Both sides reduce to the same expression.
-/
theorem restrict_eq_inv_localArtinMap : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
        (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
  have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
  obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
  have e2 : ψ σ = g := by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
  have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
      (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
    restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
  have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
      [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
      a τ ∈ (normUnits (w.adicCompletion E) L).range →
        restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
    have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
    rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
    exact this
  let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
  have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
  have hker : a'.ker ≤ r.ker := fun τ hτ => by
    have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
    refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
    rw [map_one]
    exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
  let b := a'.liftOfSurjective ha' ⟨r, hker⟩
  have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
    MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
  have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
    refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
    · obtain ⟨τ, rfl⟩ := ha' π
      have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
      rw [ha.ord_eq, deg_inv, neg_neg] at h1
      have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb, hr]
      refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
      rw [unramifiedDegree_eq_ofAdd_one_iff]
      rintro ξ ⟨n, hn, hξ⟩
      have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := resCard_eq_normV w
      rw [hq] at hξ ⊢
      refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
      have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (one_lt_normV w)))).symm
      rw [h2, pow_succ, hξ, one_mul]
    · obtain ⟨τ, rfl⟩ := ha' x
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb]
      exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
  rw [← map_inv, ← hbφ, hb, ← e2]
  rfl

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h Ω' _ _ _ j hj hA a ha σ g hg`. Establish `: CharZero (w.adicCompletion E)` using `charZero_of_injective_algebraMap (algebraMap E _).injective`. Establish `: IsSepClosure (w.adicCompletion E) (Kbar w)` using `⟨inferInstance, inferInstance⟩`. Set `ε : Ω' ≃ₐ[w.adicCompletion E] Kbar w` to `IsSepClosure.equiv (w.adicCompletion E) Ω' (Kbar w)`. Set `ι : Ω →ₐ[E] Kbar w` to `{ (ε : Ω' →+* Kbar w).comp j with commutes' := fun x => by`.

Express the relevant statement in the definitionally equal form `ε (j (algebraMap E Ω x)) = _`. Rewrite using `[hj, ε.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)] }`. Establish `hιz : ∀ z, ι z = ε (j z)` using `fun _ => rfl`. Establish `hc : (ε : Ω' →+* Kbar w).comp ((algebraMap (w.adicCompletion E) Ω').comp (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) = algebraMap (w.adicCompletionIntegers E) (Kbar w)` using `RingHom.ext fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply (w.adicCompletionIntegers E) (w.adicCompletion E) (Kbar w)]`.

Conclude with `ε.commutes _`. Establish `hι : IsLocEmb A w ι` using `fun z => by`. Rewrite using `[hA, hιz]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, hp'⟩`.

Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Use `congrArg (ε : Ω' →+* Kbar w) hp'` as an intermediate fact. Rewrite `this` using `[Polynomial.hom_eval₂, map_zero]`. Then use the resulting hypothesis. Introduce and unpack `⟨p, hp, hp'⟩`.

Use `⟨p, hp, (ε : Ω' →+* Kbar w).injective ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.hom_eval₂, map_zero, hc]`. Conclude with `hp'`. Set `g' : GalLoc w` to `ε.symm.trans (g.trans ε)`. Establish `hg' : Lifts ι g' σ` using `fun z => by`.

Express the relevant statement in the definitionally equal form `ε (g (ε.symm (ε (j z)))) = ε (j _)`. Rewrite using `[ε.symm_apply_apply, hg]`. Establish `H` using `restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ g' hg'`. Establish `H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g = (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹`. Rewrite `H`, the goal using `[← map_inv]`.

Use extensionality with `y`. Establish `h1` using `localArtinMap_transport (RingEquiv.refl (w.adicCompletion E)) (fun _ _ => Iff.rfl) (ε : Ω' ≃+* Kbar w) (fun x => ε.commutes x) (a σ)⁻¹ y.2`. Establish `h2 : Units.map (RingEquiv.refl (w.adicCompletion E)).toRingHom.toMonoidHom (a σ)⁻¹ = (a σ)⁻¹` using `Units.ext rfl`. Rewrite `h1` using `[h2, ← H, AlgEquiv.restrictNormalHom_apply]`. Rewrite using `[AlgEquiv.restrictNormalHom_apply]`.

Apply `ε.injective` to reduce the goal to its premises. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ε (g (ε.symm (ε y)))`. Rewrite using `[ε.symm_apply_apply]`. Use `⟨H1, fun M _ _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[← restrictAb_localArtinMap, ← map_inv, ← H1]`. Conclude with `(restrictAb_topologicalAbelianizationEquiv M (le_maximalAbelianExtension M) g).symm`.
-/
theorem restrict_eq_inv_reciprocity : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (Ω' : Type) [Field Ω'] [Algebra (w.adicCompletion E) Ω'] [IsSepClosure (w.adicCompletion E) Ω'] (j : Ω →+* Ω'),
    (∀ x : E, j (algebraMap E Ω x) = algebraMap (w.adicCompletion E) Ω' (algebraMap E (w.adicCompletion E) x)) →
    (∀ z : Ω, z ∈ A ↔ ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).IsIntegralElem (j z)) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ (σ : Weil h) (g : Ω' ≃ₐ[w.adicCompletion E] Ω'), (∀ z : Ω, g (j z) = j ((σ : G E Ω) z)) →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
        (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ ∧
      ∀ (M : IntermediateField (w.adicCompletion E) Ω') [FiniteDimensional (w.adicCompletion E) M]
        [IsAbelianGalois (w.adicCompletion E) M],
        AlgEquiv.restrictNormalHom M g =
          ((localReciprocityAbelian M).symm
            (a σ : (w.adicCompletion E)ˣ ⧸ (normUnits (w.adicCompletion E) M).range))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h Ω' _ _ _ j hj hA a ha σ g hg
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : IsSepClosure (w.adicCompletion E) (Kbar w) := ⟨inferInstance, inferInstance⟩
  let ε : Ω' ≃ₐ[w.adicCompletion E] Kbar w := IsSepClosure.equiv (w.adicCompletion E) Ω' (Kbar w)
  let ι : Ω →ₐ[E] Kbar w :=
    { (ε : Ω' →+* Kbar w).comp j with
      commutes' := fun x => by
        change ε (j (algebraMap E Ω x)) = _
        rw [hj, ε.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)] }
  have hιz : ∀ z, ι z = ε (j z) := fun _ => rfl
  have hc : (ε : Ω' →+* Kbar w).comp ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) =
      algebraMap (w.adicCompletionIntegers E) (Kbar w) := RingHom.ext fun x => by
    rw [IsScalarTower.algebraMap_apply (w.adicCompletionIntegers E) (w.adicCompletion E) (Kbar w)]
    exact ε.commutes _
  have hι : IsLocEmb A w ι := fun z => by
    rw [hA, hιz]
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      rw [← hc]
      have := congrArg (ε : Ω' →+* Kbar w) hp'
      rwa [Polynomial.hom_eval₂, map_zero] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (ε : Ω' →+* Kbar w).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hc]
      exact hp'
  let g' : GalLoc w := ε.symm.trans (g.trans ε)
  have hg' : Lifts ι g' σ := fun z => by
    change ε (g (ε.symm (ε (j z)))) = ε (j _)
    rw [ε.symm_apply_apply, hg]
  have H := restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ g' hg'
  have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
      (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ := by
    rw [← map_inv] at H ⊢
    ext y
    have h1 := localArtinMap_transport (RingEquiv.refl (w.adicCompletion E)) (fun _ _ => Iff.rfl)
      (ε : Ω' ≃+* Kbar w) (fun x => ε.commutes x) (a σ)⁻¹ y.2
    have h2 : Units.map (RingEquiv.refl (w.adicCompletion E)).toRingHom.toMonoidHom (a σ)⁻¹ = (a σ)⁻¹ :=
      Units.ext rfl
    rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
    rw [AlgEquiv.restrictNormalHom_apply]
    apply ε.injective
    refine Eq.trans ?_ h1.symm
    change _ = ε (g (ε.symm (ε y)))
    rw [ε.symm_apply_apply]
  refine ⟨H1, fun M _ _ => ?_⟩
  rw [← restrictAb_localArtinMap, ← map_inv, ← H1]
  exact (restrictAb_topologicalAbelianizationEquiv M (le_maximalAbelianExtension M) g).symm

end GlobalTheory.ArtinCompare
