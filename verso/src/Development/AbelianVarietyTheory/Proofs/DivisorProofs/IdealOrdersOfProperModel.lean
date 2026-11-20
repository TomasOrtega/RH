import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

/- English proof (translation)
Introduce `g n F W8 Z i φ X₁ Y πY hhom hprop ι J₁ hsupp hord hφ`. Use `haveI := hprop`. Establish `hsurj : Function.Surjective πY`. Establish `hgen : genericPoint X₁.M.Z ∈ Set.range πY`. Establish `w : Sp X₁.Ω₁` using `IsLocalRing.closedPoint X₁.Ω₁`.

Use `⟨Y.pt w, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)`. Simplify using `only [Scheme.Hom.comp_apply] at h`. Rewrite using `[h]`. Conclude with `X₁.M.pt_apply _`.

Establish `hcl : IsClosed (Set.range πY)` using `πY.isClosedMap.isClosed_range`. Introduce `x`. Establish `: x ∈ closure (Set.range πY)` using `closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)`. Rewrite `this` using `[hcl.closure_eq]`. Then use the resulting hypothesis. Use `⟨fun x hx => ?_, fun T ξ₁ hT => ?_⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hsurj x`. Conclude with `hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)`. Take `⟨K', _, σ, yK, hσ, hy⟩` from `GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType πY inferInstance hsurj (FractionRing T.V) (jK T.V ≫ ξ₁)`. Take `⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩` from `GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing T.V T.complete K' σ hσ`. Establish `hfK : ∀ a, (τ.comp σ) (algebraMap T.V _ a) = algebraMap V' _ (f a)` using `hτ`.

Take `⟨ξ', hξπ, hξg⟩` from `GlobalTheory.T.proper_lift_trait_of_generic_lift πY hprop T.V V' f (τ.comp σ) hfK ξ₁ (spMap τ ≫ yK) (by`. Rewrite using `[Category.assoc, hy, spMap_comp, Category.assoc])`. Establish `hB' : GlobalTheory.Mum.Base V'` using `⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩`. Take `⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩` from `GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB' inferInstance (spMap (τ.comp σ) ≫ T.y)`. Use `haveI := hfl`.

Use `haveI := hf₂l`. Establish `hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S) (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) → jK S ≫ spMap u = spMap uK ≫ jK R`. Introduce `R S _ _ _ _ u uK hu`. Express the relevant statement in the definitionally equal form `spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))`. Rewrite using `[← spMap_comp, ← spMap_comp]`.

Conclude with `congrArg spMap (RingHom.ext fun a => (hu a).symm)`. Establish `hcomm : jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = T₂.y ≫ i`. Establish `e1` using `hjK f₂ fK₂ hf₂K`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Category.assoc]`.

Use `_ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]`. Use `_ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]`. Use `_ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK T.V ≫ ξ₁ ≫ X₁.π) := by rw [hy]; simp only [Category.assoc]`. Use `_ = T₂.y ≫ i := by rw [hT, hT₂y, spMap_comp]; simp only [Category.assoc]`. Take `⟨a', ha', hid⟩` from `hord T₂ (spMap f₂ ≫ ξ') hcomm`.

Rewrite `hid` using `[GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp, GlobalTheory.TraitOrder.idlAlong_comp]`. Use `set h := f₂.comp f with hh`. Establish `hinj : Function.Injective h` using `hf₂i.comp hfi`. Establish `hloc : IsLocalHom h` using `inferInstance`. Establish `hne : h T.ϖ ≠ 0` using `(map_ne_zero_iff h hinj).2 T.irr.ne_zero`.

Take `⟨e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr`. Establish `he1 : 1 ≤ e`. Break down `Nat.eq_zero_or_pos e with rfl | hpos` into its components or cases. Conclude with `absurd ((isUnit_map_iff h T.ϖ).1 (he.isUnit_iff.2 (by simp))) T.irr.not_isUnit`. Conclude with `hpos`.

Take `⟨b, hb, hI⟩` from `GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr T.V T₂.V h hinj T.ϖ T₂.ϖ e a' _ T.irr T₂.irr he hid`. Establish `hB₂ : GlobalTheory.Mum.Base T₂.V` using `⟨⟨inferInstance, inferInstance, inferInstance, T₂.complete⟩, inferInstance⟩`. Take `⟨eq, heq⟩` from `GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n _ _ F T T₂ T₂.V h (RingHom.id _) (fK₂.comp (τ.comp σ)) (RingHom.id _) hB₂ inferInstance hinj Function.injective_id hloc inferInstance (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (fun _ => rfl) (by`. Rewrite using `[hT₂y, spMap_comp, Category.assoc]`. Establish `hid1 : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _`.

Simplify using `[spMap]`. Rewrite using `[hid1, Category.id_comp]) T₂.ϖ e 1 T₂.irr he (by simp)`. Establish `hval : φ.evalZ T₂.β = e * φ.evalZ T.β`. Rewrite using `[← hφ T e he1]`. Unfold `InvFun.evalZ`.

Rewrite using `[← φ.eval_equiv eq.toIntLinearEquiv]`. Use `congr 1`. Use extensionality with `a c`. Use `heq a c` as an intermediate fact. Simplify using `only [Nat.cast_one, one_mul] at this`.

Simplify using `[AddEquiv.coe_toIntLinearEquiv, ← this]`. Use `⟨b, ?_, hI⟩` and prove the remaining obligations. Establish `h1 : (e : ℝ) * b = e * (ι * φ.evalZ T.β)`. Rewrite using `[← Nat.cast_mul, hb, ha', hval]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (e : ℝ) ≠ 0` using `by exact_mod_cast (by omega : e ≠ 0)`. Conclude with `mul_left_cancel₀ h2 h1`.
-/
theorem _root_.GlobalTheory.Poinc.ideal_orders_of_proper_model : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a}) → (∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β) → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n F W8 Z i φ X₁ Y πY hhom hprop ι J₁ hsupp hord hφ
  haveI := hprop

  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, fun T ξ₁ hT => ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  ·
    obtain ⟨K', _, σ, yK, hσ, hy⟩ := GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType πY inferInstance hsurj (FractionRing T.V) (jK T.V ≫ ξ₁)
    obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ := GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing T.V T.complete K' σ hσ
    have hfK : ∀ a, (τ.comp σ) (algebraMap T.V _ a) = algebraMap V' _ (f a) := hτ
    obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.T.proper_lift_trait_of_generic_lift πY hprop T.V V' f (τ.comp σ) hfK ξ₁ (spMap τ ≫ yK) (by
      rw [Category.assoc, hy, spMap_comp, Category.assoc])
    have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
    obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
      GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB' inferInstance (spMap (τ.comp σ) ≫ T.y)
    haveI := hfl
    haveI := hf₂l
    have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
        (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
        jK S ≫ spMap u = spMap uK ≫ jK R := by
      intro R S _ _ _ _ u uK hu
      change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

    have hcomm : jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = T₂.y ≫ i := by
      have e1 := hjK f₂ fK₂ hf₂K
      calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
            simp only [Category.assoc]
        _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK T.V ≫ ξ₁ ≫ X₁.π) := by rw [hy]; simp only [Category.assoc]
        _ = T₂.y ≫ i := by rw [hT, hT₂y, spMap_comp]; simp only [Category.assoc]
    obtain ⟨a', ha', hid⟩ := hord T₂ (spMap f₂ ≫ ξ') hcomm
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
      GlobalTheory.TraitOrder.idlAlong_comp] at hid

    set h := f₂.comp f with hh
    have hinj : Function.Injective h := hf₂i.comp hfi
    have hloc : IsLocalHom h := inferInstance
    have hne : h T.ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 T.irr.ne_zero
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd ((isUnit_map_iff h T.ϖ).1 (he.isUnit_iff.2 (by simp))) T.irr.not_isUnit
      · exact hpos
    obtain ⟨b, hb, hI⟩ := GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr T.V T₂.V h hinj T.ϖ T₂.ϖ e a' _ T.irr T₂.irr he hid

    have hB₂ : GlobalTheory.Mum.Base T₂.V := ⟨⟨inferInstance, inferInstance, inferInstance, T₂.complete⟩, inferInstance⟩
    obtain ⟨eq, heq⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n _ _ F T T₂ T₂.V h (RingHom.id _) (fK₂.comp (τ.comp σ)) (RingHom.id _)
      hB₂ inferInstance hinj Function.injective_id hloc inferInstance
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (fun _ => rfl)
      (by
        rw [hT₂y, spMap_comp, Category.assoc]
        have hid1 : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
          simp [spMap]
        rw [hid1, Category.id_comp]) T₂.ϖ e 1 T₂.irr he (by simp)
    have hval : φ.evalZ T₂.β = e * φ.evalZ T.β := by
      rw [← hφ T e he1]
      unfold InvFun.evalZ
      rw [← φ.eval_equiv eq.toIntLinearEquiv]
      congr 1
      ext a c
      have := heq a c
      simp only [Nat.cast_one, one_mul] at this
      simp [AddEquiv.coe_toIntLinearEquiv, ← this]
    refine ⟨b, ?_, hI⟩
    have h1 : (e : ℝ) * b = e * (ι * φ.evalZ T.β) := by
      rw [← Nat.cast_mul, hb, ha', hval]; ring
    have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    exact mul_left_cancel₀ h2 h1
