import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.TorRef.DomFine

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem generalizing_of_stalk {Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) : GeneralizingMap ξ := by
  have h₁ : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := by
    rw [Flat.SpecMap_iff]; exact hf
  have h₂ : GeneralizingMap (Y.fromSpecStalk (ξ (closedPoint _))) := by
    refine (Y.fromSpecStalk (ξ (closedPoint _))).isEmbedding.isInducing.generalizingMap ?_
    rw [Scheme.range_fromSpecStalk]
    exact fun a b hab hb => hab.trans hb
  have e : (ξ : Sp A → Y) = Y.fromSpecStalk (ξ (closedPoint _)) ∘ Spec.map (Scheme.stalkClosedPointTo ξ) := by
    funext p
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    exact Scheme.Hom.comp_apply _ _ _
  rw [e]
  exact (Flat.generalizingMap _).comp h₂

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem flat_stalk_of_comp {X Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : (Scheme.stalkClosedPointTo (ξ ≫ f)).hom.Flat) :
    (Scheme.stalkClosedPointTo ξ).hom.Flat := by
  rw [Scheme.stalkClosedPointTo_comp] at hf
  have e : Scheme.stalkClosedPointTo ξ =
      inv (f.stalkMap (ξ (closedPoint _))) ≫ (f.stalkMap (ξ (closedPoint _)) ≫ Scheme.stalkClosedPointTo ξ) := by
    simp
  rw [e, CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ hf
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_specializes {Y : Scheme.{0}} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) (w : Sp (FractionRing A)) (q : Y) (h : q ⤳ (jK A ≫ ξ) w) :
    q = (jK A ≫ ξ) w := by
  rw [Scheme.Hom.comp_apply] at h ⊢
  obtain ⟨r, hr, rfl⟩ := generalizing_of_stalk ξ hf h
  have hw : (jK A w).asIdeal = ⊥ := by
    haveI : (PrimeSpectrum.asIdeal w).IsPrime := PrimeSpectrum.isPrime w
    have hw₀ : PrimeSpectrum.asIdeal w = ⊥ := Ideal.eq_bot_of_prime _
    ext x
    change algebraMap A (FractionRing A) x ∈ PrimeSpectrum.asIdeal w ↔ _
    rw [hw₀, Ideal.mem_bot, Ideal.mem_bot]
    exact map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))
  have hle := (PrimeSpectrum.le_iff_specializes (R := A) r (jK A w)).mpr hr
  have : r = jK A w := by
    apply le_antisymm hle
    change (jK A w).asIdeal ≤ PrimeSpectrum.asIdeal r
    rw [hw]; exact bot_le
  rw [this]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mem_range_of_generic {U V : Scheme.{0}} (j : U ⟶ V) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [TopologicalSpace.NoetherianSpace V] (g : V) (hg : ∀ q : V, q ⤳ g → q = g) : g ∈ Set.range j := by
  have hc : closure {g} ∈ irreducibleComponents V := by
    refine ⟨isIrreducible_singleton.closure, fun S hS hle => ?_⟩
    have hq := hS.isGenericPoint_genericPoint_closure
    have hgS : g ∈ S := hle (subset_closure rfl)
    have e := hg _ (hq.specializes (subset_closure hgS))
    rw [e] at hq
    exact subset_closure.trans hq.def.symm.subset
  obtain ⟨o, ho, hne, hle⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨u, hu, hu'⟩ := hd.inter_open_nonempty o ho hne
  have hs : g ⤳ u := specializes_iff_mem_closure.2 (hle hu)
  exact j.isOpenEmbedding.isOpen_range.stableUnderGeneralization hs hu'

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem eq_of_jK {A B : Type} [CommRing A] [IsDomain A] [CommRing B] (u v : Sp A ⟶ Sp B) (h : jK A ≫ u = jK A ≫ v) :
    u = v := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective u
  obtain ⟨g, rfl⟩ := Spec.map_surjective v
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext x
  apply IsFractionRing.injective A (FractionRing A)
  exact ConcreteCategory.congr_hom h' x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem isUnit_of_point {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [IsLocalRing R'] (a : O) (b : O →+* R)
    (hloc : @IsLocalization.Away O _ a R _ b.toAlgebra) {X : Scheme.{0}} (s : X ⟶ Sp O) (ξ₀ : Sp R' ⟶ X) (κ : O →+* R')
    (hκ : spMap κ = ξ₀ ≫ s) (x : ↥(pullback s (spMap b))) (hz : ξ₀ (closedPoint R') = pullback.fst s (spMap b) x) :
    IsUnit (κ a) := by
  by_contra hn
  have h1 : a ∈ PrimeSpectrum.asIdeal (spMap κ (closedPoint R')) := (mem_maximalIdeal _).2 hn
  have e : spMap κ (closedPoint R') = spMap b (pullback.snd s (spMap b) x) := by
    rw [hκ]
    refine (Scheme.Hom.comp_apply ξ₀ s _).trans ?_
    rw [hz]
    refine (Scheme.Hom.comp_apply (pullback.fst s (spMap b)) s x).symm.trans ?_
    rw [pullback.condition]
    exact Scheme.Hom.comp_apply _ _ x
  rw [e] at h1
  have h2 : b a ∈ PrimeSpectrum.asIdeal (pullback.snd s (spMap b) x) := h1
  have hu : IsUnit (b a) := by
    letI := b.toAlgebra
    haveI : IsLocalization.Away a R := hloc
    exact IsLocalization.Away.algebraMap_isUnit a
  exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem injective_of_flat {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat)
    (κ : O →+* A) (hκ : spMap κ = ξ₀ ≫ s) : Function.Injective ((algebraMap A (FractionRing A)).comp κ) := by
  have hsρ : spMap ((algebraMap A (FractionRing A)).comp κ) = (jK A ≫ ξ₀) ≫ s := by
    rw [← spMap_comp', hκ, Category.assoc]
  refine GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ (⊥ : PrimeSpectrum (FractionRing A)) ?_
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s
    (genericPoint_specializes (s ((jK A ≫ ξ₀) (⊥ : PrimeSpectrum (FractionRing A)))))
  have h := eq_of_specializes ξ₀ hfl (⊥ : PrimeSpectrum (FractionRing A)) y hy
  rw [hsρ]
  refine (Scheme.Hom.comp_apply (jK A ≫ ξ₀) s _).trans ?_
  rw [← h, e]

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem exists_lift_frac {O F B : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F] [CommRing B]
    (g : O →+* B) (hu : ∀ y : O, y ≠ 0 → IsUnit (g y)) : ∃ ρ : F →+* B, ρ.comp (algebraMap O F) = g := by
  have hu' : ∀ y : nonZeroDivisors O, IsUnit (g y) := fun y => hu _ (nonZeroDivisors.ne_zero y.2)
  exact ⟨IsLocalization.lift hu', IsLocalization.lift_comp hu'⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_generic_fibre {O F A : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X)
    (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ v : Sp (FractionRing A) ⟶ pullback s (spMap (algebraMap O F)), v ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ s)
  obtain ⟨κ, rfl⟩ : ∃ κ : O →+* A, CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ s := hκ'
  have hρ := injective_of_flat s hs ξ₀ hfl κ hκ
  obtain ⟨ρ', hρ'⟩ := exists_lift_frac (F := F) ((algebraMap A (FractionRing A)).comp κ) (fun y hy => by
    have h0 : κ y ≠ 0 := fun h => hy (hρ (by simp [h]))
    exact IsLocalization.map_units (FractionRing A) (⟨κ y, mem_nonZeroDivisors_of_ne_zero h0⟩ : nonZeroDivisors A))
  have hv : (jK A ≫ ξ₀) ≫ s = spMap ρ' ≫ spMap (algebraMap O F) := by
    rw [spMap_comp', hρ', ← spMap_comp', hκ, Category.assoc]
  exact ⟨pullback.lift (jK A ≫ ξ₀) _ hv, pullback.lift_fst _ _ _⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_generic_point (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    (X U : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap (algebraMap O F))) (hs : Flat s) (hp : IsProjOver s)
    (hj : IsOpenImmersion jQ) (hd : Dense (Set.range jQ)) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ y : Sp (FractionRing A) ⟶ U, y ≫ jQ ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨v, v1⟩ := exists_generic_fibre (F := F) s hs ξ₀ hfl
  obtain ⟨hN, hC, -⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ hs hp hj hd
  haveI : IsNoetherian X := {}
  have hb0 : IsPreimmersion (spMap (algebraMap O F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  haveI h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb0
  haveI hNs : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap (algebraMap O F))) :=
    (pullback.fst s (spMap (algebraMap O F))).isEmbedding.isInducing.noetherianSpace
  have hr : Set.range v ⊆ Set.range jQ := by
    rintro _ ⟨w, rfl⟩
    refine mem_range_of_generic jQ hd _ fun q hq => ?_
    have h' := hq.map (pullback.fst s (spMap (algebraMap O F))).continuous
    have e : (pullback.fst s (spMap (algebraMap O F))) (v w) = (jK A ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, v1]
    rw [e] at h'
    exact (pullback.fst s (spMap (algebraMap O F))).isEmbedding.injective ((eq_of_specializes ξ₀ hfl w _ h').trans e.symm)
  refine ⟨IsOpenImmersion.lift jQ v hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, v1]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Equip the data with the indicated structure.

Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_ext_at_points : FreeSt → ExtendSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → ∀ (m : ℕ), 1 ≤ m → AmpAt C m → (∀ z : Z.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ Z.X) (t : SAB H (Sp R')) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R') t), IsCN R' ∧ ξ (closedPoint R') = z ∧ (Scheme.stalkClosedPointTo ξ).hom.Flat ∧ FineData P.D.toPre 1 ∧ FineData P.D.toPre (m ^ 2)) → ∀ jX : Xo.XF c ⟶ pullback Z.s (spMap b), jX ≫ pullback.fst _ _ = Z.j → ∀ x : ↥(pullback Z.s (spMap b)), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ pullback Z.s (spMap b)) (y : Sp (FractionRing R') ⟶ Xo.XF c) (χ : Sp R' ⟶ C.X), ξ (closedPoint R') = x ∧ (Scheme.stalkClosedPointTo ξ).hom.Flat ∧ y ≫ jX = jK R' ≫ ξ ∧ jK R' ≫ χ = y ≫ C.j ∧ χ ≫ C.s = ξ ≫ pullback.snd _ _ ∧ ∀ (w : Sp (FractionRing R')) (q : ↥(pullback Z.s (spMap b))), q ⤳ (jK R' ≫ ξ) w → q = (jK R' ≫ ξ) w := by
  intro hFree hExt E _ _ _ H D l Xo c Z R _ a b ω C hω hωb hloc m hm hAmp hpts jX hjX x
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  haveI hopen : IsOpenImmersion (spMap b) := by
    letI := b.toAlgebra
    haveI : IsLocalization.Away a R := hloc
    exact IsOpenImmersion.of_isLocalization a
  obtain ⟨R', iR, iD, iL, ξ₀, t, μ, P, hCN, hz, hfl, hF1, hF2⟩ := hpts (pullback.fst Z.s (spMap b) x)
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ Z.s)
  obtain ⟨κ, rfl⟩ : ∃ κ : 𝓞 c.F →+* R', CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ Z.s := hκ'
  have hua : IsUnit (κ a) := isUnit_of_point a b hloc Z.s ξ₀ κ hκ x hz
  obtain ⟨b', hb'⟩ : ∃ b' : R →+* R', b'.comp b = κ := by
    letI := b.toAlgebra
    haveI : IsLocalization.Away a R := hloc
    exact ⟨IsLocalization.Away.lift a hua, IsLocalization.Away.lift_comp a hua⟩
  have hsb : spMap b' ≫ spMap b = ξ₀ ≫ Z.s := by rw [spMap_comp', hb', hκ]
  obtain ⟨ξ, e1, e2⟩ : ∃ ξ : Sp R' ⟶ pullback Z.s (spMap b), ξ ≫ pullback.fst _ _ = ξ₀ ∧ ξ ≫ pullback.snd _ _ = spMap b' :=
    ⟨pullback.lift ξ₀ (spMap b') hsb.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hinjf : Function.Injective (pullback.fst Z.s (spMap b)) := (pullback.fst Z.s (spMap b)).isOpenEmbedding.injective
  have hclosed : ξ (closedPoint R') = x := hinjf
    ((Scheme.Hom.comp_apply ξ (pullback.fst Z.s (spMap b)) _).symm.trans (by rw [e1]; exact hz))
  have hflat : (Scheme.stalkClosedPointTo ξ).hom.Flat :=
    flat_stalk_of_comp ξ (pullback.fst Z.s (spMap b)) (by rw [e1]; exact hfl)
  have hlast : ∀ (w : Sp (FractionRing R')) (q : ↥(pullback Z.s (spMap b))), q ⤳ (jK R' ≫ ξ) w → q = (jK R' ≫ ξ) w := by
    intro w q h
    apply hinjf
    have h' := h.map (pullback.fst Z.s (spMap b)).continuous
    have e : (pullback.fst Z.s (spMap b)) ((jK R' ≫ ξ) w) = (jK R' ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, e1]
    rw [e] at h' ⊢
    exact eq_of_specializes ξ₀ hfl w _ h'
  obtain ⟨y, hyj'⟩ := exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense ξ₀ hfl
  have hyj : y ≫ Z.j = jK R' ≫ ξ₀ := hyj'
  have hyX : y ≫ jX = jK R' ≫ ξ := by
    rw [← cancel_mono (pullback.fst Z.s (spMap b)), Category.assoc, hjX, hyj, Category.assoc, e1]
  have hjs : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over]
  have hjC : C.j ≫ C.s = pullback.snd _ _ ≫ spMap ω := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hs : jK R' ≫ spMap b' = (y ≫ pullback.snd _ _) ≫ spMap ω :=
    GlobalTheory.Models.Domination.eq_of_overring hβ hω hωb (jK R' ≫ spMap b') (y ≫ pullback.snd _ _) (by
      rw [Category.assoc, hsb, ← Category.assoc, ← hyj, Category.assoc, hjs, Category.assoc])
  have hC1 : y ≫ C.j ≫ C.s = jK R' ≫ spMap b' := by
    rw [hjC, hs, Category.assoc]
  obtain ⟨χ, hχ⟩ := hExt E H D l Xo c R (𝓞 c.F) ω (algebraMap _ _) C Z R' ξ₀ t μ y b' m hCN hyj hC1 hAmp
    (hFree E H R' t P 1 hCN le_rfl hF1) (hFree E H R' t P (m ^ 2) hCN (Nat.one_le_pow _ _ hm) hF2)
  refine ⟨R', iR, iD, iL, ξ, y, χ, hclosed, hflat, hyX, hχ, ?_, hlast⟩
  rw [e2]
  apply eq_of_jK
  rw [← Category.assoc, hχ, Category.assoc, hC1]

end GlobalTheory.TorRef.DomFine
