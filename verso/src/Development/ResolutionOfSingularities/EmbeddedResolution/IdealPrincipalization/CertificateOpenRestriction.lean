import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

noncomputable def comapSubscheme {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    (D.comap f).subscheme ⟶ D.subscheme :=
  Scheme.IdealSheafData.subschemeMap (D.comap f) D f (D.le_map_comap f)

/- English proof (authored)
The map of closed subschemes is induced by the given ambient morphism and the pulled-back ideal. The defining compatibility of that map is that its composite with the original inclusion equals the pulled-back inclusion followed by the ambient morphism.
-/
theorem comapSubscheme_comp {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    comapSubscheme f D ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  simp [comapSubscheme]

/- English proof (authored)
Compose the compatibility of the induced subscheme map with the remaining morphism. Associativity gives the stated equality.
-/
theorem comapSubscheme_comp_assoc {V W T : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData)
    (g : W ⟶ T) :
    comapSubscheme f D ≫ D.subschemeι ≫ g = (D.comap f).subschemeι ≫ f ≫ g := by
  rw [← Category.assoc, comapSubscheme_comp, Category.assoc]

structure OpenImmersionStability (k : Type u) [Field k] : Prop where
  comap_nonzeroOnComponents :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (J : W.IdealSheafData),
      NonzeroOnComponents J → NonzeroOnComponents (J.comap f)
  isOpenImmersion_comapSubscheme :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (D : W.IdealSheafData),
      IsOpenImmersion (comapSubscheme f D)
  comap_isSmoothDivisor :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
      (p : W ⟶ Spec (CommRingCat.of k)) (D : W.IdealSheafData),
      IsSmoothDivisor p D → IsSmoothDivisor (f ≫ p) (D.comap f)

/- English proof (authored)
The support of an ideal sheaf pulled back to a scheme is the inverse image of its original support, since the pulled-back ideal defines the base-changed closed subscheme.
-/
private theorem coe_support_comap {V W : Scheme.{u}} (f : V ⟶ W) (Z : W.IdealSheafData) :
    ((Z.comap f).support : Set ↥V) = ⇑f.base ⁻¹' ((Z.support : Set ↥W)) := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

/- English proof (authored)
A point maps into the given set under the composite exactly when its image under the first map is in the inverse image under the second. This is the nested inverse-image formula.
-/
private theorem preimage_base_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (S : Set ↥C) :
    ⇑(a ≫ b).base ⁻¹' S = ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) := by
  ext w
  exact Iff.rfl

/- English proof (authored)
Each nested inverse image is the inverse image under its composite. Equal composites have the same inverse image.
-/
private theorem preimage_base_preimage_base_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (e : a ≫ b = c ≫ d) (S : Set ↥D) :
    ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) = ⇑c.base ⁻¹' (⇑d.base ⁻¹' S) := by
  rw [← preimage_base_comp, ← preimage_base_comp, e]

/- English proof (authored)
Use the equalities of the structure maps, input ideals, memory sets and target ideals to identify all certificate parameters. The given certificate then has the required data.
-/
private theorem principalizationCertificate_congr {k : Type u} [Field k] {A : Scheme.{u}}
    {p₁ p₂ : A ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : A.IdealSheafData} {m : ℕ}
    {Mem₁ Mem₂ : Set ↥A} {Z₁ Z₂ : A.IdealSheafData}
    (h : PrincipalizationCertificate A p₁ I₁ m Mem₁ Z₁) (hp : p₁ = p₂) (hI : I₁ = I₂) (hM : Mem₁ = Mem₂)
    (hZ : Z₁ = Z₂) : PrincipalizationCertificate A p₂ I₂ m Mem₂ Z₂ := by
  subst hp; subst hI; subst hM; subst hZ; exact h

/- English proof (authored)
Replace each of the structure map, input ideal, memory and target ideal by its equal value. This gives the required order certificate directly.
-/
private theorem orderCertificate_congr {k : Type u} [Field k] {A : Scheme.{u}}
    {p₁ p₂ : A ⟶ Spec (CommRingCat.of k)} {N₁ N₂ : A.IdealSheafData} {μ : ℕ}
    {Mem₁ Mem₂ : Set ↥A} {Z₁ Z₂ : A.IdealSheafData}
    (h : OrderCertificate A p₁ N₁ μ Mem₁ Z₁) (hp : p₁ = p₂) (hN : N₁ = N₂) (hM : Mem₁ = Mem₂)
    (hZ : Z₁ = Z₂) : OrderCertificate A p₂ N₂ μ Mem₂ Z₂ := by
  subst hp; subst hN; subst hM; subst hZ; exact h

private def IsPrincipalizationCertificateOnOpens {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (⇑f.base ⁻¹' Mem) (Z.comap f)

private def IsOrderCertificateOnOpens {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    OrderCertificate V (f ≫ p) (N.comap f) μ (⇑f.base ⁻¹' Mem) (Z.comap f)

/- English proof (authored)
For any open immersion, the pulled-back target support is the inverse image of the original support. It is contained in the inverse image of memory by the given containment. The memory case therefore gives a principalization certificate on the open.
-/
private theorem comapPrincipalizationCertificate_of_support_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : ((Z.support : Set ↥W)) ⊆ Mem) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f _hf
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap]
  exact Set.preimage_mono h

/- English proof (authored)
The inverse image of the support lies in the inverse image of memory. The support of the pulled-back ideal is that inverse image, so the memory constructor gives an order certificate on every open.
-/
private theorem comapOrderCertificate_of_support_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : ((Z.support : Set ↥W)) ⊆ Mem) :
    IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f _hf
  refine OrderCertificate.memory ?_
  rw [coe_support_comap]
  exact Set.preimage_mono h

/- English proof (authored)
The marking is retained on any open and is at least two. The large-marking constructor supplies a principalization certificate for the pulled-back data.
-/
private theorem comapPrincipalizationCertificate_of_two_le {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hm : 2 ≤ m) : IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f _hf
  exact PrincipalizationCertificate.large hm

/- English proof (authored)
The marking does not change under restriction. Its lower bound still applies, so the large-marking case gives the required order certificate.
-/
private theorem comapOrderCertificate_of_two_le {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hmu : 2 ≤ μ) : IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f _hf
  exact OrderCertificate.large hmu

/- English proof (authored)
Pullback preserves the ideal product and sends the support of the first factor to its inverse image, which lies in the pulled-back memory. The marking inequality stays the same. A point in the pulled-back target support maps to a point where the second factor has the required order. The order inequality for pullback gives at least that order at the source point. The order certificate for the second factor pulls back by hypothesis. These data assemble the principalization certificate on the open.
-/
private theorem comapPrincipalizationCertificate_of_mul_of_order {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : ((M.support : Set ↥W)) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : ((Z.support : Set ↥W)) ⊆ orderAtLeastLocus N μ) (ih : IsOrderCertificateOnOpens W p N μ Mem Z) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f hf
  refine PrincipalizationCertificate.toOrder (M.comap f) (N.comap f) μ ?_ ?_ hmu ?_ (ih V f hf)
  · rw [hI, Scheme.IdealSheafData.comap_mul]
  · rw [coe_support_comap]
    exact Set.preimage_mono hM
  · rw [coe_support_comap]
    intro y hy
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans ((mem_orderAtLeastLocus_iff N μ (f.base y)).mp (hZ hy))
      (orderAt_le_orderAt_comap f N y)

/- English proof (authored)
For each point in the pulled-back target support, its image lies in the original support. Choose the given original neighborhood of that image and take its inverse image. The restricted map to the original neighborhood is an open immersion, so the local hypothesis supplies a principalization certificate there. The commuting square of open inclusions identifies its structural map, ideals and memory with the restrictions of the new ambient data. The localization constructor assembles these certificates.
-/
private theorem comapPrincipalizationCertificate_of_open_cover {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsPrincipalizationCertificateOnOpens (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap] at h1
    exact h1
  refine PrincipalizationCertificate.localize (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (f.base y) (hsup y hy)) ≫ (U (f.base y) (hsup y hy)).ι
      = (f ⁻¹ᵁ U (f.base y) (hsup y hy)).ι ≫ f := morphismRestrict_ι ..
  refine principalizationCertificate_congr (ih (f.base y) (hsup y hy) _ (f ∣_ U (f.base y) (hsup y hy))
    inferInstance) ?_ ?_ ?_ ?_
  · rw [← Category.assoc, e1, Category.assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  · exact preimage_base_preimage_base_of_comp_eq e1 Mem
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]

/- English proof (authored)
Each point of the pulled-back support maps into the original support. Use the inverse image of its original neighborhood, which contains that point. The open restriction of the map gives the local order certificate by hypothesis. Its structural map, pulled-back ideals and memory agree with the required restrictions because the maps through the two open inclusions have equal composites. Apply the localization constructor.
-/
private theorem comapOrderCertificate_of_open_cover {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsOrderCertificateOnOpens (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap] at h1
    exact h1
  refine OrderCertificate.localize (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (f.base y) (hsup y hy)) ≫ (U (f.base y) (hsup y hy)).ι
      = (f ⁻¹ᵁ U (f.base y) (hsup y hy)).ι ≫ f := morphismRestrict_ι ..
  refine orderCertificate_congr (ih (f.base y) (hsup y hy) _ (f ∣_ U (f.base y) (hsup y hy))
    inferInstance) ?_ ?_ ?_ ?_
  · rw [← Category.assoc, e1, Category.assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  · exact preimage_base_preimage_base_of_comp_eq e1 Mem
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]

/- English proof (authored)
Restrict the open immersion to the inverse image of the chosen target open. This is again an open immersion, so the smooth divisor pulls back to a smooth divisor by the stability assumption. The open restriction square identifies its composite structural map with the one in the statement.
-/
private theorem isSmoothDivisor_comap_morphismRestrict {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData)
    (h : IsSmoothDivisor (U'.ι ≫ p) Hd) :
    IsSmoothDivisor ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)) (Hd.comap (f ∣_ U')) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have h2 := hin.comap_isSmoothDivisor (f ∣_ U') (U'.ι ≫ p) Hd h
  have e4 : (f ∣_ U') ≫ (U'.ι ≫ p) = (f ⁻¹ᵁ U').ι ≫ (f ≫ p) := by
    rw [← Category.assoc, e1, Category.assoc]
  rwa [e4] at h2

/- English proof (authored)
The open restriction square identifies pulling back the restricted ambient ideal with restricting the pulled-back ideal. Both supports on the new open are therefore inverse images under the restricted map. Pulling back the original containment gives the result.
-/
private theorem support_comap_morphismRestrict_subset {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (K : W.IdealSheafData)
    (h : ((K.comap U'.ι).support : Set ↥U'.toScheme) ⊆ ((Hd.support : Set ↥U'.toScheme))) :
    ((((K.comap f).comap (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme)) ⊆
      (((Hd.comap (f ∣_ U')).support : Set ↥(f ⁻¹ᵁ U').toScheme)) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (f ⁻¹ᵁ U').ι = (K.comap U'.ι).comap (f ∣_ U') := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  rw [e5, coe_support_comap (f ∣_ U') (K.comap U'.ι), coe_support_comap (f ∣_ U') Hd]
  exact Set.preimage_mono h

/- English proof (authored)
The support on the new open is the inverse image of the relevant support on the old open, by compatibility of ideal pullback with the restriction square. The subscheme map commutes with the two inclusions. Thus the further inverse image on the new subscheme is the inverse image of the given open on the old subscheme. It is open by continuity.
-/
private theorem isOpen_preimage_support_comap_morphismRestrict {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (K : W.IdealSheafData)
    (h : IsOpen (⇑Hd.subschemeι.base ⁻¹'
      (((K.comap U'.ι).support : Set ↥U'.toScheme)))) :
    IsOpen (⇑(Hd.comap (f ∣_ U')).subschemeι.base ⁻¹'
      ((((K.comap f).comap (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme))) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (f ⁻¹ᵁ U').ι = (K.comap U'.ι).comap (f ∣_ U') := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  rw [e5, coe_support_comap (f ∣_ U') (K.comap U'.ι),
    preimage_base_preimage_base_of_comp_eq (comapSubscheme_comp (f ∣_ U') Hd).symm
      (((K.comap U'.ι).support : Set ↥U'.toScheme))]
  exact h.preimage (comapSubscheme (f ∣_ U') Hd).base.hom.continuous

/- English proof (authored)
The restricted ambient map is an open immersion, so the induced map of closed subschemes is an open immersion by the stated stability assumption. Componentwise nonvanishing pulls back along it by that same assumption.
-/
private theorem nonzeroOnComponents_comap_comapSubscheme {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (Jz : Hd.subscheme.IdealSheafData)
    (h : NonzeroOnComponents Jz) :
    NonzeroOnComponents (Jz.comap (comapSubscheme (f ∣_ U') Hd)) := by
  have : IsOpenImmersion (comapSubscheme (f ∣_ U') Hd) :=
    hin.isOpenImmersion_comapSubscheme (f ∣_ U') Hd
  exact hin.comap_nonzeroOnComponents (comapSubscheme (f ∣_ U') Hd) Jz h

/- English proof (authored)
The composite through the new subscheme and open into the original ambient scheme agrees with the route through the original subscheme. A point outside the inverse image of memory therefore maps to a point outside the original memory. Choose the neighborhood of that point on which the two original ideals agree. Its inverse image contains the given point. Pull the equality of ideals back along the restricted subscheme map and use the commuting inclusions to identify the result with the asserted local equality.
-/
private theorem exists_isOpen_comap_eq_comap_morphismRestrict {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (N : W.IdealSheafData) (Mem : Set ↥W)
    (Jz : Hd.subscheme.IdealSheafData)
    (h : ∀ x : ↥Hd.subscheme, (Hd.subschemeι ≫ U'.ι).base x ∉ Mem →
      ∃ V₀ : Hd.subscheme.Opens, x ∈ V₀ ∧
        Jz.comap V₀.ι = ((N.comap U'.ι).comap Hd.subschemeι).comap V₀.ι)
    (x : ↥(Hd.comap (f ∣_ U')).subscheme)
    (hx : ((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x ∉ ⇑f.base ⁻¹' Mem) :
    ∃ V₁ : (Hd.comap (f ∣_ U')).subscheme.Opens, x ∈ V₁ ∧
      (Jz.comap (comapSubscheme (f ∣_ U') Hd)).comap V₁.ι =
        (((N.comap f).comap (f ⁻¹ᵁ U').ι).comap
          (Hd.comap (f ∣_ U')).subschemeι).comap V₁.ι := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e2 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ∣_ U') := comapSubscheme_comp ..
  have e3 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι ≫ U'.ι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι ≫ f := by
    rw [← Category.assoc, e2, Category.assoc, e1]
  have h9 : (Hd.subschemeι ≫ U'.ι).base ((comapSubscheme (f ∣_ U') Hd).base x)
      = f.base (((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x) :=
    congrArg (fun t : (Hd.comap (f ∣_ U')).subscheme ⟶ W => t.base x) e3
  have hx' : (Hd.subschemeι ≫ U'.ι).base ((comapSubscheme (f ∣_ U') Hd).base x) ∉ Mem := by
    intro hmem
    apply hx
    show f.base (((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x) ∈ Mem
    rw [← h9]
    exact hmem
  obtain ⟨V₀, hxV₀, hV₀⟩ := h _ hx'
  refine ⟨(comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀, hxV₀, ?_⟩
  have hc := congrArg (fun K => Scheme.IdealSheafData.comap K
      ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀)) hV₀
  have e7 : ((comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀).ι ≫ comapSubscheme (f ∣_ U') Hd
      = ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀) ≫ V₀.ι := (morphismRestrict_ι ..).symm
  have e8 : ((comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀).ι ≫ (Hd.comap (f ∣_ U')).subschemeι ≫
        (f ⁻¹ᵁ U').ι ≫ f
      = ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀) ≫ V₀.ι ≫ Hd.subschemeι ≫ U'.ι := by
    rw [← e3, ← Category.assoc, e7, Category.assoc]
  simp only [← Scheme.IdealSheafData.comap_comp] at hc ⊢
  rw [e7, e8]
  exact hc

/- English proof (authored)
The restricted map of hypersurfaces is an open immersion by the stability assumption. Apply the hypothesis giving certificates on all opens of the original hypersurface to that map. The commuting open and subscheme inclusions identify its structural map, inverse image of memory and pullback of the target ideal with the prescribed data. The input ideal is already the required pullback.
-/
private theorem principalizationCertificate_comapSubscheme_of_isOpenImmersion {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData) (Z : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (Jz : Hd.subscheme.IdealSheafData)
    (h : IsPrincipalizationCertificateOnOpens Hd.subscheme (Hd.subschemeι ≫ (U'.ι ≫ p)) Jz μ
      (⇑(Hd.subschemeι ≫ U'.ι).base ⁻¹' Mem) ((Z.comap U'.ι).comap Hd.subschemeι)) :
    PrincipalizationCertificate (Hd.comap (f ∣_ U')).subscheme
      ((Hd.comap (f ∣_ U')).subschemeι ≫ ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)))
      (Jz.comap (comapSubscheme (f ∣_ U') Hd)) μ
      (⇑((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base ⁻¹' (⇑f.base ⁻¹' Mem))
      (((Z.comap f).comap (f ⁻¹ᵁ U').ι).comap (Hd.comap (f ∣_ U')).subschemeι) := by
  have hq : IsOpenImmersion (comapSubscheme (f ∣_ U') Hd) :=
    hin.isOpenImmersion_comapSubscheme (f ∣_ U') Hd
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e2 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ∣_ U') := comapSubscheme_comp ..
  have e3 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι ≫ U'.ι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι ≫ f := by
    rw [← Category.assoc, e2, Category.assoc, e1]
  have e3' : comapSubscheme (f ∣_ U') Hd ≫ (Hd.subschemeι ≫ U'.ι)
      = ((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι) ≫ f := by
    rw [Category.assoc]; exact e3
  refine principalizationCertificate_congr (h _ (comapSubscheme (f ∣_ U') Hd) hq) ?_ rfl ?_ ?_
  · have h5 := congrArg (fun t : (Hd.comap (f ∣_ U')).subscheme ⟶ W => t ≫ p) e3
    simpa only [Category.assoc] using h5
  · exact preimage_base_preimage_base_of_comp_eq e3' Mem
  · simp only [← Scheme.IdealSheafData.comap_comp]
    rw [e3]

/- English proof (authored)
For each point of the pulled-back support, choose the inverse image of the original neighborhood of its image. Pull the smooth divisor back to this open. Stability gives smoothness and the support containments pull back. Transport any present auxiliary ideal along the induced map of hypersurfaces, and keep absent values absent.

For an absent ideal the required support preimage is open by the pulled-back openness result. For a present ideal the hypersurface map preserves nonvanishing on components. It also transports the local equality away from memory and, by the all-opens hypothesis on the original hypersurface, the descended principalization certificate. Thus the new data satisfy the descent conditions and give the order certificate.
-/
private theorem comapOrderCertificate_of_smoothDivisor_cover {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → ∀ x : ↥(H z hz).subscheme,
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V₀ : (H z hz).subscheme.Opens, x ∈ V₀ ∧
          Jz.comap V₀.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V₀.ι)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz →
      IsPrincipalizationCertificateOnOpens (H z hz).subscheme ((H z hz).subschemeι ≫ ((U z hz).ι ≫ p)) Jz μ
        (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap] at h1
    exact h1
  refine OrderCertificate.descend (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _)
    (fun y hy => (H (f.base y) (hsup y hy)).comap (f ∣_ U (f.base y) (hsup y hy)))
    (fun y hy => isSmoothDivisor_comap_morphismRestrict hin f (U (f.base y) (hsup y hy))
      (H (f.base y) (hsup y hy)) (hH _ _))
    (fun y hy => support_comap_morphismRestrict_subset f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) N
      (hNsubH _ _))
    (fun y hy => support_comap_morphismRestrict_subset f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z
      (hZH _ _))
    (fun y hy => (J (f.base y) (hsup y hy)).map (fun Jz =>
      Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)))))
    ?_ ?_ ?_ ?_
  · intro y hy hnone
    have hJn : J (f.base y) (hsup y hy) = none := by
      cases hJ : J (f.base y) (hsup y hy) with
      | none => rfl
      | some Jz =>
          rw [hJ] at hnone
          simp at hnone
    exact isOpen_preimage_support_comap_morphismRestrict f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z
      (hJnone _ _ hJn)
  · intro y hy Jz' hsome
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact nonzeroOnComponents_comap_comapSubscheme hin f (U (f.base y) (hsup y hy))
          (H (f.base y) (hsup y hy)) Jz (hJcomp _ _ Jz hJ)
  · intro y hy Jz' hsome x hx
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact exists_isOpen_comap_eq_comap_morphismRestrict f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) N Mem Jz
          (hJloc _ _ Jz hJ) x hx
  · intro y hy Jz' hsome
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact principalizationCertificate_comapSubscheme_of_isOpenImmersion hin f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z μ Mem
          Jz (ih _ _ Jz hJ)

/- English proof (authored)
Induct simultaneously on principalization and order certificates, requiring each to restrict along every open immersion. The memory and large-marking cases follow by support containment and the same marking. The factorization case uses the pulled-back product and the induction hypothesis on its order certificate. The localization cases follow by taking inverse images of the chosen covering opens. The descent case follows by pulling back the smooth divisors, optional ideals and descended certificates using the open-immersion stability assumptions. These cases establish the required restriction property.
-/
private theorem comapPrincipalizationCertificate_of_principalizationCertificate {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z :=
  PrincipalizationCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => IsOrderCertificateOnOpens W p N μ Mem Z)
    (fun h => comapPrincipalizationCertificate_of_support_subset h)
    (fun hm => comapPrincipalizationCertificate_of_two_le hm)
    (fun M N μ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order M N μ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover U hU ih)
    (fun h => comapOrderCertificate_of_support_subset h)
    (fun hmu => comapOrderCertificate_of_two_le hmu)
    (fun U hU _ ih => comapOrderCertificate_of_open_cover U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

/- English proof (authored)
Apply simultaneous induction to the order and principalization certificates. The elementary constructors remain valid under pullback of supports, ideals and memory. For a principalization certificate built from an order certificate, pull back the factorization and use the induction hypothesis for that order certificate. For both localization cases take inverse images of the specified neighborhoods. For an order certificate built by descent, use the smooth-divisor restriction result and the induction hypotheses for the descended principalization certificates. This supplies the restriction for the given order certificate.
-/
private theorem comapOrderCertificate_of_orderCertificate {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    IsOrderCertificateOnOpens W p N μ Mem Z :=
  OrderCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => IsOrderCertificateOnOpens W p N μ Mem Z)
    (fun h => comapPrincipalizationCertificate_of_support_subset h)
    (fun hm => comapPrincipalizationCertificate_of_two_le hm)
    (fun M N μ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order M N μ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover U hU ih)
    (fun h => comapOrderCertificate_of_support_subset h)
    (fun hmu => comapOrderCertificate_of_two_le hmu)
    (fun U hU _ ih => comapOrderCertificate_of_open_cover U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

/- English proof (authored)
The simultaneous induction theorem gives a principalization certificate after restriction along every open immersion. Apply it to the specified immersion.
-/
theorem PrincipalizationCertificate.comap_of_openImmersionStability {k : Type u} [Field k]
    (hin : OpenImmersionStability k) {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (f.base ⁻¹' Mem) (Z.comap f) :=
  comapPrincipalizationCertificate_of_principalizationCertificate hin h V f inferInstance

/- English proof (authored)
The order certificate satisfies the restriction property along all open immersions by the simultaneous induction theorem. Apply it to the given one.
-/
theorem OrderCertificate.comap_of_isOpenImmersion {k : Type u} [Field k]
    (hin : OpenImmersionStability k) {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    OrderCertificate V (f ≫ p) (N.comap f) μ (f.base ⁻¹' Mem) (Z.comap f) :=
  comapOrderCertificate_of_orderCertificate hin h V f inferInstance

/- English proof (authored)
The inclusion of an open subscheme is an open immersion. Apply the restriction theorem to this inclusion.
-/
theorem OrderCertificate.restrict {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    (hin : OpenImmersionStability k) (U : W.Opens) :
    OrderCertificate U.toScheme (U.ι ≫ p) (N.comap U.ι) μ (U.ι.base ⁻¹' Mem) (Z.comap U.ι) :=
  h.comap_of_isOpenImmersion hin U.ι

end FunctorialResolution.EmbeddedResolution
