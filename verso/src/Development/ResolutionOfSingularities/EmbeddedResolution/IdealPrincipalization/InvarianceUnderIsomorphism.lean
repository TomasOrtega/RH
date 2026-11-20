import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Restricting the ambient isomorphism to the inverse image of an open is the base change of that isomorphism to the open. Base changes of isomorphisms are isomorphisms.
-/
private theorem isIso_resLE_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    IsIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

def preimageOpensIso {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    Scheme.Opens.toScheme ((Opens.map e.hom.base).obj U) ≅ Scheme.Opens.toScheme U :=
  letI := isIso_resLE_of_iso e U
  asIso (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl)

@[simp]
/- English proof (authored)
The isomorphism of the inverse image open with the given open is constructed from the restricted ambient map, which is therefore its forward map.
-/
theorem preimageOpensIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpensIso e U).hom = e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl :=
  rfl

def OrderCertificateIsoInvariantOfMaxContact : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
      (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData)
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (_hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (_hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (_hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        ((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (_hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
      (_hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = Option.none →
        IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
          ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)))
      (_hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz → NonzeroOnComponents Jz)
      (_hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          ∀ x : ↥(H z hz).subscheme,
            ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
              ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
                Jz.comap V.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V.ι)
      (_hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
            (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
            ((Z.comap (U z hz).ι).comap (H z hz).subschemeι))
      (_hJtrans : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          ∀ (X : Scheme.{u}) (f : X ≅ (H z hz).subscheme),
            PrincipalizationCertificate X (f.hom ≫ (H z hz).subschemeι ≫ (U z hz).ι ≫ p) (Jz.comap f.hom) μ
              (⇑f.hom.base ⁻¹' (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem))
              (((Z.comap (U z hz).ι).comap (H z hz).subschemeι).comap f.hom))
      (W' : Scheme.{u}) (e : W' ≅ W),
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom)

/- English proof (authored)
A point belongs to the support of the pulled-back ideal exactly when its image belongs to the original support. This identifies the support with the inverse image.
-/
private theorem coe_support_comap_iso_hom {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Y.IdealSheafData) :
    ((Z.comap e.hom).support : Set ↥X) = ⇑e.hom.base ⁻¹' (Z.support : Set ↥Y) := by
  ext x
  simp

/- English proof (authored)
A point lies in the successive inverse images exactly when its image under the composite lies in the set.
-/
private theorem preimage_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (S : Set ↥C) :
    ⇑f.base ⁻¹' (⇑g.base ⁻¹' S) = ⇑(f ≫ g).base ⁻¹' S := by
  ext x
  simp

/- English proof (authored)
The isomorphism between the opens is the restriction of the ambient isomorphism. Composing it with the original open inclusion agrees with following the inverse image inclusion by the ambient map.
-/
private theorem preimageOpensIso_hom_comp_ι {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpensIso e U).hom ≫ U.ι = Scheme.Opens.ι ((Opens.map e.hom.base).obj U) ≫ e.hom := by
  rw [preimageOpensIso_hom, Scheme.Hom.resLE_comp_ι]

/- English proof (authored)
Postcompose the equality for the restricted isomorphism and open inclusions with the structural map. Associativity gives the stated identity.
-/
private theorem preimageOpensIso_hom_comp_ι_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (U : Y.Opens) :
    (preimageOpensIso e U).hom ≫ (U.ι ≫ q) =
      Scheme.Opens.ι ((Opens.map e.hom.base).obj U) ≫ (e.hom ≫ q) := by
  rw [← Category.assoc, preimageOpensIso_hom_comp_ι, Category.assoc]

/- English proof (authored)
Both iterated pullbacks are pullbacks along composites. The identity for the restricted isomorphism and its inclusions makes those composites equal, so the ideal sheaves agree.
-/
private theorem comap_preimageOpensIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) (I : Y.IdealSheafData) :
    (I.comap U.ι).comap (preimageOpensIso e U).hom =
      (I.comap e.hom).comap (Scheme.Opens.ι ((Opens.map e.hom.base).obj U)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, preimageOpensIso_hom_comp_ι]

/- English proof (authored)
Each nested inverse image is the inverse image along the corresponding composite into the original scheme. Those composites agree by compatibility of the open isomorphism with inclusion.
-/
private theorem preimage_preimageOpensIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) (Mem : Set ↥Y) :
    ⇑(preimageOpensIso e U).hom.base ⁻¹' (⇑U.ι.base ⁻¹' Mem) =
      ⇑(Scheme.Opens.ι ((Opens.map e.hom.base).obj U)).base ⁻¹' (⇑e.hom.base ⁻¹' Mem) := by
  rw [preimage_comp_base, preimage_comp_base, preimageOpensIso_hom_comp_ι]

/- English proof (authored)
Substitute the equal structure map, input ideal, memory set and target ideal. The given certificate is then a certificate for the specified data.
-/
private theorem principalizationCertificate_congr {k : Type u} [Field k] {W : Scheme.{u}}
    {p p' : W ⟶ Spec (CommRingCat.of k)} {I I' : W.IdealSheafData} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z Z' : W.IdealSheafData} (hp : p = p') (hI : I = I')
    (hMem : Mem = Mem') (hZ : Z = Z') (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p' I' m Mem' Z' := by
  subst hp hI hMem hZ
  exact h

/- English proof (authored)
Use the four equalities to identify the parameters of the two certificates. The original order certificate has the required parameters after substitution.
-/
private theorem orderCertificate_congr {k : Type u} [Field k] {W : Scheme.{u}}
    {p p' : W ⟶ Spec (CommRingCat.of k)} {N N' : W.IdealSheafData} {μ : ℕ}
    {Mem Mem' : Set ↥W} {Z Z' : W.IdealSheafData} (hp : p = p') (hN : N = N')
    (hMem : Mem = Mem') (hZ : Z = Z') (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W p' N' μ Mem' Z' := by
  subst hp hN hMem hZ
  exact h

/- English proof (authored)
The pulled-back target support is the inverse image of the original support. It lies in the inverse image of memory by the given containment, which yields a principalization certificate by the memory case.
-/
private theorem principalizationCertificate_comap_iso_of_support_subset {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (h : (Z.support : Set ↥W) ⊆ Mem) (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap_iso_hom e Z]
  exact Set.preimage_mono h

/- English proof (authored)
The isomorphism transport retains the marking. Since that marking is at least two, use the large-marking principalization constructor.
-/
private theorem principalizationCertificate_comap_iso_of_two_le {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hm : 2 ≤ m) (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  PrincipalizationCertificate.large hm

/- English proof (authored)
The ideal factorization persists under pullback. The support of the first factor is the inverse image of its old support and remains in the pulled-back memory. Order loci are preserved under the isomorphism, so the pulled-back target support satisfies the order bound for the second factor. Together with the same marking inequality and the transported order certificate from the hypothesis, these give the transported principalization certificate.
-/
private theorem principalizationCertificate_comap_iso_of_orderCertificate {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ) (_hcert : OrderCertificate W p N μ Mem Z)
    (ih : ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine PrincipalizationCertificate.toOrder (M.comap e.hom) (N.comap e.hom) μ ?_ ?_ hmu ?_ (ih W' e)
  · rw [hI, Scheme.IdealSheafData.comap_mul]
  · rw [coe_support_comap_iso_hom e M]
    exact Set.preimage_mono hM
  · rw [coe_support_comap_iso_hom e Z, orderAtLeastLocus_comap_iso_hom_eq_preimage e N μ]
    exact Set.preimage_mono hZ

/- English proof (authored)
For a point of the new support, its image lies in the original support. Take the inverse image of the chosen original neighborhood. The local hypothesis transports its principalization certificate along the restricted isomorphism. The open inclusion compatibility identifies the transported structure map, ideals and memory with the desired local data. These local certificates give the new global certificate by localization.
-/
private theorem principalizationCertificate_comap_iso_of_opens_cover {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (_hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
      PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι))
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (X : Scheme.{u}) (f : X ≅ (U z hz).toScheme),
      PrincipalizationCertificate X (f.hom ≫ ((U z hz).ι ≫ p)) ((I.comap (U z hz).ι).comap f.hom) m
        (⇑f.hom.base ⁻¹' (⇑(U z hz).ι.base ⁻¹' Mem)) ((Z.comap (U z hz).ι).comap f.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine PrincipalizationCertificate.localize
    (fun z' hz' =>
      (Opens.map e.hom.base).obj
        (U (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')))
    (fun z' hz' => ?_) ?_
  · exact hU (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')
  · intro z' hz'
    have hz : e.hom.base z' ∈ Z.support := by
      rwa [Scheme.IdealSheafData.mem_support_comap] at hz'
    exact principalizationCertificate_congr (preimageOpensIso_hom_comp_ι_comp p e (U (e.hom.base z') hz))
      (comap_preimageOpensIso_hom e (U (e.hom.base z') hz) I)
      (preimage_preimageOpensIso_hom e (U (e.hom.base z') hz) Mem)
      (comap_preimageOpensIso_hom e (U (e.hom.base z') hz) Z)
      (ih (e.hom.base z') hz _ (preimageOpensIso e (U (e.hom.base z') hz)))

/- English proof (authored)
Under the isomorphism the support becomes the inverse image of the original support. It remains inside the inverse image of memory, so the order certificate follows from the memory case.
-/
private theorem orderCertificate_comap_iso_of_support_subset {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (h : (Z.support : Set ↥W) ⊆ Mem) (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine OrderCertificate.memory ?_
  rw [coe_support_comap_iso_hom e Z]
  exact Set.preimage_mono h

/- English proof (authored)
The marking stays at least two under pullback. The large-marking constructor therefore supplies the transported order certificate.
-/
private theorem orderCertificate_comap_iso_of_two_le {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hmu : 2 ≤ μ) (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  OrderCertificate.large hmu

/- English proof (authored)
Every point of the new target support maps to one of the original support points. Use the inverse image of its specified open neighborhood. The local order certificate transports through the restriction of the ambient isomorphism. Its structure map, ideals and memory match those of the new open because the inclusions commute with the isomorphism. The localization constructor assembles the claim.
-/
private theorem orderCertificate_comap_iso_of_opens_cover {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (_hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
      OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι))
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (X : Scheme.{u}) (f : X ≅ (U z hz).toScheme),
      OrderCertificate X (f.hom ≫ ((U z hz).ι ≫ p)) ((N.comap (U z hz).ι).comap f.hom) μ
        (⇑f.hom.base ⁻¹' (⇑(U z hz).ι.base ⁻¹' Mem)) ((Z.comap (U z hz).ι).comap f.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  refine OrderCertificate.localize
    (fun z' hz' =>
      (Opens.map e.hom.base).obj
        (U (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')))
    (fun z' hz' => ?_) ?_
  · exact hU (e.hom.base z') (by rwa [Scheme.IdealSheafData.mem_support_comap] at hz')
  · intro z' hz'
    have hz : e.hom.base z' ∈ Z.support := by
      rwa [Scheme.IdealSheafData.mem_support_comap] at hz'
    exact orderCertificate_congr (preimageOpensIso_hom_comp_ι_comp p e (U (e.hom.base z') hz))
      (comap_preimageOpensIso_hom e (U (e.hom.base z') hz) N)
      (preimage_preimageOpensIso_hom e (U (e.hom.base z') hz) Mem)
      (comap_preimageOpensIso_hom e (U (e.hom.base z') hz) Z)
      (ih (e.hom.base z') hz _ (preimageOpensIso e (U (e.hom.base z') hz)))

/- English proof (authored)
The assumed invariance of the descent step applies to the given local smooth divisors, support conditions and auxiliary ideals. It takes the original descended principalization certificates together with their transported versions supplied by the hypothesis. Its conclusion is precisely the order certificate after the ambient isomorphism.
-/
private theorem orderCertificate_comap_iso_of_smoothDivisor_cover (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData)
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
        ((H z hz).support : Set ↥(U z hz).toScheme))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme) ⊆
        ((H z hz).support : Set ↥(U z hz).toScheme))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = Option.none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        ((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
            ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
              Jz.comap V.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V.ι)
    (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι))
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        ∀ (X : Scheme.{u}) (f : X ≅ (H z hz).subscheme),
          PrincipalizationCertificate X (f.hom ≫ (H z hz).subschemeι ≫ (U z hz).ι ≫ p) (Jz.comap f.hom) μ
            (⇑f.hom.base ⁻¹' (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem))
            (((Z.comap (U z hz).ι).comap (H z hz).subschemeι).comap f.hom))
    (W' : Scheme.{u}) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  hT k W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih W' e

/- English proof (authored)
Use simultaneous induction on principalization and order certificates, asking for transport along every isomorphism. Support containments, markings and products are preserved, which gives the memory, large-marking and factorization cases using the relevant induction hypotheses. Charts in the two localization cases transport by inverse image and the restricted isomorphism. The descent case follows from the assumed invariance for smooth divisors applied to the original principalization certificates on the hypersurfaces and their transported versions. These cases prove the required transport.
-/
private theorem principalizationCertificate_comap_iso (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  @PrincipalizationCertificate.rec k _
    (fun W p I m Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun W p N μ Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun {W p I m Mem Z} h => principalizationCertificate_comap_iso_of_support_subset W p I m Mem Z h)
    (fun {W p I m Mem Z} hm => principalizationCertificate_comap_iso_of_two_le W p I m Mem Z hm)
    (fun {W p I m Mem Z} M N μ hI hM hmu hZ hcert ihc =>
      principalizationCertificate_comap_iso_of_orderCertificate W p I m Mem Z M N μ hI hM hmu hZ hcert ihc)
    (fun {W p I m Mem Z} U hU hcert ihc =>
      principalizationCertificate_comap_iso_of_opens_cover W p I m Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} h => orderCertificate_comap_iso_of_support_subset W p N μ Mem Z h)
    (fun {W p N μ Mem Z} hmu => orderCertificate_comap_iso_of_two_le W p N μ Mem Z hmu)
    (fun {W p N μ Mem Z} U hU hcert ihc =>
      orderCertificate_comap_iso_of_opens_cover W p N μ Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ihc =>
      orderCertificate_comap_iso_of_smoothDivisor_cover hT W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc
        hJcert ihc)
    W p I m Mem Z h

/- English proof (authored)
Induct simultaneously on order and principalization certificates with the assertion that each transports under every isomorphism. The memory and marking cases use the underlying pulled-back support and the same marking. The principalization factorization case transmits the factorization and the smaller order certificate. The localization cases transport through isomorphic opens. For a descent step, the assumed invariance applies using the transported principalization certificates supplied by induction. This proves transport for the order certificate.
-/
private theorem orderCertificate_comap_iso (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (Z : W.IdealSheafData) (h : OrderCertificate W p N μ Mem Z) :
    ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  @OrderCertificate.rec k _
    (fun W p I m Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun W p N μ Mem Z _ => ∀ (W' : Scheme.{u}) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom))
    (fun {W p I m Mem Z} h => principalizationCertificate_comap_iso_of_support_subset W p I m Mem Z h)
    (fun {W p I m Mem Z} hm => principalizationCertificate_comap_iso_of_two_le W p I m Mem Z hm)
    (fun {W p I m Mem Z} M N μ hI hM hmu hZ hcert ihc =>
      principalizationCertificate_comap_iso_of_orderCertificate W p I m Mem Z M N μ hI hM hmu hZ hcert ihc)
    (fun {W p I m Mem Z} U hU hcert ihc =>
      principalizationCertificate_comap_iso_of_opens_cover W p I m Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} h => orderCertificate_comap_iso_of_support_subset W p N μ Mem Z h)
    (fun {W p N μ Mem Z} hmu => orderCertificate_comap_iso_of_two_le W p N μ Mem Z hmu)
    (fun {W p N μ Mem Z} U hU hcert ihc =>
      orderCertificate_comap_iso_of_opens_cover W p N μ Mem Z U hU hcert ihc)
    (fun {W p N μ Mem Z} U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ihc =>
      orderCertificate_comap_iso_of_smoothDivisor_cover hT W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc
        hJcert ihc)
    W p N μ Mem Z h

/- English proof (authored)
The simultaneous transport theorem applies to the given principalization certificate. Evaluate it at the specified scheme and isomorphism.
-/
theorem PrincipalizationCertificate.comap_iso (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    {W W' : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' (e.hom ≫ p) (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  principalizationCertificate_comap_iso hT W p I m Mem Z h W' e

/- English proof (authored)
The simultaneous induction proves transport of the order certificate along any isomorphism under the stated descent assumption. Apply it to this isomorphism.
-/
theorem OrderCertificate.comap_iso (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    {W W' : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' (e.hom ≫ p) (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) :=
  orderCertificate_comap_iso hT W p N μ Mem Z h W' e

/- English proof (authored)
Pull the certificate back along the isomorphism by the transport theorem. The equality of structure maps lets that certificate be viewed over the stated new structural map.
-/
theorem PrincipalizationCertificate.comap_iso_of_eq (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    {W W' : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {p' : W' ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (hp : p' = e.hom ≫ p)
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' p' (I.comap e.hom) m (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  subst hp
  exact PrincipalizationCertificate.comap_iso hT e h

/- English proof (authored)
Use the order certificate transport theorem for the isomorphism, then identify its composite structural map with the new one by the given equality.
-/
theorem OrderCertificate.comap_iso_of_eq (hT : OrderCertificateIsoInvariantOfMaxContact.{u}) {k : Type u} [Field k]
    {W W' : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
    {p' : W' ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (e : W' ≅ W) (hp : p' = e.hom ≫ p)
    (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W' p' (N.comap e.hom) μ (⇑e.hom.base ⁻¹' Mem) (Z.comap e.hom) := by
  subst hp
  exact OrderCertificate.comap_iso hT e h

end FunctorialResolution.EmbeddedResolution

end
