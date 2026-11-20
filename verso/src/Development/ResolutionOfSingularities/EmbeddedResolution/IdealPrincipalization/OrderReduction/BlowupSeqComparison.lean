import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Every image of the composite is an image under the second map. Conversely, a point in the domain of the second map has a preimage under the isomorphism, so its image also belongs to the range of the composite.
-/
private theorem range_iso_hom_comp {X Y Z : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ Z) :
    Set.range (e.hom ≫ g).base = Set.range g.base := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨e.hom.base x, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    show g.base (e.hom.base (e.inv.base y)) = g.base y
    rw [Scheme.inv_hom_apply]

/- English proof (authored)
The two pullbacks compose to pullback along the inverse followed by the isomorphism. That composite is the identity, which fixes the ideal.
-/
private theorem comap_hom_comap_inv {X Y : Scheme.{u}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

/- English proof (authored)
Inclusion of ideals reverses inclusion of supports. The support of the larger ideal is therefore contained in that of the smaller one.
-/
private theorem mem_support_of_le {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) (x : ↥X)
    (hx : x ∈ J.support) : x ∈ I.support :=
  Scheme.IdealSheafData.support_antitone h hx

/- English proof (authored)
The closed-subscheme inclusion has image equal to the ideal's support. Membership in that support thus supplies a point of the closed subscheme mapping to the given point.
-/
private theorem exists_subschemeι_base_eq {X : Scheme.{u}} (I : X.IdealSheafData) (x : ↥X)
    (hx : x ∈ I.support) : ∃ z, I.subschemeι.base z = x := by
  have hmem : x ∈ Set.range ⇑I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι I]
    exact hx
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

/- English proof (authored)
The range of the first projection from a scheme pullback is the inverse image of the range of the other input map. The given membership puts the point in that range, providing a preimage.
-/
private theorem exists_pullbackFst_base_eq {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : ↥X)
    (hx : f.base x ∈ Set.range g.base) : ∃ z, (Limits.pullback.fst f g).base z = x := by
  have h := Scheme.Pullback.range_fst f g
  rw [Set.ext_iff] at h
  exact (h x).mpr hx

/- English proof (authored)
Identify the given square with the canonical scheme pullback. The range of the first projection is unchanged by precomposing with this isomorphism. The hypothesis supplies a preimage under the canonical projection and therefore under the given projection.
-/
private theorem exists_preimage_of_isPullback {X' X S : Scheme.{u}} {g : X' ⟶ X} {s : S ⟶ X}
    {Q : Scheme.{u}} {p : Q ⟶ S} {q : Q ⟶ X'} (h : IsPullback p q s g) (x : ↥S)
    (hx : s.base x ∈ Set.range g.base) : ∃ y : ↥Q, p.base y = x := by
  have h1 : Set.range p.base = Set.range (Limits.pullback.fst s g).base := by
    rw [← h.isoPullback_hom_fst]
    exact range_iso_hom_comp h.isoPullback _
  obtain ⟨z, hz⟩ := exists_pullbackFst_base_eq s g x hx
  have hmem : x ∈ Set.range p.base := by
    rw [h1]
    exact ⟨z, hz⟩
  exact hmem

def BlowupLiftEqOnControlledTransform : Prop :=
  ∀ (X Y S T : Scheme.{u}) (π : Y ⟶ X) (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ f g : S ⟶ X, Z.comap f = Z.comap g →
      ∀ ρ : T ⟶ S, Blowup.IsBlowupAlongIdealSheaf ρ (Z.comap f) →
        ∀ f' g' : T ⟶ Y, f' ≫ π = ρ ≫ f → g' ≫ π = ρ ≫ g →
          ∀ a : S.IdealSheafData, a.subschemeι ≫ f = a.subschemeι ≫ g →
            ∀ c : T.IdealSheafData,
              Blowup.exceptionalIdeal ρ (Z.comap f) * c = a.comap ρ →
              c.subschemeι ≫ f' = c.subschemeι ≫ g'

variable {V P : Scheme.{u}}

structure BlowupSeqLevelIso (C : SequenceOfBlowups V) (B₁ B₂ : SequenceOfBlowups P) (L : ℕ)
    (σ₁ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₁.schemeAt i))
    (σ₂ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₂.schemeAt i))
    (a : ∀ i : ℕ, (C.schemeAt i).IdealSheafData) (i : ℕ) where
  iso : B₁.schemeAt i ≅ B₂.schemeAt i
  compat : ∀ hi : i ≤ L,
    (a i).subschemeι ≫ σ₁ i hi = (a i).subschemeι ≫ σ₂ i hi ≫ iso.inv

structure BlowupSeqComparison (f g : V ⟶ P) (C : SequenceOfBlowups V) (B₁ B₂ : SequenceOfBlowups P) (L : ℕ)
    (σ₁ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₁.schemeAt i))
    (σ₂ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₂.schemeAt i))
    (a : ∀ i : ℕ, (C.schemeAt i).IdealSheafData) : Prop where
  zero_ideal :
    (a 0).subschemeι ≫ C.isoZero.hom ≫ f = (a 0).subschemeι ≫ C.isoZero.hom ≫ g
  isBlowup_B₁ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (B₁.transitionMapSucc i) (B₁.center i)
  isBlowup_B₂ : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (B₂.transitionMapSucc i) (B₂.center i)
  isBlowup_C : ∀ i : ℕ, i < L → Blowup.IsBlowupAlongIdealSheaf (C.transitionMapSucc i) (C.center i)
  ideal_succ : ∀ i : ℕ, i < L →
    Blowup.exceptionalIdeal (C.transitionMapSucc i) (C.center i) * a (i + 1) = (a i).comap (C.transitionMapSucc i)
  ideal_le_center : ∀ i : ℕ, i < L → a i ≤ C.center i
  center_C₁ : ∀ i : ℕ, ∀ hi : i < L, C.center i = (B₁.center i).comap (σ₁ i hi.le)
  center_C₂ : ∀ i : ℕ, ∀ hi : i < L, C.center i = (B₂.center i).comap (σ₂ i hi.le)
  cover₁ : ∀ i : ℕ, i < L → ∀ x ∈ (B₁.center i).support,
    (B₁.projectionToBase i).base x ∈ Set.range f.base
  cover₂ : ∀ i : ℕ, i < L → ∀ x ∈ (B₂.center i).support,
    (B₂.projectionToBase i).base x ∈ Set.range g.base
  lifting : BlowupLiftEqOnControlledTransform.{u}
  determined₁ : ∀ i : ℕ, i < L → ∀ J : (B₁.schemeAt i).IdealSheafData,
    (B₁.center i).support ≤ J.support → J ≤ B₁.center i
  determined₂ : ∀ i : ℕ, i < L → ∀ J : (B₂.schemeAt i).IdealSheafData,
    (B₂.center i).support ≤ J.support → J ≤ B₂.center i
  pullback₁ : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (σ₁ (i + 1) hi) (C.transitionMapSucc i) (B₁.transitionMapSucc i) (σ₁ i hi.le)
  pullback₂ : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (σ₂ (i + 1) hi) (C.transitionMapSucc i) (B₂.transitionMapSucc i) (σ₂ i hi.le)
  zero₁ : σ₁ 0 (Nat.zero_le _) ≫ B₁.isoZero.hom = C.isoZero.hom ≫ f
  zero₂ : σ₂ 0 (Nat.zero_le _) ≫ B₂.isoZero.hom = C.isoZero.hom ≫ g

variable {f g : V ⟶ P} {C : SequenceOfBlowups V} {B₁ B₂ : SequenceOfBlowups P} {L : ℕ}
  {σ₁ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₁.schemeAt i)}
  {σ₂ : ∀ i : ℕ, i ≤ L → (C.schemeAt i ⟶ B₂.schemeAt i)}
  {a : ∀ i : ℕ, (C.schemeAt i).IdealSheafData}

/- English proof (authored)
The left stage comparison and the projections form a pullback square over the left base map. The coverage condition puts the chosen center point's projection in that base map's range. The point therefore has a preimage in the common sequence's stage.
-/
theorem BlowupSeqComparison.exists_preimage_of_mem_center_support_left (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    (i : ℕ) (hi : i < L) (x : ↥(B₁.schemeAt i)) (hx : x ∈ (B₁.center i).support) :
    ∃ y : ↥(C.schemeAt i), (σ₁ i hi.le).base y = x := by
  have hsq : IsPullback (σ₁ i hi.le) (C.projectionToBase i) (B₁.projectionToBase i) f :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism f C B₁ L σ₁ hd.zero₁ hd.pullback₁ i hi.le
  exact exists_preimage_of_isPullback hsq x (hd.cover₁ i hi x hx)

/- English proof (authored)
The right stage comparison is the projection of a pullback square over the right base map. By the right coverage condition the center point projects to the range of that map. The pullback projection then provides a preimage in the common stage.
-/
theorem BlowupSeqComparison.exists_preimage_of_mem_center_support_right (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    (i : ℕ) (hi : i < L) (x : ↥(B₂.schemeAt i)) (hx : x ∈ (B₂.center i).support) :
    ∃ y : ↥(C.schemeAt i), (σ₂ i hi.le).base y = x := by
  have hsq : IsPullback (σ₂ i hi.le) (C.projectionToBase i) (B₂.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g C B₂ L σ₂ hd.zero₂ hd.pullback₂ i hi.le
  exact exists_preimage_of_isPullback hsq x (hd.cover₂ i hi x hx)

/- English proof (authored)
Compose both sides with the left initial isomorphism. The stage-zero comparison identities express the composites as the common initial identification followed by the left and right base maps respectively. They agree on the closed subscheme by the initial ideal hypothesis. Cancel the left initial isomorphism.
-/
theorem subschemeι_comp_zero_eq_comp_isoObjZero_inv (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    ∀ hi : (0 : ℕ) ≤ L,
      (a 0).subschemeι ≫ σ₁ 0 hi =
        (a 0).subschemeι ≫ σ₂ 0 hi ≫ (B₁.isoZero ≪≫ B₂.isoZero.symm).inv := by
  intro hi
  have h1 : σ₁ 0 hi ≫ B₁.isoZero.hom = C.isoZero.hom ≫ f := hd.zero₁
  have h2 : σ₂ 0 hi ≫ B₂.isoZero.hom = C.isoZero.hom ≫ g := hd.zero₂
  rw [← cancel_mono B₁.isoZero.hom]
  simp only [Category.assoc, Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id, Category.comp_id]
  rw [h1, h2]
  exact hd.zero_ideal

def blowupSeqLevelIsoZero (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a 0 where
  iso := B₁.isoZero ≪≫ B₂.isoZero.symm
  compat := subschemeι_comp_zero_eq_comp_isoObjZero_inv hd

/- English proof (authored)
The initial stage isomorphism is the left initial identification followed by the inverse right identification. Following it by the right identification cancels the inverse and leaves the left identification.
-/
theorem blowupSeqLevelIsoZero_iso_hom_comp_isoObjZero (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    (blowupSeqLevelIsoZero hd).iso.hom ≫ B₂.isoZero.hom = B₁.isoZero.hom := by
  show (B₁.isoZero ≪≫ B₂.isoZero.symm).hom ≫ B₂.isoZero.hom = B₁.isoZero.hom
  simp

/- English proof (authored)
On the common center support the two stage comparisons agree after applying the inverse stage isomorphism. Indeed, the auxiliary ideal is contained in the center ideal, so each point of the center support comes from its closed subscheme, where agreement is assumed. Now lift a point of the left center support to the common stage using coverage. Its lift lies on the common center because centers pull back, and its right image lies on the right center. Agreement of the two comparisons sends the original left point into the right support under the stage isomorphism. The symmetric lifting argument gives the reverse inclusion after transport. Each center is determined by its support in the stated sense, so these inclusions give opposite ideal inclusions after transport by the inverse isomorphisms. Hence the two center ideals agree.
-/
theorem BlowupSeqLevelIso.center_comap_iso_hom_eq (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    (B₂.center i).comap st.iso.hom = B₁.center i := by
  have hkey : ∀ y : ↥(C.schemeAt i), y ∈ (C.center i).support →
      (σ₁ i hi.le).base y = st.iso.inv.base ((σ₂ i hi.le).base y) := by
    intro y hy
    have hy2 : y ∈ (a i).support := mem_support_of_le (hd.ideal_le_center i hi) y hy
    obtain ⟨z, hz⟩ := exists_subschemeι_base_eq (a i) y hy2
    have e1 : ((a i).subschemeι ≫ σ₁ i hi.le).base z
        = ((a i).subschemeι ≫ σ₂ i hi.le ≫ st.iso.inv).base z := by
      rw [st.compat hi.le]
    have e2 : (σ₁ i hi.le).base ((a i).subschemeι.base z)
        = st.iso.inv.base ((σ₂ i hi.le).base ((a i).subschemeι.base z)) := e1
    rw [hz] at e2
    exact e2
  have h1 : (B₁.center i).support ≤ ((B₂.center i).comap st.iso.hom).support := by
    intro x hx
    obtain ⟨y, hy⟩ := hd.exists_preimage_of_mem_center_support_left i hi x hx
    have hyc : y ∈ (C.center i).support := by
      rw [hd.center_C₁ i hi, Scheme.IdealSheafData.mem_support_comap, hy]
      exact hx
    have hy2 : (σ₂ i hi.le).base y ∈ (B₂.center i).support := by
      have := hyc
      rw [hd.center_C₂ i hi, Scheme.IdealSheafData.mem_support_comap] at this
      exact this
    rw [Scheme.IdealSheafData.mem_support_comap]
    have hx' : x = st.iso.inv.base ((σ₂ i hi.le).base y) := by
      rw [← hy]
      exact hkey y hyc
    rw [hx', Scheme.inv_hom_apply]
    exact hy2
  have h2 : (B₂.center i).support ≤ ((B₁.center i).comap st.iso.inv).support := by
    intro x hx
    obtain ⟨y, hy⟩ := hd.exists_preimage_of_mem_center_support_right i hi x hx
    have hyc : y ∈ (C.center i).support := by
      rw [hd.center_C₂ i hi, Scheme.IdealSheafData.mem_support_comap, hy]
      exact hx
    have hy1 : (σ₁ i hi.le).base y ∈ (B₁.center i).support := by
      have := hyc
      rw [hd.center_C₁ i hi, Scheme.IdealSheafData.mem_support_comap] at this
      exact this
    rw [Scheme.IdealSheafData.mem_support_comap, ← hy, ← hkey y hyc]
    exact hy1
  have hle1 : (B₂.center i).comap st.iso.hom ≤ B₁.center i :=
    hd.determined₁ i hi _ h1
  have hle2 : (B₁.center i).comap st.iso.inv ≤ B₂.center i :=
    hd.determined₂ i hi _ h2
  have hle3 : B₁.center i ≤ (B₂.center i).comap st.iso.hom := by
    have hmono : ((B₁.center i).comap st.iso.inv).comap st.iso.hom
        ≤ (B₂.center i).comap st.iso.hom :=
      Scheme.IdealSheafData.comap_mono st.iso.hom hle2
    rwa [← Scheme.IdealSheafData.comap_comp, st.iso.hom_inv_id,
      Scheme.IdealSheafData.comap_id] at hmono
  exact le_antisymm hle1 hle3

/- English proof (authored)
Transport the right blowup along the inverse stage isomorphism to the left stage. The center comparison says its transported center is the left center. Both successors are therefore blowups of the same ideal on the left stage. The universal property gives an isomorphism over that stage.
-/
theorem BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    ∃ e : B₁.schemeAt (i + 1) ≅ B₂.schemeAt (i + 1),
      e.hom ≫ B₂.transitionMapSucc i ≫ st.iso.inv = B₁.transitionMapSucc i := by
  have h2 : Blowup.IsBlowupAlongIdealSheaf (B₂.transitionMapSucc i ≫ st.iso.symm.hom)
      ((B₂.center i).comap st.iso.symm.inv) :=
    (hd.isBlowup_B₂ i hi).comp_iso_hom st.iso.symm
  rw [Iso.symm_hom, Iso.symm_inv, BlowupSeqLevelIso.center_comap_iso_hom_eq hd hi st] at h2
  exact (hd.isBlowup_B₁ i hi).exists_iso h2

/- English proof (authored)
Postcompose the given identity with the forward stage isomorphism. It cancels the inverse on one side, producing the desired square.
-/
theorem BlowupSeqLevelIso.hom_comp_blowupMorphism_eq_comp_iso_hom {i : ℕ} (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i)
    (e : B₁.schemeAt (i + 1) ≅ B₂.schemeAt (i + 1))
    (he : e.hom ≫ B₂.transitionMapSucc i ≫ st.iso.inv = B₁.transitionMapSucc i) :
    e.hom ≫ B₂.transitionMapSucc i = B₁.transitionMapSucc i ≫ st.iso.hom := by
  rw [← he]
  simp

def BlowupSeqLevelIso.isoSucc (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    B₁.schemeAt (i + 1) ≅ B₂.schemeAt (i + 1) :=
  (BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism hd hi st).choose

/- English proof (authored)
The chosen successor isomorphism is a witness from the blowup uniqueness result. Its compatibility with the two blowup maps is part of that witness.
-/
theorem BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    (BlowupSeqLevelIso.isoSucc hd hi st).hom ≫ B₂.transitionMapSucc i ≫ st.iso.inv = B₁.transitionMapSucc i :=
  (BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism hd hi st).choose_spec

/- English proof (authored)
Use the current stage isomorphism to view both comparison maps into the left stage. Their center pullbacks are equal because both give the common center. They agree on the closed subscheme of the current auxiliary ideal by the stage hypothesis. The successor comparison maps, with the right one transported by the inverse successor isomorphism, lift these maps through the left blowup by commutativity of the comparison squares. The auxiliary ideal at the next stage is obtained by removing one exceptional factor from the total transform. The controlled-transform comparison for blowup lifts therefore gives agreement on its closed subscheme.
-/
theorem BlowupSeqLevelIso.subschemeι_comp_eq_comp_isoSucc_inv (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    ∀ hj : i + 1 ≤ L,
      (a (i + 1)).subschemeι ≫ σ₁ (i + 1) hj =
        (a (i + 1)).subschemeι ≫ σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv := by
  intro hj
  have hcen1 : C.center i = (B₁.center i).comap (σ₁ i hi.le) := hd.center_C₁ i hi
  have hinv : (B₁.center i).comap st.iso.inv = B₂.center i := by
    rw [← BlowupSeqLevelIso.center_comap_iso_hom_eq hd hi st, comap_hom_comap_inv]
  have hcen2 : (B₁.center i).comap (σ₂ i hi.le ≫ st.iso.inv) = C.center i := by
    rw [Scheme.IdealSheafData.comap_comp, hinv, ← hd.center_C₂ i hi]
  have hZeq : (B₁.center i).comap (σ₁ i hi.le)
      = (B₁.center i).comap (σ₂ i hi.le ≫ st.iso.inv) := by
    rw [← hcen1, hcen2]
  have hρ : Blowup.IsBlowupAlongIdealSheaf (C.transitionMapSucc i) ((B₁.center i).comap (σ₁ i hi.le)) := by
    rw [← hcen1]
    exact hd.isBlowup_C i hi
  have hf' : σ₁ (i + 1) hj ≫ B₁.transitionMapSucc i = C.transitionMapSucc i ≫ σ₁ i hi.le :=
    (hd.pullback₁ i hi).w
  have hspec := BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism hd hi st
  have hw2 : σ₂ (i + 1) hj ≫ B₂.transitionMapSucc i = C.transitionMapSucc i ≫ σ₂ i hi.le :=
    (hd.pullback₂ i hi).w
  have hg' : (σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv) ≫ B₁.transitionMapSucc i
      = C.transitionMapSucc i ≫ σ₂ i hi.le ≫ st.iso.inv := by
    calc (σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv) ≫ B₁.transitionMapSucc i
        = σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv ≫ B₁.transitionMapSucc i := by
          rw [Category.assoc]
      _ = σ₂ (i + 1) hj ≫ B₂.transitionMapSucc i ≫ st.iso.inv := by
          rw [← hspec]
          simp
      _ = (σ₂ (i + 1) hj ≫ B₂.transitionMapSucc i) ≫ st.iso.inv := by rw [Category.assoc]
      _ = C.transitionMapSucc i ≫ σ₂ i hi.le ≫ st.iso.inv := by rw [hw2, Category.assoc]
  have hc : Blowup.exceptionalIdeal (C.transitionMapSucc i) ((B₁.center i).comap (σ₁ i hi.le)) * a (i + 1)
      = (a i).comap (C.transitionMapSucc i) := by
    rw [← hcen1]
    exact hd.ideal_succ i hi
  exact hd.lifting (B₁.schemeAt i) (B₁.schemeAt (i + 1)) (C.schemeAt i) (C.schemeAt (i + 1)) (B₁.transitionMapSucc i)
    (B₁.center i) (hd.isBlowup_B₁ i hi) (σ₁ i hi.le) (σ₂ i hi.le ≫ st.iso.inv) hZeq
    (C.transitionMapSucc i) hρ (σ₁ (i + 1) hj)
    (σ₂ (i + 1) hj ≫ (BlowupSeqLevelIso.isoSucc hd hi st).inv) hf' hg' (a i) (st.compat hi.le)
    (a (i + 1)) hc

def BlowupSeqLevelIso.succ (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a)
    {i : ℕ} (hi : i < L) (st : BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i) :
    BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a (i + 1) where
  iso := BlowupSeqLevelIso.isoSucc hd hi st
  compat := BlowupSeqLevelIso.subschemeι_comp_eq_comp_isoSucc_inv hd hi st

private def blowupSeqLevelIsoOfLE (hd : BlowupSeqComparison f g C B₁ B₂ L σ₁ σ₂ a) :
    ∀ i : ℕ, i ≤ L → BlowupSeqLevelIso C B₁ B₂ L σ₁ σ₂ a i
  | 0, _ => blowupSeqLevelIsoZero hd
  | (i + 1), h =>
      BlowupSeqLevelIso.succ hd (Nat.lt_of_succ_le h) (blowupSeqLevelIsoOfLE hd i (Nat.le_of_succ_le h))

/- English proof (authored)
The strict pullback relations give a common length and two stagewise comparisons with the same source. Together with coverage, determination of the centers by support, and the auxiliary ideal identities, they give the comparison data for constructing stage isomorphisms. At the initial stage use the two initial identifications. At each successor the current isomorphism identifies the centers, so the universal property identifies the two blowups. The lift comparison preserves agreement on the auxiliary subscheme at that successor, enabling the induction. The resulting stage isomorphisms commute with the initial and transition maps and identify all center ideals, which is the required sequence isomorphism.
-/
theorem SequenceOfBlowups.isomorphic_of_isStrictPullback_same_source (B B' : SequenceOfBlowups P)
    {φ ψ : V ⟶ P} {D : SequenceOfBlowups V}
    (hlift : BlowupLiftEqOnControlledTransform.{u})
    (h₁ : IsStrictPullbackBlowupSeq φ D B) (h₂ : IsStrictPullbackBlowupSeq ψ D B')
    (hcov₁ : ∀ i : ℕ, i < B.length → ∀ x ∈ (B.center i).support,
      (B.projectionToBase i).base x ∈ Set.range φ.base)
    (hcov₂ : ∀ i : ℕ, i < B'.length → ∀ x ∈ (B'.center i).support,
      (B'.projectionToBase i).base x ∈ Set.range ψ.base)
    (hdet₁ : ∀ i : ℕ, i < B.length → ∀ J : (B.schemeAt i).IdealSheafData,
      (B.center i).support ≤ J.support → J ≤ B.center i)
    (hdet₂ : ∀ i : ℕ, i < B'.length → ∀ J : (B'.schemeAt i).IdealSheafData,
      (B'.center i).support ≤ J.support → J ≤ B'.center i)
    (b : ∀ i : ℕ, (D.schemeAt i).IdealSheafData)
    (hzero : (b 0).subschemeι ≫ D.isoZero.hom ≫ φ = (b 0).subschemeι ≫ D.isoZero.hom ≫ ψ)
    (hsucc : ∀ i : ℕ, i < D.length →
      Blowup.exceptionalIdeal (D.transitionMapSucc i) (D.center i) * b (i + 1) = (b i).comap (D.transitionMapSucc i))
    (hle : ∀ i : ℕ, i < D.length → b i ≤ D.center i) :
    B.Isomorphic B' := by
  unfold IsStrictPullbackBlowupSeq at h₁ h₂
  obtain ⟨hlen1, s₁, hz1, hpb1, hc1⟩ := h₁
  obtain ⟨hlen2, s₂, hz2, hpb2, hc2⟩ := h₂
  have hd : BlowupSeqComparison φ ψ D B B' D.length s₁ s₂ b :=
    { zero_ideal := hzero
      isBlowup_B₁ := fun i hi => B.isBlowupAlongIdealSheaf_blowupMorphism i (by rw [← hlen1]; exact hi)
      isBlowup_B₂ := fun i hi => B'.isBlowupAlongIdealSheaf_blowupMorphism i (by rw [← hlen2]; exact hi)
      isBlowup_C := fun i hi => D.isBlowupAlongIdealSheaf_blowupMorphism i hi
      ideal_succ := hsucc
      ideal_le_center := hle
      center_C₁ := fun i hi => hc1 i hi
      center_C₂ := fun i hi => hc2 i hi
      cover₁ := fun i hi => hcov₁ i (by rw [← hlen1]; exact hi)
      cover₂ := fun i hi => hcov₂ i (by rw [← hlen2]; exact hi)
      lifting := hlift
      determined₁ := fun i hi => hdet₁ i (by rw [← hlen1]; exact hi)
      determined₂ := fun i hi => hdet₂ i (by rw [← hlen2]; exact hi)
      pullback₁ := hpb1
      pullback₂ := hpb2
      zero₁ := hz1
      zero₂ := hz2 }
  unfold SequenceOfBlowups.Isomorphic
  refine ⟨hlen1.symm.trans hlen2,
    fun i hi => (blowupSeqLevelIsoOfLE hd i (le_of_le_of_eq hi hlen1.symm)).iso, ?_, ?_, ?_⟩
  · exact blowupSeqLevelIsoZero_iso_hom_comp_isoObjZero hd
  · intro i hi
    have hiD : i < D.length := by rw [hlen1]; exact hi
    exact BlowupSeqLevelIso.hom_comp_blowupMorphism_eq_comp_iso_hom (blowupSeqLevelIsoOfLE hd i hiD.le)
      (BlowupSeqLevelIso.isoSucc hd hiD (blowupSeqLevelIsoOfLE hd i hiD.le))
      (BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism hd hiD (blowupSeqLevelIsoOfLE hd i hiD.le))
  · intro i hi
    have hiD : i < D.length := by rw [hlen1]; exact hi
    exact BlowupSeqLevelIso.center_comap_iso_hom_eq hd hiD (blowupSeqLevelIsoOfLE hd i hiD.le)

end FunctorialResolution.EmbeddedResolution

end
