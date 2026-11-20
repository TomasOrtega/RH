import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderPullbackInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SmoothBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev baseChangeProj (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    (T.baseChange L f).scheme ⟶ T.scheme :=
  pullback.fst T.structMap (specMapOfFieldHom T.base L f)

abbrev baseChangeStructMap (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    (T.baseChange L f).scheme ⟶ Spec (CommRingCat.of L) :=
  pullback.snd T.structMap (specMapOfFieldHom T.base L f)

/- English proof (authored)
The two successive pullbacks equal pullback along the forward map followed by the inverse map. This composite is the identity on the original scheme, so the ideal is unchanged.
-/
private theorem comap_hom_comap_inv_eq_self {A B : Scheme.{u}} (e : A ≅ B) (D : A.IdealSheafData) :
    (D.comap e.inv).comap e.hom = D := by
  rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id]
  simp

/- English proof (authored)
The given splitting witnesses existence, so the definition selects some pair that also satisfies the splitting condition. By uniqueness, its second entry is N. That entry is the defined nonmonomial part.
-/
private theorem nonMonomialPart_eq_of_isMonomialSplitting_unique {X : Scheme.{u}} {E : List X.IdealSheafData}
    {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N)
    (hu : ∀ M' N' : X.IdealSheafData, IsMonomialSplitting E I M' N' → M = M' ∧ N = N') :
    nonMonomialPart E I = N := by
  have hex : ∃ q : X.IdealSheafData × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2 :=
    ⟨(M, N), hs⟩
  have hch : IsMonomialSplitting E I hex.choose.1 hex.choose.2 := hex.choose_spec
  have hNN := (hu _ _ hch).2
  unfold nonMonomialPart monomialSplitting
  rw [dif_pos hex]
  exact hNN.symm

/- English proof (authored)
The scheme and field are fixed. Substituting the equalities of the structure maps, ideals, markings, and boundaries makes the two marked objects equal.
-/
private theorem markedIdealWithBoundary_mk_congr {k : Type u} [Field k] {A : Scheme.{u}}
    {p q : A ⟶ Spec (CommRingCat.of k)} {I J : A.IdealSheafData} {m n : ℕ}
    {E F : List A.IdealSheafData} (hp : p = q) (hI : I = J) (hm : m = n) (hE : E = F) :
    MarkedIdealWithBoundary.mk k A p I m E = MarkedIdealWithBoundary.mk k A q J n F := by
  subst hp; subst hI; subst hm; subst hE; rfl

/- English proof (authored)
First substitute the equality of the marked objects so that the two maps have the same domain. The given equality of those maps then has a common type. Substituting it makes the pullback statement exactly the hypothesis.
-/
private theorem isPullbackBlowupSequence_of_eq_of_heq (F : PrincipalizationAssignment.{u}) (B : MarkedIdealWithBoundary.{u})
    {W U : MarkedIdealWithBoundary.{u}} (h : W = U) (g : W.scheme ⟶ B.scheme) (g' : U.scheme ⟶ B.scheme)
    (hg : HEq g g')
    (hh : IsPullbackBlowupSequence g (F W).toSequenceOfBlowups (F B).toSequenceOfBlowups) :
    IsPullbackBlowupSequence g' (F U).toSequenceOfBlowups (F B).toSequenceOfBlowups := by
  subst h
  have hgg := eq_of_heq hg
  subst hgg
  exact hh

/- English proof (authored)
The scheme isomorphism induces a homeomorphism of the underlying spaces. Topological Krull dimension is invariant under homeomorphism, and applying the same successor and natural-number conversion gives equality of the stated dimensions.
-/
theorem krullDimSucc_eq_of_iso {A B : Scheme.{u}} (e : A ≅ B) : krullDimSucc A = krullDimSucc B := by
  have hh := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  congr 1
  exact hh.topologicalKrullDim_eq

/- English proof (authored)
An isomorphism preserves smoothness and quasi-compactness of the structure map and gives local finite type for the transported map. It also carries irreducible components and the strict normal crossing configuration to their counterparts, preserving nonvanishing and the crossing condition. The field and positive marking are unchanged. These are all the admissibility requirements.
-/
theorem isAdmissible_comap_of_iso {k : Type u} [Field k] {A B : Scheme.{u}} (e : A ≅ B)
    (s : B ⟶ Spec (CommRingCat.of k)) (J : B.IdealSheafData) (m : ℕ)
    (E : List B.IdealSheafData)
    (h : (MarkedIdealWithBoundary.mk k B s J m E).IsAdmissible) :
    (MarkedIdealWithBoundary.mk k A (e.hom ≫ s) (J.comap e.hom) m
      (E.map (fun D : B.IdealSheafData => D.comap e.hom))).IsAdmissible := by
  have hsm : AlgebraicGeometry.Smooth s := h.smooth
  have hqc : AlgebraicGeometry.QuasiCompact s := h.quasiCompact
  exact
    { charZero := h.charZero
      locallyOfFiniteType := inferInstance
      nonzeroOnComponents := nonzeroOnComponents_comap_iso_hom e J h.nonzeroOnComponents
      one_le_mult := h.one_le_mult
      quasiCompact := inferInstance
      smooth := inferInstance
      snc := inStrictNormalCrossingPosition_comap_iso s e E h.snc }

/- English proof (authored)
Given a test pullback square for the vertical map, paste it with the marked pullback square. Its composite lower map respects the structure map by commutativity of the two structure triangles. Use the original marking on the test lower scheme, keeping its geometric and ideal data and taking positivity from the admissibility of T. The original order invariance then applies to the pasted square and gives the needed equality for its left projection.
-/
theorem orderAtPullbackInvariant_verticalMap {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {Y : Scheme.{u}} {g : Y ⟶ T.scheme} (hg : OrderAtPullbackInvariant T g)
    (S : MarkedPullbackSquare T g) :
    OrderAtPullbackInvariant S.lowerTriple S.left := by
  intro B b pB IB EB hvalid hbp Q a b' hpb A y
  refine hg B (b ≫ S.bottom) pB IB EB ?_ ?_ Q a (b' ≫ S.top) ?_ A y
  · exact
      { charZero := hvalid.charZero
        locallyOfFiniteType := hvalid.locallyOfFiniteType
        nonzeroOnComponents := hvalid.nonzeroOnComponents
        one_le_mult := hT.one_le_mult
        quasiCompact := hvalid.quasiCompact
        smooth := hvalid.smooth
        snc := hvalid.snc }
  · rw [Category.assoc, S.bottom_structMap]
    exact hbp
  · exact hpb.paste_vert S.isPullback

/- English proof (authored)
The vertical map in each marked pullback square is flat. Choose a monomial splitting of the lower ideal using admissibility. Its pullback is a splitting for the pulled back boundary, and equivalence of boundaries makes it a splitting for the designated upper boundary. Uniqueness on each admissible object identifies the chosen nonmonomial parts with these lower and upper factors. The upper factor is the pullback of the lower factor.
-/
theorem nonMonomialPartBaseChange_of_flat (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g] (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) :
    NonMonomialPartBaseChange T g k' q := by
  intro S E hE hV
  have : AlgebraicGeometry.Flat S.left := S.flat_verticalMap
  obtain ⟨M, N, hMN⟩ := hG.splitting_exists S.lowerTriple S.valid
  have hu1 : ∀ M' N' : S.baseScheme.IdealSheafData,
      IsMonomialSplitting S.boundary S.ideal M' N' → M = M' ∧ N = N' :=
    fun M' N' h' => hG.splitting_unique S.lowerTriple S.valid M N M' N' hMN h'
  have h1 := isMonomialSplitting_comap_of_flat S.left hMN
  have hMNcomap : IsMonomialSplitting E (S.ideal.comap S.left) (M.comap S.left)
      (N.comap S.left) := (isMonomialSplitting_congr hE _ _ _).1 h1
  have hu2 : ∀ M' N' : S.topScheme.IdealSheafData,
      IsMonomialSplitting E (S.ideal.comap S.left) M' N' →
        M.comap S.left = M' ∧ N.comap S.left = N' :=
    fun M' N' h' => hG.splitting_unique (S.upperTriple k' q E) hV (M.comap S.left)
      (N.comap S.left) M' N' hMNcomap h'
  rw [nonMonomialPart_eq_of_isMonomialSplitting_unique hMNcomap hu2, nonMonomialPart_eq_of_isMonomialSplitting_unique hMN hu1]

/- English proof (authored)
In the marked pullback square the vertical map is flat, and the test-square order invariance for the original map passes to that vertical map by pasting. Use the flat pullback theorem for monomial principalization with this order invariance, the two locally monomial objects, and the equivalence between the pulled back boundary and the upper boundary. It gives the required comparison of their sequences.
-/
theorem monomialPrincipalizationBaseChange_of_flat (hG : PrincipalizationGeometryHypotheses.{u}) (τ : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    [AlgebraicGeometry.Flat g] (hg : OrderAtPullbackInvariant T g) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) :
    MonomialPrincipalizationBaseChange τ T g k' q := by
  intro S hsmooth E hE hSm'
  have : AlgebraicGeometry.Flat S.left := S.flat_verticalMap
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hG.monomialInputs τ S.lowerTriple S.topScheme k'
    (S.top ≫ q) S.left E hsmooth hE.symm hSm'
    (fun B b pB hbp IB EB hv Q a b' hpb A z =>
      orderAtPullbackInvariant_verticalMap hT hg S B b pB IB EB hv hbp Q a b' hpb A z)

namespace MarkedPullbackSquare

/- English proof (authored)
Paste the marked square with the defining pullback square for the extension of the ground field. The lower composite is the lower object's structure map by its compatibility with the original structure map. The pasted square is therefore the claimed field-extension pullback.
-/
theorem isPullback_comp_baseChangeStructMap {T : MarkedIdealWithBoundary.{u}} {L : Type u} [Field L]
    {f : T.base →+* L} (S : MarkedPullbackSquare T (baseChangeProj T L f)) :
    IsPullback S.left (S.top ≫ baseChangeStructMap T L f) S.structMap (specMapOfFieldHom T.base L f) := by
  have h := S.isPullback.paste_vert
    (IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f))
  rw [S.bottom_structMap] at h
  exact h

end MarkedPullbackSquare

/- English proof (authored)
The pasted square identifies the upper scheme with the direct extension of the lower scheme to the new field. Its canonical isomorphism commutes with both projections. Transport the chosen upper boundary along the inverse isomorphism. This boundary is equivalent to the direct field-change boundary because pullbacks compose and remove unit ideals in the same way. Admissibility and the dimension bound persist under transport, and the order bound follows from order invariance under field extension and along the isomorphism. The lower dimension bound follows from the marked square.

Apply the field-change property of the assignment on the direct field extension. The isomorphism from the upper scheme is smooth and surjective, so the strict smooth pullback property compares its assigned sequence to the sequence on the direct field extension. Pullbacks in the two directions of the isomorphism cancel on the boundary, and the ideal and structure-map identities identify the transported object with the given upper one. Composing the two sequence comparisons and identifying the composite projection with the original vertical map gives the desired pullback.
-/
theorem commutesWithBaseChange_baseChangeProj_of_isOrderReduction (hG : PrincipalizationGeometryHypotheses.{u}) (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (L : Type u) [Field L] [CharZero L]
    (f : T.base →+* L) :
    PrincipalizationBaseChange F n T (baseChangeProj T L f) L (baseChangeStructMap T L f) := by
  intro S hord E hE hV hd
  have hgstable : OrderAtPullbackInvariant T (baseChangeProj T L f) :=
    orderAtPullbackInvariant_baseChange_field hG T hT L f
  have hsq : IsPullback S.left (S.top ≫ baseChangeStructMap T L f) S.structMap
      (specMapOfFieldHom T.base L f) := MarkedPullbackSquare.isPullback_comp_baseChangeStructMap S
  obtain ⟨e, hfst, hsnd⟩ :
      ∃ e : S.topScheme ≅ pullback S.structMap (specMapOfFieldHom T.base L f),
        e.hom ≫ pullback.fst S.structMap (specMapOfFieldHom T.base L f) = S.left ∧
          e.hom ≫ pullback.snd S.structMap (specMapOfFieldHom T.base L f) =
            S.top ≫ baseChangeStructMap T L f :=
    ⟨hsq.isoPullback, hsq.isoPullback_hom_fst, hsq.isoPullback_hom_snd⟩
  have hinvfst : e.inv ≫ S.left = pullback.fst S.structMap (specMapOfFieldHom T.base L f) := by
    rw [← hfst, Iso.inv_hom_id_assoc]
  have hinvsnd : e.inv ≫ (S.top ≫ baseChangeStructMap T L f) =
      pullback.snd S.structMap (specMapOfFieldHom T.base L f) := by
    rw [← hsnd, Iso.inv_hom_id_assoc]
  have h2gen : ∀ A : S.baseScheme.IdealSheafData,
      (A.comap S.left).comap e.inv =
        A.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f)) := by
    intro A
    have h : (A.comap S.left).comap e.inv = A.comap (e.inv ≫ S.left) := by simp
    rw [h, hinvfst]
  have hideal : (S.ideal.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))).comap e.hom
      = S.ideal.comap S.left := by
    have h : (S.ideal.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))).comap e.hom
        = S.ideal.comap (e.hom ≫ pullback.fst S.structMap (specMapOfFieldHom T.base L f)) := by simp
    rw [h, hfst]
  have hmapinv : ∀ l : List S.baseScheme.IdealSheafData,
      List.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)
          (List.map (fun D : S.baseScheme.IdealSheafData => D.comap S.left) l)
        = List.map (fun D : S.baseScheme.IdealSheafData =>
            D.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))) l := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, ih, h2gen a]
  have hmapback : ∀ l : List S.topScheme.IdealSheafData,
      List.map (fun D : (pullback S.structMap (specMapOfFieldHom T.base L f)).IdealSheafData =>
          D.comap e.hom) (List.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv) l)
        = l := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, ih, comap_hom_comap_inv_eq_self e a]
  have hdimS : S.lowerTriple.krullDimSucc ≤ n := le_trans S.dim_le hdim
  have hOBS : S.lowerTriple.IsOrderBoundedByMult := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr hord
  have hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (S.lowerTriple.baseChange L f).boundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)) := by
    have h := MarkedIdealWithBoundary.SameNontrivialBoundary.map (fun D => D.comap e.inv) (by simp) hE
    rw [hmapinv] at h
    exact h
  have h0 := isAdmissible_comap_of_iso (k := L) e.symm (S.top ≫ baseChangeStructMap T L f)
    (S.ideal.comap S.left) S.mult E hV
  simp only [Iso.symm_hom] at h0
  rw [hinvsnd, h2gen S.ideal] at h0
  have hval' : ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).IsAdmissible := h0
  have hdim' : ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).krullDimSucc ≤ n := by
    have hde : krullDimSucc S.topScheme = krullDimSucc (pullback S.structMap (specMapOfFieldHom T.base L f)) :=
      krullDimSucc_eq_of_iso e
    show krullDimSucc (pullback S.structMap (specMapOfFieldHom T.base L f)) ≤ n
    rw [← hde]
    exact hd
  have hOB'fun : ∀ y : ↥(pullback S.structMap (specMapOfFieldHom T.base L f)),
      orderAt (S.ideal.comap (pullback.fst S.structMap (specMapOfFieldHom T.base L f))) y
        ≤ (S.mult : ℕ∞) := by
    intro y
    have hy := S.orderAt_comap_verticalMap_le_of_forall_orderAt_le hT hgstable hord (e.inv y)
    have h3 : orderAt ((S.ideal.comap S.left).comap e.symm.hom) y
        = orderAt (S.ideal.comap S.left) (e.symm.hom y) :=
      orderAt_comap_of_isOpenImmersion e.symm.hom _ y
    simp only [Iso.symm_hom] at h3
    rw [h2gen S.ideal] at h3
    rw [h3]
    exact hy
  have hOB' : ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr hOB'fun
  have hpull := hF.base_change S.lowerTriple S.valid hdimS hOBS L f
    (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)) hBE hval' hdim' hOB'
  have htri : ((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom).withBoundary E)
      = S.upperTriple L (baseChangeStructMap T L f) E :=
    markedIdealWithBoundary_mk_congr rfl hideal rfl rfl
  have hBE2 : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).boundary E := by
    show MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D : (pullback S.structMap (specMapOfFieldHom T.base L f)).IdealSheafData =>
        D.comap e.hom) (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))) E
    rw [hmapback]
    exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl E
  have hval2 : (((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).withBoundary E).IsAdmissible := by
    rw [htri]
    exact hV
  have hdim2 : (((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).withBoundary E).krullDimSucc ≤ n := hd
  have hOB2 : (((((S.lowerTriple.baseChange L f).withBoundary
        (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv))).pullbackAlong
        S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom)).withBoundary E).IsOrderBoundedByMult := by
    rw [htri]
    exact (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr
      (fun y => S.orderAt_comap_verticalMap_le_of_forall_orderAt_le hT hgstable hord y)
  have hsmE : AlgebraicGeometry.Smooth e.hom := inferInstance
  have hsjE : AlgebraicGeometry.Surjective e.hom := inferInstance
  have hstrict := @IsOrderReduction.smooth_pullback_strict (fun d => d ≤ n) F G hF
    ((S.lowerTriple.baseChange L f).withBoundary
      (E.map (fun D : S.topScheme.IdealSheafData => D.comap e.inv)))
    hval' hdim' hOB' S.topScheme (S.top ≫ baseChangeStructMap T L f) e.hom hsmE hsjE hsnd E hBE2
    hval2 hdim2 hOB2
  have hres := hpull.comp_isStrictPullbackSequenceOfBlowups hstrict
  rw [hfst] at hres
  exact isPullbackBlowupSequence_of_eq_of_heq F S.lowerTriple htri S.left S.left HEq.rfl hres

/- English proof (authored)
The field extension projection is flat and preserves order in all test squares. The comparison for the order-reduction assignment gives the required rule. Flatness and the order invariance supply the comparison for monomial principalization, and flatness gives the pullback formula for the nonmonomial part. These properties are the components of the asserted base-change compatibility.
-/
theorem baseChangeCompatible_baseChangeProj_of_isOrderReduction (hG : PrincipalizationGeometryHypotheses.{u}) (τ : ComapIsoInvariance.{u}) (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (L : Type u) [Field L] [CharZero L]
    (f : T.base →+* L) :
    BaseChangeCompatible τ F n T (baseChangeProj T L f) L (baseChangeStructMap T L f) := by
  have hflat : AlgebraicGeometry.Flat (baseChangeProj T L f) :=
    inferInstanceAs
      (AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
  exact ⟨commutesWithBaseChange_baseChangeProj_of_isOrderReduction hG n F G hF T hT hdim L f, hflat,
    monomialPrincipalizationBaseChange_of_flat hG τ T hT (baseChangeProj T L f)
      (orderAtPullbackInvariant_baseChange_field hG T hT L f) L (baseChangeStructMap T L f),
    nonMonomialPartBaseChange_of_flat hG T (baseChangeProj T L f) L (baseChangeStructMap T L f),
    orderAtPullbackInvariant_baseChange_field hG T hT L f⟩

end FunctorialResolution.EmbeddedResolution

end
