import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

open scoped Classical

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

noncomputable def balancedTunedIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : T.scheme.IdealSheafData :=
  @balancedTunedSheaf T.base _ _ T.scheme T.structMap hv.locallyOfFiniteType T.ideal T.mult

abbrev tunedMult (T : MarkedIdealWithBoundary.{u}) : ℕ := tuningExponent T.mult

noncomputable def chosenCoverData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactReduction.FiniteOpenCoverWithIdeals T :=
  MaxContactReduction.maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)

/- English proof (authored)
The existence hypothesis selects the branch of the cover construction that chooses a witness to the maximal-contact cover condition. The chosen cover carries that condition by the specification of the witness.
-/
theorem isMaxContactCover_maxContactCover (T : MarkedIdealWithBoundary.{u})
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (μ : ℕ)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T, MaxContactReduction.IsMaxContactCover T D hft W μ) :
    MaxContactReduction.IsMaxContactCover T (MaxContactReduction.maxContactCover T hft W μ) hft W μ := by
  have he : MaxContactReduction.maxContactCover T hft W μ = h.choose := dif_pos h
  rw [he]
  exact h.choose_spec

/- English proof (authored)
The chosen cover data are obtained by applying the cover construction to the balanced tuned ideal and its tuned mark. The given witness lets the construction choose a cover satisfying the required condition for those inputs.
-/
theorem isMaxContactCover_chosenCoverData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)) :
    MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T) :=
  isMaxContactCover_maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T) h

@[reducible] noncomputable def coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (chosenCoverData T hv).disjointUnion ⟶ T.scheme :=
  (chosenCoverData T hv).disjointUnionMap

/- English proof (authored)
The defining cover map is induced from the open inclusions by the universal property of their disjoint union.
-/
theorem coverMap_eq_sigmaOpensDesc (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    coverMap T hv = sigmaOpensDesc T.scheme (chosenCoverData T hv).opens := rfl

/- English proof (authored)
On each open summand the cover map is its open inclusion into the original scheme. These inclusions are étale, and the summands cover the source, so the cover map is étale.
-/
theorem etale_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Etale (coverMap T hv) := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact etale_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens

instance instEtaleCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    Etale (coverMap T hv) :=
  etale_coverMap_of_isAdmissible T hv

/- English proof (authored)
The cover map is étale. Every étale morphism is smooth.
-/
theorem smooth_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Smooth (coverMap T hv) := by
  have : Etale (coverMap T hv) := etale_coverMap_of_isAdmissible T hv
  infer_instance

instance instSmoothCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Smooth (coverMap T hv) :=
  smooth_coverMap_of_isAdmissible T hv

/- English proof (authored)
The cover map is étale. Étale morphisms are flat.
-/
theorem flat_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Flat (coverMap T hv) := by
  have : Etale (coverMap T hv) := etale_coverMap_of_isAdmissible T hv
  infer_instance

instance instFlatCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    AlgebraicGeometry.Flat (coverMap T hv) :=
  flat_coverMap_of_isAdmissible T hv

/- English proof (authored)
The summands are open in the source of the cover map and cover it. On each summand the map is an open immersion, hence locally of finite type. The property is local on the source.
-/
theorem locallyOfFiniteType_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    LocallyOfFiniteType (coverMap T hv) := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact locallyOfFiniteType_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens

instance instLocallyOfFiniteTypeCoverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    LocallyOfFiniteType (coverMap T hv) :=
  locallyOfFiniteType_coverMap T hv

@[reducible] noncomputable def coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (chosenCoverData T hv).disjointUnion.IdealSheafData :=
  (chosenCoverData T hv).iInfImageIdeal

noncomputable def coverTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : MarkedIdealWithBoundary.{u} :=
  (chosenCoverData T hv).markedTriple (balancedTunedIdeal T hv) (tunedMult T)

/- English proof (authored)
The cover triple uses the disjoint union of the chosen open sets as its underlying scheme.
-/
@[simp] theorem coverTriple_scheme (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).scheme = (chosenCoverData T hv).disjointUnion := rfl

/- English proof (authored)
The cover triple uses the original base field.
-/
@[simp] theorem coverTriple_baseField (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).base = T.base := rfl

/- English proof (authored)
The structural map of the cover triple first maps the disjoint union to the original scheme and then applies the original structural map.
-/
@[simp] theorem coverTriple_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).structMap = coverMap T hv ≫ T.structMap := rfl

/- English proof (authored)
The definition of the cover triple assigns it the pullback of the balanced tuned ideal along the cover map.
-/
@[simp] theorem coverTriple_ideal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).ideal = (balancedTunedIdeal T hv).comap (coverMap T hv) := rfl

/- English proof (authored)
The mark of the cover triple is defined to be the tuned mark.
-/
@[simp] theorem coverTriple_mult (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).mult = tunedMult T := rfl

/- English proof (authored)
The boundary of the cover triple is constructed by pulling back each original boundary component along the cover map in its original position.
-/
@[simp] theorem coverTriple_boundary (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).boundary = T.boundary.map (fun D => D.comap (coverMap T hv)) := rfl

/- English proof (authored)
The successor dimension of a triple is computed from its underlying scheme. For the cover triple that scheme is the disjoint union of the chosen open sets.
-/
@[simp] theorem coverTriple_dim (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (coverTriple T hv).krullDimSucc = krullDimSucc (chosenCoverData T hv).disjointUnion := rfl

noncomputable def coverMarkedBlowupData (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData (coverTriple T hv).structMap (coverTriple T hv).ideal
      (coverTriple T hv).mult (coverTriple T hv).boundary :=
  MaxContactReduction.reduceAlongHypersurface hinv T rc (coverTriple T hv) (coverMaxContactIdeal T hv)

/- English proof (authored)
The marked sequence on the cover is defined by applying reduction along a hypersurface to the cover triple and its chosen maximal-contact ideal, using the given recursion and invariance data.
-/
theorem cover_eq_reduceAlongHypersurface (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hinv : ComapIsoInvariance.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) :
    coverMarkedBlowupData T hv hinv rc =
      MaxContactReduction.reduceAlongHypersurface hinv T rc (coverTriple T hv) (coverMaxContactIdeal T hv) := rfl

/- English proof (authored)
If a strict descent exists, the descent operation returns a witness, and equality of the two returned values identifies that witness with the stated sequence. Its defining property is the desired strict pullback relation. If no strict descent exists, the operation returns no sequence, contradicting the hypothesis.
-/
theorem isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some {T S : MarkedIdealWithBoundary.{u}} (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) {d : BlowupSequenceData T.scheme}
    (hd : MaxContactReduction.descendStrictPullback T S φ s = some d) :
    IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups := by
  by_cases hex : ∃ e : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups e.toSequenceOfBlowups
  · have he : MaxContactReduction.descendStrictPullback T S φ s = some hex.choose := dif_pos hex
    rw [he] at hd
    have h2 : hex.choose = d := Option.some.inj hd
    exact h2 ▸ hex.choose_spec
  · have he : MaxContactReduction.descendStrictPullback T S φ s = none := dif_neg hex
    rw [he] at hd
    simp at hd

/- English proof (authored)
By hypothesis there is a strict descent. The descent operation therefore returns a chosen sequence satisfying that condition, which witnesses the claimed existence.
-/
theorem exists_descendStrictPullback_eq_some {T S : MarkedIdealWithBoundary.{u}} (φ : S.scheme ⟶ T.scheme)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (h : ∃ d : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq φ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∃ d : BlowupSequenceData T.scheme, MaxContactReduction.descendStrictPullback T S φ s = some d :=
  ⟨h.choose, dif_pos h⟩

/- English proof (authored)
The mark certificate makes the conversion choose its valid branch. In that branch it equips the same blowup data with the supplied markings and takes the resulting marked sequence.
-/
theorem asMarkedSeq_eq_toMarkedSequence_of_isMarked (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme)
    (h : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    MaxContactReduction.asMarkedSeq T d =
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h).toMarkedSequenceOfBlowups :=
  dif_pos h

/- English proof (authored)
The mark certificate identifies the converted sequence with the one obtained by equipping the original blowup data with markings. Forgetting those markings recovers the original underlying sequence.
-/
theorem asMarkedSeq_toSequenceOfBlowups (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme)
    (h : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    (MaxContactReduction.asMarkedSeq T d).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  rw [asMarkedSeq_eq_toMarkedSequence_of_isMarked T d h,
    BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]

/- English proof (authored)
Admissibility and the nonempty order locus select the branch that trims the boundary, reduces on the resulting cover, and tries to descend. By the given descent identity this branch returns the sequence furnished by the conversion to a marked sequence.
-/
theorem reduceOrder_eq_asMarkedSeq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (hne : orderAtLeastLocus T.ideal T.mult ≠ ∅)
    (htrim : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible) (d : BlowupSequenceData T.scheme)
    (hd : MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
        (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) = some d) :
    MaxContactReduction.reduceOrder hinv T rc = MaxContactReduction.asMarkedSeq T d := by
  have key : MaxContactReduction.reduceOrderOfValid hinv T rc hv = MaxContactReduction.asMarkedSeq T d := by
    show (match MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) with
          | some e => MaxContactReduction.asMarkedSeq T e
          | none => MaxContactReduction.emptyMarkedSeq T) = MaxContactReduction.asMarkedSeq T d
    rw [hd]
  unfold MaxContactReduction.reduceOrder
  rw [dif_pos hv, if_neg hne, key]

/- English proof (authored)
The descent identity expresses the reduction as the marked conversion of the given blowup data. The mark certificate then identifies that conversion with the marked sequence obtained directly from those data.
-/
theorem reduceOrder_eq_toMarkedSequence (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (hv : T.IsAdmissible)
    (hne : orderAtLeastLocus T.ideal T.mult ≠ ∅)
    (htrim : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible) (d : BlowupSequenceData T.scheme)
    (hd : MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
        (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
        (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) = some d)
    (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    MaxContactReduction.reduceOrder hinv T rc =
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  rw [reduceOrder_eq_asMarkedSeq hinv T rc hv hne htrim d hd, asMarkedSeq_eq_toMarkedSequence_of_isMarked T d hm]

/- English proof (authored)
The empty marked sequence comes from the marked blowup data with no steps. Passing to its sequence of blowups preserves that length, which is zero.
-/
@[simp] theorem emptyMarkedSeq_length (T : MarkedIdealWithBoundary.{u}) :
    (MaxContactReduction.emptyMarkedSeq T).length = 0 :=
  emptyMarkedBlowupSequenceData_toMarkedSequence_length T.structMap T.ideal T.mult T.boundary

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

/- English proof (authored)
The certificate says the proposed continuation is marked for the structural map, ideal, mark, and boundary at the last stage. It therefore selects the successful branch of the conversion, which returns the given continuation with this marking.
-/
theorem asMarkedData_eq_some_of_isMarked (s : MarkedBlowupSequenceData p I m E) (d : BlowupSequenceData (s.obj s.length))
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :
    MaxContactReduction.asMarkedData s d =
      some (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h) :=
  dif_pos h

/- English proof (authored)
The mark certificate makes the conversion of the continuation succeed. In that case the concatenation operation appends the resulting marked continuation to the initial sequence.
-/
theorem concatOfIsMarked_eq_append_of_isMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData (s.obj s.length))
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :
    MaxContactReduction.concatOfIsMarked hinv s d =
      s.append (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
        (s.boundary s.length) h) hinv := by
  have hr := asMarkedData_eq_some_of_isMarked s d h
  show (match MaxContactReduction.asMarkedData s d with
        | some t => s.append t hinv
        | none => s) = _
  rw [hr]

end

noncomputable def derivedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary.{u} :=
  MaxContactReduction.tunedTriple S s hft extra keep

/- English proof (authored)
The derived triple is formed on the last stage of the given marked sequence, so that stage is its scheme.
-/
@[simp] theorem derivedTriple_scheme (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).scheme = s.obj s.length := rfl

/- English proof (authored)
The derived triple uses the balanced tuning of the final ideal. Its mark is defined as the tuning exponent of the original mark.
-/
@[simp] theorem derivedTriple_mult (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).mult = tuningExponent S.mult := rfl

/- English proof (authored)
To form the boundary, remove the prescribed initial number of entries from the last-stage boundary. The definition then places the supplemental list before the remaining entries.
-/
@[simp] theorem derivedTriple_boundary (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).boundary = extra ++ (s.boundary s.length).drop keep := rfl

/- English proof (authored)
The structural map from the last stage first projects to the original scheme and then applies that scheme's structural morphism. This is the map specified in the derived triple.
-/
theorem derivedTriple_structureMorphism (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (derivedTriple S s hft extra keep).structMap = s.proj s.length ≫ S.structMap := rfl

/- English proof (authored)
The local finite-type hypothesis permits forming the derived triple, and the dimension bound permits calling the recursion on it at the given index. With both tests passed, the construction tries to append the underlying blowup data of the recursive result as a marked continuation.
-/
theorem appendLowerDimReduction_eq_concatOfIsMarked (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hdim : (derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n =
      MaxContactReduction.concatOfIsMarked hinv s
        (BlowupSequenceData.ofSequenceOfBlowups (rc (derivedTriple S s hft extra keep) hdim n).toSequenceOfBlowups) := by
  unfold MaxContactReduction.appendLowerDimReduction
  rw [dif_pos hft]
  exact dif_pos hdim

/- English proof (authored)
The construction first tests whether the structural map of the last stage is locally of finite type. Here the test fails, so the definition returns the given sequence.
-/
theorem appendLowerDimReduction_of_not_locallyOfFiniteType (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ)
    (hft : ¬ LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n = s := by
  unfold MaxContactReduction.appendLowerDimReduction
  exact dif_neg hft

/- English proof (authored)
Boundary separation is defined recursively on the number of entries to process. At zero it starts with the empty marked sequence for the given ideal, mark, and boundary.
-/
@[simp] theorem separateBoundary_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) :
    MaxContactReduction.separateBoundary hinv T rc S 0 =
      emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary := rfl

/- English proof (authored)
At the successor stage take the previously separated sequence and apply lower-dimensional reduction at the preceding index. In this recursive step the supplemental boundary is empty and the number of entries to drop is zero.
-/
theorem separateBoundary_succ (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u}) (j : ℕ) :
    MaxContactReduction.separateBoundary hinv T rc S (j + 1) =
      MaxContactReduction.appendLowerDimReduction hinv T rc S (MaxContactReduction.separateBoundary hinv T rc S j) [] 0 j := rfl

/- English proof (authored)
The construction first processes all entries of the original boundary by boundary separation. It then calls lower-dimensional reduction at index zero, putting the final strict transform of the hypersurface in the supplemental list and dropping as many boundary entries as the original boundary had.
-/
theorem reduceAlongHypersurface_eq_appendLowerDimReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary.{u})
    (H : S.scheme.IdealSheafData) :
    MaxContactReduction.reduceAlongHypersurface hinv T rc S H =
      MaxContactReduction.appendLowerDimReduction hinv T rc S
        (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length)
        [MaxContactReduction.strictTransformAtLength (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length) H]
        S.boundary.length 0 := rfl

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
