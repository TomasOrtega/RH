import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem nonzeroOnComponents_of_support_ne_univ {X : Scheme.{u}} [IrreducibleSpace ↥X]
    (I : X.IdealSheafData) (h : (↑I.support : Set ↥X) ≠ Set.univ) :
    NonzeroOnComponents I := by
  intro T hT hsub
  have huniv : IsIrreducible (Set.univ : Set ↥X) := IrreducibleSpace.isIrreducible_univ ↥X
  have hle : (Set.univ : Set ↥X) ⊆ T := hT.2 huniv (Set.subset_univ T)
  exact h (Set.univ_subset_iff.mp (hle.trans hsub))

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem base_injective_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : Function.Injective ⇑f.base :=
  (Scheme.Hom.isClosedEmbedding f).injective

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem isClosed_range_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : IsClosed (Set.range ⇑f.base) :=
  (Scheme.Hom.isClosedEmbedding f).isClosed_range

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
private theorem support_ker_eq_range_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] :
    ((Scheme.Hom.ker f).support : Set ↥Y) = Set.range ⇑f.base := by
  have hcl := (isClosed_range_of_isClosedImmersion f).closure_eq
  simp [Scheme.Hom.support_ker, hcl]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem nonzeroOnComponents_ker_comp {Y A A' : Scheme.{u}} (j : Y ⟶ A) (i : A ⟶ A')
    [IsClosedImmersion j] [IsClosedImmersion i] [IrreducibleSpace ↥A']
    (h : NonzeroOnComponents (Scheme.Hom.ker j)) :
    NonzeroOnComponents (Scheme.Hom.ker (j ≫ i)) := by
  refine nonzeroOnComponents_of_support_ne_univ _ ?_
  rw [support_ker_eq_range_of_isClosedImmersion (j ≫ i)]
  intro hrange
  have hsurj : ∀ z : ↥A', ∃ y : ↥Y, (j ≫ i).base y = z := by
    intro z
    have hz : z ∈ Set.range ⇑(j ≫ i).base := by
      rw [hrange]
      exact Set.mem_univ z
    exact Set.mem_range.mp hz
  obtain ⟨a'⟩ : Nonempty ↥A' := inferInstance
  obtain ⟨y, -⟩ := hsurj a'
  have hjsurj : ∀ b : ↥A, ∃ y' : ↥Y, j.base y' = b := by
    intro b
    obtain ⟨y', hy'⟩ := hsurj (i.base b)
    refine ⟨y', base_injective_of_isClosedImmersion i ?_⟩
    simpa using hy'
  refine h (irreducibleComponent (j.base y))
    (irreducibleComponent_mem_irreducibleComponents _) ?_
  rw [support_ker_eq_range_of_isClosedImmersion j]
  intro b _
  exact Set.mem_range.mpr (hjsurj b)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem appTop_comp_apply_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (a ≫ b))) x
      = (ConcreteCategory.hom (Scheme.Hom.appTop a))
          ((ConcreteCategory.hom (Scheme.Hom.appTop b)) x) := by
  have h : Scheme.Hom.appTop (a ≫ b) = Scheme.Hom.appTop b ≫ Scheme.Hom.appTop a := by
    simp
  rw [h]
  rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isClosedImmersion_of_coord_surjective {R : CommRingCat.{u}} {N M : Type u}
    (f : AffineSpace N (Spec R) ⟶ AffineSpace M (Spec R))
    (hover : f ≫ (AffineSpace M (Spec R) ↘ Spec R) = (AffineSpace N (Spec R) ↘ Spec R))
    (hcoord : ∀ i : N, ∃ s : ↑((AffineSpace M (Spec R)).presheaf.obj (Opposite.op ⊤)),
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) s = AffineSpace.coord (Spec R) i) :
    IsClosedImmersion f := by
  choose s hs using hcoord
  have hgcoord : ∀ i : N,
      (ConcreteCategory.hom (Scheme.Hom.appTop
        (AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s)))
        (AffineSpace.coord (Spec R) i) = s i := by
    intro i
    simp [AffineSpace.homOfVector_appTop_coord]
  have key : f ≫ AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s
      = 𝟙 (AffineSpace N (Spec R)) := by
    apply AffineSpace.hom_ext
    · simp [hover]
    · intro i
      rw [appTop_comp_apply_eq, hgcoord i, hs i]
      simp
  have hsurj : Function.Surjective (ConcreteCategory.hom (Scheme.Hom.appTop f)) := by
    intro x
    refine ⟨(ConcreteCategory.hom (Scheme.Hom.appTop
      (AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s))) x, ?_⟩
    have h : (ConcreteCategory.hom (Scheme.Hom.appTop
          (f ≫ AffineSpace.homOfVector (AffineSpace M (Spec R) ↘ Spec R) s))) x
        = (ConcreteCategory.hom (Scheme.Hom.appTop (𝟙 (AffineSpace N (Spec R))))) x := by
      rw [key]
    rw [appTop_comp_apply_eq] at h
    simpa using h
  exact IsClosedImmersion.of_surjective_of_isAffine f hsurj

def affineSpaceInl (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m)) :=
  AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
    (coordVectorInl n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))))

def affineSpaceInrEmbedding (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m)) :=
  AffineSpace.homOfVector (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
    (coordVectorInr n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))))

@[simp]
/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem affineSpaceInl_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) := by
  simp [affineSpaceInl]

@[simp]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) := by
  simp [affineSpaceInrEmbedding]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem pullbackCoord_id {k : Type u} [Field k] {N : Type u} (j : N) :
    pullbackCoord (𝟙 (affineSpaceIndexedBy k N)) j
      = AffineSpace.coord (Spec (CommRingCat.of k)) j := by
  simp

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem pullbackCoord_affineSpaceInl (k : Type u) [Field k] (n m : ℕ)
    (i : ULift.{u, 0} (Fin n ⊕ Fin m)) :
    pullbackCoord (affineSpaceInl k n m) i =
      Sum.elim (fun a : Fin n =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        (fun _ : Fin m => 0) i.down := by
  have h : pullbackCoord (affineSpaceInl k n m) i
      = coordVectorInl n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))) i := by
    simp only [pullbackCoord_def, affineSpaceInl, AffineSpace.homOfVector_appTop_coord]
  rw [h]
  obtain ⟨j⟩ := i
  cases j with
  | inl a =>
      show pullbackCoord (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))) (ULift.up.{u, 0} a)
          = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)
      exact pullbackCoord_id _
  | inr _ => rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullbackCoord_affineSpaceInl_inl (k : Type u) [Field k] (n m : ℕ) (a : Fin n) :
    pullbackCoord (affineSpaceInl k n m) (ULift.up.{u, 0} (Sum.inl a)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) :=
  pullbackCoord_affineSpaceInl k n m (ULift.up.{u, 0} (Sum.inl a))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullbackCoord_affineSpaceInl_inr (k : Type u) [Field k] (n m : ℕ) (b : Fin m) :
    pullbackCoord (affineSpaceInl k n m) (ULift.up.{u, 0} (Sum.inr b)) = 0 :=
  pullbackCoord_affineSpaceInl k n m (ULift.up.{u, 0} (Sum.inr b))

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem pullbackCoord_affineSpaceInrEmbedding (k : Type u) [Field k] (n m : ℕ)
    (i : ULift.{u, 0} (Fin n ⊕ Fin m)) :
    pullbackCoord (affineSpaceInrEmbedding k n m) i =
      Sum.elim (fun _ : Fin n => 0)
        (fun b : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b)) i.down := by
  have h : pullbackCoord (affineSpaceInrEmbedding k n m) i
      = coordVectorInr n m (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))) i := by
    simp only [pullbackCoord_def, affineSpaceInrEmbedding, AffineSpace.homOfVector_appTop_coord]
  rw [h]
  obtain ⟨j⟩ := i
  cases j with
  | inl _ => rfl
  | inr b =>
      show pullbackCoord (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))) (ULift.up.{u, 0} b)
          = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b)
      exact pullbackCoord_id _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullbackCoord_affineSpaceInrEmbedding_inl (k : Type u) [Field k] (n m : ℕ) (a : Fin n) :
    pullbackCoord (affineSpaceInrEmbedding k n m) (ULift.up.{u, 0} (Sum.inl a)) = 0 :=
  pullbackCoord_affineSpaceInrEmbedding k n m (ULift.up.{u, 0} (Sum.inl a))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pullbackCoord_affineSpaceInrEmbedding_inr (k : Type u) [Field k] (n m : ℕ) (b : Fin m) :
    pullbackCoord (affineSpaceInrEmbedding k n m) (ULift.up.{u, 0} (Sum.inr b)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b) :=
  pullbackCoord_affineSpaceInrEmbedding k n m (ULift.up.{u, 0} (Sum.inr b))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isClosedImmersion_affineSpaceInl (k : Type u) [Field k] (n m : ℕ) :
    IsClosedImmersion (affineSpaceInl k n m) := by
  refine isClosedImmersion_of_coord_surjective (affineSpaceInl k n m)
    (affineSpaceInl_comp_affineSpaceIndexedByToSpec k n m) ?_
  rintro ⟨a⟩
  refine ⟨AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} (Sum.inl a)), ?_⟩
  have h : pullbackCoord (affineSpaceInl k n m) (ULift.up.{u, 0} (Sum.inl a))
      = AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) :=
    pullbackCoord_affineSpaceInl_inl k n m a
  exact h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isClosedImmersion_affineSpaceInrEmbedding (k : Type u) [Field k] (n m : ℕ) :
    IsClosedImmersion (affineSpaceInrEmbedding k n m) := by
  refine isClosedImmersion_of_coord_surjective (R := CommRingCat.of k)
    (N := ULift.{u, 0} (Fin m)) (M := ULift.{u, 0} (Fin n ⊕ Fin m))
    (affineSpaceInrEmbedding k n m) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k n m) ?_
  intro i
  refine ⟨AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} (Sum.inr i.down)), ?_⟩
  exact pullbackCoord_affineSpaceInrEmbedding k n m (ULift.up.{u, 0} (Sum.inr i.down))

instance instIsClosedImmersionLinEmbLeft (k : Type u) [Field k] (n m : ℕ) :
    IsClosedImmersion (affineSpaceInl k n m) :=
  isClosedImmersion_affineSpaceInl k n m

instance instIsClosedImmersionLinEmbRight (k : Type u) [Field k] (n m : ℕ) :
    IsClosedImmersion (affineSpaceInrEmbedding k n m) :=
  isClosedImmersion_affineSpaceInrEmbedding k n m

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem comp_affineSpaceInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (q : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = q) :
    f ≫ affineSpaceInl k n m = AffineSpace.homOfVector q (coordVectorInl n m f) := by
  apply AffineSpace.hom_ext
  · simp [hf]
  · intro i
    obtain ⟨j⟩ := i
    rw [appTop_comp_apply_eq, AffineSpace.homOfVector_appTop_coord, ← pullbackCoord_def,
      pullbackCoord_affineSpaceInl]
    cases j with
    | inl _ => rfl
    | inr _ => exact map_zero _

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data.

Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem comp_affineSpaceInrEmbedding {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (q : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) = q) :
    f ≫ affineSpaceInrEmbedding k n m = AffineSpace.homOfVector q (coordVectorInr n m f) := by
  apply AffineSpace.hom_ext
  · simp [hf]
  · rintro ⟨j⟩
    rw [appTop_comp_apply_eq, AffineSpace.homOfVector_appTop_coord]
    cases j with
    | inl a =>
        have h := pullbackCoord_affineSpaceInrEmbedding_inl k n m a
        rw [pullbackCoord_def] at h
        rw [h, map_zero, coordVectorInr_inl]
    | inr b =>
        have h := pullbackCoord_affineSpaceInrEmbedding_inr k n m b
        rw [pullbackCoord_def] at h
        rw [h, coordVectorInr_inr, pullbackCoord_def]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem IsStrictPullbackBlowupSeq.id {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    IsStrictPullbackBlowupSeq (𝟙 X) s s := by
  refine ⟨rfl, fun i _ => 𝟙 (s.schemeAt i), by simp, fun i _ => ?_, fun i _ => ?_⟩
  · exact IsPullback.of_id_fst
  · simp

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isomorphic_of_isPullbackSequenceOfBlowups_id {X : Scheme.{u}} (s t : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s t) (hc : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    s.Isomorphic t := by
  have : AlgebraicGeometry.Surjective (𝟙 X) := inferInstance
  exact IsStrictPullbackBlowupSeq.isomorphic (h.isStrictPullback_of_surjective hc)
    (IsStrictPullbackBlowupSeq.id t)

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem smooth_affineSpaceIndexedByToSpec (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (n : ℕ) :
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) :=
  hsm k n

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem inStrictNormalCrossingPosition_nil_affineSpace (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (n : ℕ) :
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) [] := by
  have : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) := hsm k n
  exact inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))

def EmbeddingDatum.ofClosedImmersionAffineSpace (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (n : ℕ)
    (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) [IsClosedImmersion e]
    (hker : NonzeroOnComponents (Scheme.Hom.ker e))
    (hcomp : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = p) :
    EmbeddingDatum k Y p where
  ambient := affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))
  ambientStruct := affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))
  emb := e
  isAffine_ambient := by unfold affineSpaceIndexedBy; infer_instance
  smooth_ambientStruct := smooth_affineSpaceIndexedByToSpec hsm k n
  locallyOfFiniteType_ambientStruct := by unfold affineSpaceIndexedByToSpec; infer_instance
  quasiCompact_ambientStruct := by unfold affineSpaceIndexedByToSpec; infer_instance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := inStrictNormalCrossingPosition_nil_affineSpace hsm k n

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem EmbeddingDatum.ofClosedImmersionAffineSpace_ambient (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k]
    [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (n : ℕ)
    (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) [IsClosedImmersion e]
    (hker : NonzeroOnComponents (Scheme.Hom.ker e))
    (hcomp : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = p) :
    (EmbeddingDatum.ofClosedImmersionAffineSpace hsm n e hker hcomp).ambient =
      affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) :=
  rfl

end FunctorialResolution.EmbeddedResolution

end
