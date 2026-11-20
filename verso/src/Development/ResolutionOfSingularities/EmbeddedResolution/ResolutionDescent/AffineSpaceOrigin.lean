import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    Spec (CommRingCat.of k) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k))) (fun _ => 0)

@[simp]
/- English proof (authored)
The origin is the affine-space map defined by zero coordinates over the identity of the field spectrum. Composing with the structure map recovers that identity.
-/
theorem affineSpaceOrigin_comp_toSpec (k : Type u) [Field k] (m : ℕ) :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) =
      𝟙 (Spec (CommRingCat.of k)) := by
  unfold affineSpaceOrigin
  simp

@[simp]
/- English proof (authored)
The origin followed by the structure map is the identity on the field spectrum. Composing with the given map therefore returns the given map.
-/
theorem affineSpaceOrigin_comp_toSpec_assoc (k : Type u) [Field k] (m : ℕ) {Z : Scheme.{u}}
    (g : Spec (CommRingCat.of k) ⟶ Z) :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫ g = g := by
  rw [← Category.assoc, affineSpaceOrigin_comp_toSpec, Category.id_comp]

/- English proof (authored)
The defining vector of the origin is zero at every coordinate. Its pullback of the specified coordinate is therefore zero.
-/
theorem pullbackCoord_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    pullbackCoord (affineSpaceOrigin k m) i = 0 := by
  simp [pullbackCoord_def, affineSpaceOrigin]

@[simp]
/- English proof (authored)
The map on global sections sends each target coordinate to the corresponding entry of the defining vector of the origin. This entry is zero.
-/
theorem affineSpaceOrigin_appTop_coord (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) i) = 0 := by
  simp [affineSpaceOrigin]

/- English proof (authored)
A morphism into affine space is determined by its structural map and the pullback of each coordinate. The given map has the identity as its structural map and sends all coordinates to zero, just as the origin does.
-/
theorem eq_affineSpaceOrigin_of_pullbackCoord_eq_zero (k : Type u) [Field k] (m : ℕ)
    (f : Spec (CommRingCat.of k) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) = 𝟙 (Spec (CommRingCat.of k)))
    (hcoord : ∀ i : ULift.{u, 0} (Fin m), pullbackCoord f i = 0) :
    f = affineSpaceOrigin k m := by
  refine AffineSpace.hom_ext ?_ ?_
  · simpa only [affineSpaceOrigin, AffineSpace.homOfVector_over] using hf
  · intro i
    simpa only [affineSpaceOrigin, AffineSpace.homOfVector_appTop_coord, pullbackCoord_def]
      using hcoord i

/- English proof (authored)
The structural map after the origin is the identity, so pullback along the structural map is a right inverse to pullback along the origin on global sections. Thus the origin's section map is surjective. Both schemes are affine, so the origin is a closed immersion.
-/
theorem isClosedImmersion_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    IsClosedImmersion (affineSpaceOrigin k m) := by
  have hsurj : Function.Surjective
      (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) := by
    intro x
    refine ⟨(ConcreteCategory.hom
        (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))))) x, ?_⟩
    have h1 : Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) ≫
        Scheme.Hom.appTop (affineSpaceOrigin k m) =
        Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k))) := by
      rw [← Scheme.Hom.comp_appTop, affineSpaceOrigin_comp_toSpec]
    have h2 : (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m)))
        ((ConcreteCategory.hom
          (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))))) x) =
        (ConcreteCategory.hom
          (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) ≫
            Scheme.Hom.appTop (affineSpaceOrigin k m))) x := by
      simp
    rw [h2, h1]
    simp
  apply IsClosedImmersion.of_surjective_of_isAffine
  exact hsurj

instance instIsClosedImmersionAffineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    IsClosedImmersion (affineSpaceOrigin k m) :=
  isClosedImmersion_affineSpaceOrigin k m

/- English proof (authored)
Pullback of global sections is a contravariant functor. Its value on the identity scheme map is the identity ring map.
-/
private theorem appTop_id (X : Scheme.{u}) :
    Scheme.Hom.appTop (𝟙 X) = 𝟙 (X.presheaf.obj (Opposite.op ⊤)) := by
  simp [Scheme.Hom.appTop]

/- English proof (authored)
The successive pullbacks are the pullback along the composite of the isomorphism and its inverse. That composite is the identity, which fixes every section.
-/
private theorem appTop_hom_appTop_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y)
    (x : ↑(X.presheaf.obj (Opposite.op ⊤))) :
    CommRingCat.Hom.hom (Scheme.Hom.appTop e.hom)
        (CommRingCat.Hom.hom (Scheme.Hom.appTop e.inv) x) = x := by
  have h : Scheme.Hom.appTop e.inv ≫ Scheme.Hom.appTop e.hom =
      𝟙 (X.presheaf.obj (Opposite.op ⊤)) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, appTop_id]
  have h2 := congrArg (fun φ => CommRingCat.Hom.hom φ x) h
  simpa using h2

/- English proof (authored)
The global sections of the field spectrum identify with the field. Under this identification zero and one are distinct, so the section ring is nontrivial.
-/
private theorem nontrivial_globalSections_spec (k : Type u) [Field k] :
    Nontrivial ↑((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤)) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h3 := congrArg (fun z => CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of k)).hom z) h
  simp only [map_one, map_zero] at h3
  have h4 : (1 : k) = 0 := h3
  exact one_ne_zero h4

private def mvPolynomialFinToAffineSpaceGlobalSections (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u, 0} (Fin m)) k →+*
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))).presheaf.obj (Opposite.op ⊤)) :=
  RingHom.comp
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
      (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).hom))
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv)

/- English proof (authored)
The section associated to a polynomial is obtained by first taking its section on the polynomial spectrum and then pulling back along the affine-space isomorphism.
-/
private theorem mvPolynomialToSections_apply (k : Type u) [Field k] (m : ℕ)
    (x : MvPolynomial (ULift.{u, 0} (Fin m)) k) :
    mvPolynomialFinToAffineSpaceGlobalSections k m x =
      CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).hom)
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso
          (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv x) := rfl

/- English proof (authored)
Under the inverse affine-space isomorphism, the coordinate pulls back to the section of its corresponding polynomial variable. The polynomial-to-section map then pulls this section back along the forward isomorphism, recovering the original coordinate.
-/
private theorem mvPolynomialToSections_X (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    mvPolynomialFinToAffineSpaceGlobalSections k m (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  have hX : CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv)
        (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv (MvPolynomial.X i) := by
    exact AffineSpace.SpecIso_inv_appTop_coord ..
  rw [mvPolynomialToSections_apply, ← hX]
  exact appTop_hom_appTop_inv_apply _ _

/- English proof (authored)
Given an affine-space section, pull it back along the inverse isomorphism to the polynomial spectrum. Take the polynomial corresponding to this section. Both steps are reversed by the polynomial-to-section map, so the chosen polynomial maps to the original section.
-/
private theorem mvPolynomialToSections_surjective (k : Type u) [Field k] (m : ℕ) :
    Function.Surjective (mvPolynomialFinToAffineSpaceGlobalSections k m) := by
  intro x
  refine ⟨CommRingCat.Hom.hom (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).hom
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x), ?_⟩
  have hinv : CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv
      (CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).hom
        (CommRingCat.Hom.hom (Scheme.Hom.appTop
          (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x)) =
      CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x := by
    exact CommRingCat.inv_hom_apply ..
  rw [mvPolynomialToSections_apply, hinv, appTop_hom_appTop_inv_apply]

/- English proof (authored)
Subtract the constant term. Every remaining monomial contains at least one variable and hence lies in the ideal generated by the variables. Equivalently, polynomial induction gives zero for a constant, preserves the assertion under addition, and gives a multiple of a generator for a polynomial multiplied by a variable.
-/
private theorem sub_C_constantCoeff_mem_span_X {σ : Type u} {A : Type u} [CommRing A]
    (p : MvPolynomial σ A) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ A)) := by
  induction p using MvPolynomial.induction_on
  · rename_i a
    simp only [MvPolynomial.constantCoeff_C, sub_self]
    exact Ideal.zero_mem _
  · rename_i q r hq hr
    have hadd : q + r - MvPolynomial.C (MvPolynomial.constantCoeff (q + r)) =
        (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) +
          (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]
      ring
    rw [hadd]
    exact Ideal.add_mem _ hq hr
  · rename_i q i hq
    have hmul : q * MvPolynomial.X i -
        MvPolynomial.C (MvPolynomial.constantCoeff (q * MvPolynomial.X i)) =
        q * MvPolynomial.X i := by
      simp
    rw [hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (authored)
Each variable maps to zero, so the ideal they generate lies in the kernel. Any polynomial differs from its constant term by an element of this ideal. If it lies in the kernel, its constant term also maps to zero. The restriction of the ring map to the coefficient field is injective because the target is nontrivial, so that constant term is zero. The polynomial then belongs to the variable ideal.
-/
private theorem ker_eq_span_range_X {σ : Type u} {K : Type u} [Field K] {T : Type u}
    [CommRing T] [Nontrivial T] (g : MvPolynomial σ K →+* T)
    (hg : ∀ i, g (MvPolynomial.X i) = 0) :
    RingHom.ker g = Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
  have hspan : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simpa [RingHom.mem_ker] using hg i
  refine le_antisymm ?_ hspan
  intro p hp
  have hsub := sub_C_constantCoeff_mem_span_X (σ := σ) (A := K) p
  have h1 : g (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 :=
    RingHom.mem_ker.mp (hspan hsub)
  have hp0 : g p = 0 := RingHom.mem_ker.mp hp
  have h0 : g (MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 := by
    rw [map_sub, hp0, zero_sub, neg_eq_zero] at h1
    exact h1
  have hc : MvPolynomial.constantCoeff p = 0 := by
    have hinj : Function.Injective (g.comp (MvPolynomial.C : K →+* MvPolynomial σ K)) :=
      RingHom.injective _
    apply hinj
    simpa using h0
  have hpe : p = p - MvPolynomial.C (MvPolynomial.constantCoeff p) := by
    rw [hc, map_zero, sub_zero]
  rw [hpe]
  exact hsub

/- English proof (authored)
The kernel of the composite is the inverse image of the second map's kernel along the first map. Since the first map is surjective, mapping this inverse image forward recovers the second kernel. Mapping an ideal generated by a set gives the ideal generated by its images, yielding the asserted formula.
-/
private theorem ker_eq_span_image_of_surjective {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (ψ : A →+* B) (hsurj : Function.Surjective ψ) (g : B →+* C) (s : Set A)
    (h : RingHom.ker (g.comp ψ) = Ideal.span s) :
    RingHom.ker g = Ideal.span (ψ '' s) := by
  have h1 : Ideal.comap ψ (RingHom.ker g) = Ideal.span s := by
    rw [← h]
    ext x
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have h2 : Ideal.map ψ (Ideal.comap ψ (RingHom.ker g)) = RingHom.ker g :=
    Ideal.map_comap_of_surjective ψ hsurj _
  rw [← h2, h1, Ideal.map_span]

/- English proof (authored)
Compose the origin's section map with the surjection from polynomials to affine-space sections. The composite sends every variable to zero and has nontrivial target, so its kernel is generated by the variables. By surjectivity, the original kernel is generated by their images in the section ring. Those images are precisely the affine coordinates.
-/
private theorem ker_appTop_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) =
      Ideal.span (Set.range fun i : Fin m =>
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) := by
  have := nontrivial_globalSections_spec k
  have hcomp : RingHom.ker
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))).comp
        (mvPolynomialFinToAffineSpaceGlobalSections k m)) =
      Ideal.span (Set.range
        (MvPolynomial.X : ULift.{u, 0} (Fin m) → MvPolynomial (ULift.{u, 0} (Fin m)) k)) := by
    refine ker_eq_span_range_X _ ?_
    intro i
    rw [RingHom.comp_apply, mvPolynomialToSections_X k m i]
    exact affineSpaceOrigin_appTop_coord k m i
  have main := ker_eq_span_image_of_surjective (mvPolynomialFinToAffineSpaceGlobalSections k m)
    (mvPolynomialToSections_surjective k m)
    (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) _ hcomp
  rw [main]
  congr 1
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := hp
    exact ⟨j.down, (mvPolynomialToSections_X k m j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X (ULift.up.{u, 0} i), Set.mem_range_self _,
      mvPolynomialToSections_X k m (ULift.up.{u, 0} i)⟩

/- English proof (authored)
On an affine scheme the kernel ideal sheaf of this quasi-compact map is determined by the kernel on global sections. This kernel is generated by all the coordinate sections, which is the global ideal of the full coordinate subspace ideal.
-/
theorem ker_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    Scheme.Hom.ker (affineSpaceOrigin k m) = coordSubspaceIdeal k m Finset.univ := by
  have : QuasiCompact (affineSpaceOrigin k m) := inferInstance
  have hker : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app (affineSpaceOrigin k m) ⊤)) =
      Ideal.span (Set.range fun i : Fin m =>
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) :=
    ker_appTop_affineSpaceOrigin k m
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simpa using hker

/- English proof (authored)
Pulling the coordinate back along a composite pulls it back along the second map and then applies the first map's pullback on sections.
-/
private theorem pullbackCoord_comp_eq_hom_appTop_apply {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {n : Type u} (f : Y ⟶ Z) (g : Z ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (f ≫ g) i =
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) (pullbackCoord g i) := by
  rw [pullbackCoord_def, pullbackCoord_def, Scheme.Hom.comp_appTop]
  rfl

@[simp]
/- English proof (authored)
The composite preserves the structural map and pulls each coordinate back to itself because first-block projection recovers the coordinates retained by the first-block inclusion. It is therefore the identity.
-/
theorem affineSpaceInl_comp_projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ projLeft k n m = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, Category.id_comp]
  · rintro ⟨a⟩
    have h : pullbackCoord (affineSpaceInl k n m ≫ projLeft k n m) (ULift.up.{u, 0} a) =
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projLeft k n m),
        projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inl]
    rw [← pullbackCoord_def, h]
    simp

@[simp]
/- English proof (authored)
The first-block inclusion followed by its projection is the identity. Following this by the given map returns the given map.
-/
theorem affineSpaceInl_comp_projLeft_assoc (k : Type u) [Field k] (n m : ℕ) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) ⟶ Z) :
    affineSpaceInl k n m ≫ projLeft k n m ≫ g = g := by
  rw [← Category.assoc, affineSpaceInl_comp_projLeft, Category.id_comp]

@[simp]
/- English proof (authored)
The composite is over the field and recovers each second-block coordinate retained by the inclusion. By the coordinate characterization it is the identity.
-/
theorem affineSpaceInrEmbedding_comp_projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ projRight k n m = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, Category.id_comp]
  · rintro ⟨b⟩
    have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projRight k n m) (ULift.up.{u, 0} b) =
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b) := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projRight k n m),
        projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inr]
    rw [← pullbackCoord_def, h]
    simp

@[simp]
/- English proof (authored)
The second-block inclusion followed by its projection is the identity. Composing with the given map therefore gives that map.
-/
theorem affineSpaceInrEmbedding_comp_projRight_assoc (k : Type u) [Field k] (n m : ℕ) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) ⟶ Z) :
    affineSpaceInrEmbedding k n m ≫ projRight k n m ≫ g = g := by
  rw [← Category.assoc, affineSpaceInrEmbedding_comp_projRight, Category.id_comp]

/- English proof (authored)
Both maps have the original structural map to the field. The projection to the second block reads only the zero coordinates appended by the first inclusion, so every coordinate pulls back to zero. This agrees with the map through the origin of the second block.
-/
theorem affineSpaceInl_comp_projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ projRight k n m =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) ≫ affineSpaceOrigin k m := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, Category.assoc,
      affineSpaceOrigin_comp_toSpec, Category.comp_id]
  · rintro ⟨b⟩
    have h : pullbackCoord (affineSpaceInl k n m ≫ projRight k n m) (ULift.up.{u, 0} b) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projRight k n m),
        projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inr]
    have h2 : pullbackCoord
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) ≫ affineSpaceOrigin k m)
        (ULift.up.{u, 0} b) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_affineSpaceOrigin, map_zero]
    rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]

/- English proof (authored)
The two maps preserve the field structure. The second-block inclusion sets all first-block coordinates to zero, so the first projection after it has the same coordinate pullbacks as the composite through the first-block origin.
-/
theorem affineSpaceInrEmbedding_comp_projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ projLeft k n m =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫ affineSpaceOrigin k n := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, Category.assoc,
      affineSpaceOrigin_comp_toSpec, Category.comp_id]
  · rintro ⟨a⟩
    have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projLeft k n m) (ULift.up.{u, 0} a) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projLeft k n m),
        projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inl]
    have h2 : pullbackCoord (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫
        affineSpaceOrigin k n) (ULift.up.{u, 0} a) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_affineSpaceOrigin]
      simp
    rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]

/- English proof (authored)
The first-block inclusion is the pullback of the second-block origin along the second projection. To see this, use the affine product square and cancel it from the outer rectangle, which is a pullback because both the first projection of the inclusion and the field projection of the origin are identities. The second projection is smooth and hence flat, and the closed immersions in the square are quasi-compact. The flat pullback formula for kernels gives the equality.
-/
theorem ker_affineSpaceInl_eq_comap (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    Scheme.Hom.ker (affineSpaceInl k n m) =
      (Scheme.Hom.ker (affineSpaceOrigin k m)).comap (projRight k n m) := by
  have hsmooth : AlgebraicGeometry.Smooth (projRight k n m) := smooth_projRight hsm k n m
  have hflat : AlgebraicGeometry.Flat (projRight k n m) := inferInstance
  have hbig : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
      (affineSpaceInl k n m ≫ projLeft k n m)
      (affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) := by
    rw [affineSpaceInl_comp_projLeft, affineSpaceOrigin_comp_toSpec]
    exact IsPullback.id_vert _
  have hsq : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) (affineSpaceInl k n m)
      (affineSpaceOrigin k m) (projRight k n m) :=
    IsPullback.of_bot hbig (affineSpaceInl_comp_projRight k n m).symm
      (isPullback_projLeft_projRight k n m).flip
  have : QuasiCompact (affineSpaceOrigin k m) := inferInstance
  have : QuasiCompact (affineSpaceInl k n m) := quasiCompact_of_isPullback hsq
  exact ker_eq_comap_ker_of_isPullback_of_flat hsq

/- English proof (authored)
Place the square above the affine product square. The second projection of the inclusion is the identity and the structure map of the first-block origin after that origin is the identity. These identify the outer rectangle with the pullback of an identity. The inner square commutes by the first-projection formula for the second-block inclusion, so cancelling the product square proves the claim.
-/
private theorem isPullback_affineSpaceInrEmbedding_projLeft (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) (affineSpaceInrEmbedding k n m)
      (affineSpaceOrigin k n) (projLeft k n m) := by
  have h0 : IsPullback (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (𝟙 (Spec (CommRingCat.of k))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have s : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceInrEmbedding k n m ≫ projRight k n m)
      (affineSpaceOrigin k n ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) := by
    rw [affineSpaceInrEmbedding_comp_projRight, affineSpaceOrigin_comp_toSpec]
    exact h0.flip
  exact IsPullback.of_bot s (affineSpaceInrEmbedding_comp_projLeft k n m).symm
    (isPullback_projLeft_projRight k n m)

/- English proof (authored)
The second-block inclusion is the base change of the first-block origin along the first projection. This projection is smooth and therefore flat, and the two closed immersions are quasi-compact. Apply the flat pullback formula to identify their kernel ideals.
-/
theorem ker_affineSpaceInrEmbedding_eq_comap (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    Scheme.Hom.ker (affineSpaceInrEmbedding k n m) =
      (Scheme.Hom.ker (affineSpaceOrigin k n)).comap (projLeft k n m) := by
  have hsmooth : AlgebraicGeometry.Smooth (projLeft k n m) := smooth_projLeft hsm k n m
  have hflat : AlgebraicGeometry.Flat (projLeft k n m) := inferInstance
  have hq1 : AlgebraicGeometry.QuasiCompact (affineSpaceOrigin k n) := inferInstance
  have hq2 : AlgebraicGeometry.QuasiCompact (affineSpaceInrEmbedding k n m) := inferInstance
  exact ker_eq_comap_ker_of_isPullback_of_flat (isPullback_affineSpaceInrEmbedding_projLeft k n m)

/- English proof (authored)
Use the whole target affine space as the chart domain, with the projection to the second block as the chart. It is smooth and over the field. The kernel of the first-block inclusion is the pullback along this projection of the origin ideal of the second block. That ideal is generated by all its coordinates, giving the stated codimension.
-/
theorem hasSmoothCoordCodim_affineSpaceInl (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (n m : ℕ) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
      (affineSpaceInl k n m) m := by
  have hsp : AlgebraicGeometry.Smooth (projRight k n m) := smooth_projRight hsm k n m
  intro x
  refine ⟨⊤, ?_, (⊤ : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m))).Opens).ι ≫
      projRight k n m, ?_, ?_, ?_⟩
  · trivial
  · infer_instance
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec]
  · rw [restrictIdeal_eq_comap_ι, ker_affineSpaceInl_eq_comap hsm, ker_affineSpaceOrigin,
      Scheme.IdealSheafData.comap_comp]

/- English proof (authored)
Take the entire target as the chart and the smooth projection to the first block as its coordinate map over the field. The defining ideal of the inclusion is the pullback of the first-block origin ideal, which is generated by its full set of coordinates. This yields the required codimension.
-/
theorem hasSmoothCoordCodim_affineSpaceInrEmbedding (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (n m : ℕ) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
      (affineSpaceInrEmbedding k n m) n := by
  have hsmooth : AlgebraicGeometry.Smooth (projLeft k n m) := smooth_projLeft hsm k n m
  intro x
  refine ⟨⊤, by simp, (⊤ : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m))).Opens).ι ≫
      projLeft k n m, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec]
  · rw [restrictIdeal_eq_comap_ι, ker_affineSpaceInrEmbedding_eq_comap hsm k n m, ker_affineSpaceOrigin k n]
    simp [Scheme.IdealSheafData.comap_comp]

end FunctorialResolution.EmbeddedResolution

end
