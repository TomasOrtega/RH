import Mathlib

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace JacobianCriterion

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)

end

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
/- English proof (authored)
The differentials of the polynomial variables form a basis over the polynomial ring. Extending scalars to S gives a basis whose vectors are the tensors of 1 with those differentials. They are therefore linearly independent.
-/
private theorem linearIndependent_one_tmul_D_X :
    LinearIndependent S fun i : ι =>
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i)) := by
  have hfun : (fun i : ι => (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))) =
      ⇑(Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis k ι)) := by
    funext i
    rw [Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  rw [hfun]
  exact (Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).linearIndependent

/- English proof (authored)
Induct on the polynomial. Constants have zero differential, and the differential of a sum is the sum of the differentials. When multiplying a polynomial by one variable, the product rule makes the differential a combination of the differential of the polynomial and the differential of that variable. This keeps it in the span of the variable differentials at every step.
-/
private theorem D_mem_span_range_D_X (K : Type*) [CommRing K] (σ : Type*)
    (f : MvPolynomial σ K) :
    KaehlerDifferential.D K (MvPolynomial σ K) f ∈
      Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X i)) := by
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]
    exact Submodule.zero_mem _
  · rename_i p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · rename_i p i hp
    rw [Derivation.leibniz]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.smul_mem _ _ hp)

/- English proof (authored)
The differentials of all polynomials generate the module of Kähler differentials. Each lies in the span of the variable differentials by the preceding result. Hence that smaller family also generates the whole module.
-/
private theorem span_range_D_X_eq_top (K : Type*) [CommRing K] (σ : Type*) :
    Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X i)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact D_mem_span_range_D_X K σ f

/- English proof (authored)
In the tensor product, the scalar action on the left factor multiplies that factor. Acting by a on the tensor with left factor 1 therefore replaces 1 by a.
-/
private theorem smul_one_tmul
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (a : A) (m : M) :
    a • ((1 : A) ⊗ₜ[R] m) = a ⊗ₜ[R] m := by
  have h2 : a • (1 : A) = a := by rw [smul_eq_mul, mul_one]
  have h1 : ((a • (1 : A)) ⊗ₜ[R] m : A ⊗[R] M) = a • ((1 : A) ⊗ₜ[R] m) := by
    rw [TensorProduct.smul_tmul']
  rw [h2] at h1
  exact h1.symm

/- English proof (authored)
Write any element of M as a finite linear combination of the given generators. Bilinearity expresses a pure tensor with that element as a sum of tensors with those generators, moving the coefficients from the base ring to the left factor by the balancing relation. Each such tensor is an A-multiple of the tensor with left factor 1. Since pure tensors generate the tensor product additively, the indicated tensors span over A.
-/
private theorem top_le_span_range_one_tmul
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M]
    (τ : Type*) (g : τ → M)
    (hs : Submodule.span R (Set.range g) = ⊤) :
    ⊤ ≤ Submodule.span A (Set.range fun i : τ => (1 : A) ⊗ₜ[R] g i) := by
  have key : ∀ m : M, ∀ a : A,
      a ⊗ₜ[R] m ∈ Submodule.span A (Set.range fun i : τ => (1 : A) ⊗ₜ[R] g i) := by
    intro m
    have hm : m ∈ Submodule.span R (Set.range g) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · rintro x ⟨i, rfl⟩ a
      rw [← smul_one_tmul R A M a (g i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro a
      rw [TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy a
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hx a) (hy a)
    · intro r x _ hx a
      have e : a ⊗ₜ[R] (r • x) = (r • a) ⊗ₜ[R] x := by
        rw [TensorProduct.smul_tmul]
      rw [e]
      exact hx (r • a)
  intro w _
  refine TensorProduct.induction_on w ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro a m
    exact key m a
  · intro u v hu hv
    exact Submodule.add_mem _ hu hv

omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
/- English proof (authored)
The variable differentials generate the module over the polynomial ring. Apply the scalar-extension spanning result to this generating family.
-/
private theorem top_le_span_one_tmul_D_X :
    ⊤ ≤ Submodule.span S (Set.range fun i : ι =>
        (1 : S) ⊗ₜ[MvPolynomial ι k]
          (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))) :=
  top_le_span_range_one_tmul (MvPolynomial ι k) S (KaehlerDifferential k (MvPolynomial ι k)) ι
    (fun i : ι => KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i))
    (span_range_D_X_eq_top k ι)

noncomputable def tensorKaehlerBasis :
    Module.Basis ι S (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) :=
  Module.Basis.mk (linearIndependent_one_tmul_D_X k ι S) (top_le_span_one_tmul_D_X k ι S)

@[simp]
/- English proof (authored)
The i-th vector of the scalar-extended basis is the tensor of 1 with the i-th variable differential. The map on differentials sends that vector to the differential of the image of the variable in S, which is the i-th coordinate.
-/
theorem tensorKaehlerBasis_mapBaseChange (i : ι) :
    KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S (tensorKaehlerBasis k ι S i) =
      KaehlerDifferential.D k S (coord k ι S i) := by
  have h : tensorKaehlerBasis k ι S i =
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i)) :=
    Module.Basis.mk_apply (linearIndependent_one_tmul_D_X k ι S) (top_le_span_one_tmul_D_X k ι S) i
  have h2 : coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl
  rw [h, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, h2]

/- English proof (authored)
The transitivity sequence for differentials has the scalar-extension map followed by the projection to the relative differentials over the polynomial ring. Exactness makes this composite zero. Surjectivity of the first map therefore makes the projection zero, so the relative differential of every element of S vanishes. These differentials generate the relative module. It is thus zero, which is the formal unramifiedness criterion.
-/
theorem formallyUnramified_of_mapBaseChange_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S)) :
    Algebra.FormallyUnramified (MvPolynomial ι k) S := by
  have hexact := KaehlerDifferential.exact_mapBaseChange_map k (MvPolynomial ι k) S
  have hD : ∀ s : S, KaehlerDifferential.D (MvPolynomial ι k) S s = 0 := by
    intro s
    obtain ⟨y, hy⟩ := h (KaehlerDifferential.D k S s)
    have h2 := hexact.apply_apply_eq_zero y
    rw [hy, KaehlerDifferential.map_D] at h2
    simpa using h2
  have key : ∀ x : KaehlerDifferential (MvPolynomial ι k) S, x = 0 := by
    intro x
    have hx : x ∈ Submodule.span S
        (Set.range (KaehlerDifferential.D (MvPolynomial ι k) S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨s, rfl⟩ := hy
        exact hD s
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul c a _ ha => rw [ha, smul_zero]
  exact Algebra.FormallyUnramified.mk ⟨fun a b => by rw [key a, key b]⟩

/- English proof (authored)
On each vector of the scalar-extended polynomial differential basis, the map gives the corresponding coordinate differential. By hypothesis these are the vectors of a basis of the target module. A linear map taking one basis to the other at every index is an isomorphism.
-/
theorem mapBaseChange_bijective_of_basis
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S) := by
  have h : (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S) =
      (((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)) :
        (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) →ₗ[S]
          KaehlerDifferential k S) := by
    refine (tensorKaehlerBasis k ι S).ext fun i => ?_
    rw [tensorKaehlerBasis_mapBaseChange]
    simp [hb i]
  have hx : ∀ x, KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S x =
      ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)) x := by
    intro x
    have h2 := congrArg
      (fun f : (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) →ₗ[S]
        KaehlerDifferential k S => f x) h
    simpa using h2
  constructor
  · intro x y hxy
    apply ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)).injective
    rw [← hx, ← hx, hxy]
  · intro y
    obtain ⟨x, hxe⟩ := ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)).surjective y
    exact ⟨x, (hx x).trans hxe⟩

/- English proof (authored)
Write P for the polynomial ring. The basis calculation makes the scalar-extension map on differentials an isomorphism. Its surjectivity gives formal unramifiedness over P. For formal smoothness, use the exact sequence for first cotangent homology of k → P → S. The connecting map from the first relative cotangent homology of S over P to the scalar-extended differentials has zero image, because its composite with the injective scalar-extension map is zero. Exactness therefore expresses every class in that relative homology as an image from the first cotangent homology over k. The latter vanishes by formal smoothness over k. Thus the relative homology vanishes, giving formal smoothness over P. Together the two properties give formal étaleness.
-/
theorem formallyEtale_of_basis [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Algebra.FormallyEtale (MvPolynomial ι k) S := by
  have hbij := mapBaseChange_bijective_of_basis k ι S b hb
  have hfu : Algebra.FormallyUnramified (MvPolynomial ι k) S :=
    formallyUnramified_of_mapBaseChange_surjective k ι S hbij.2
  have hh1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι k) S) := by
    have key : ∀ z : Algebra.H1Cotangent (MvPolynomial ι k) S, z = 0 := by
      intro z
      have hz : Algebra.H1Cotangent.δ k (MvPolynomial ι k) S z = 0 := by
        have h0 := (Algebra.H1Cotangent.exact_δ_mapBaseChange k (MvPolynomial ι k)
          S).apply_apply_eq_zero z
        refine hbij.1 ?_
        rw [h0, map_zero]
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ k (MvPolynomial ι k) S z).mp hz
      rw [← hw, Subsingleton.elim w 0, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · infer_instance

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

omit [IsScalarTower k (MvPolynomial ι k) S] in
/- English proof (authored)
A square coefficient matrix over a commutative ring with unit determinant is invertible. The coordinate differentials whose coefficients form that matrix are therefore a basis, in particular a linearly independent family.
-/
private theorem linearIndependent_D_coord_of_isUnit_det (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    LinearIndependent S fun i : ι => KaehlerDifferential.D k S (coord k ι S i) :=
  (b.is_basis_iff_det.mpr h).1

omit [IsScalarTower k (MvPolynomial ι k) S] in
/- English proof (authored)
A unit determinant makes the coefficient matrix of the coordinate differentials invertible. Its columns then generate all coefficient vectors in the fixed basis, so the coordinate differentials span the whole module.
-/
private theorem top_le_span_D_coord_of_isUnit_det (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    ⊤ ≤ Submodule.span S
        (Set.range fun i : ι => KaehlerDifferential.D k S (coord k ι S i)) := by
  have hb := b.is_basis_iff_det.mpr h
  have h2 : Submodule.span S
      (Set.range fun i : ι => KaehlerDifferential.D k S (coord k ι S i)) = ⊤ := hb.2
  exact h2.ge

noncomputable def coordBasis (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Module.Basis ι S (KaehlerDifferential k S) :=
  Module.Basis.mk (linearIndependent_D_coord_of_isUnit_det k ι S b h) (top_le_span_D_coord_of_isUnit_det k ι S b h)

omit [IsScalarTower k (MvPolynomial ι k) S] in
@[simp]
/- English proof (authored)
The basis is constructed from the independent spanning family of coordinate differentials. Its vector at i is by construction the differential of the i-th coordinate.
-/
theorem coordBasis_apply (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) (i : ι) :
    coordBasis k ι S b h i = KaehlerDifferential.D k S (coord k ι S i) :=
  Module.Basis.mk_apply (linearIndependent_D_coord_of_isUnit_det k ι S b h) (top_le_span_D_coord_of_isUnit_det k ι S b h) i

/- English proof (authored)
The unit determinant constructs a basis of coordinate differentials by the preceding results. The basis criterion for the formally smooth algebra S now gives formal étaleness over the coordinate polynomial ring.
-/
theorem formallyEtale_of_isUnit_det [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) S :=
  formallyEtale_of_basis k ι S (coordBasis k ι S b h) (coordBasis_apply k ι S b h)

end

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] [Algebra k S]
variable (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [Algebra.FormallyEtale S S']

/- English proof (authored)
For a formally étale map from S to S′, the differentials over k after extension of scalars identify with the differentials of S′ over k. Transport the scalar extension of the given basis under this isomorphism. Its vectors are the images of the original vectors, so they are linearly independent.
-/
private theorem linearIndependent_kaehlerMap_basis
    (b : Module.Basis ι S (KaehlerDifferential k S)) :
    LinearIndependent S' fun i : ι => KaehlerDifferential.map k k S S' (b i) := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k S S'
  have hfun : (fun i : ι => KaehlerDifferential.map k k S S' (b i)) =
      ⇑((Algebra.TensorProduct.basis S' b).map hbc.equiv) := by
    funext i
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, hbc.equiv_tmul, one_smul]
  rw [hfun]
  exact ((Algebra.TensorProduct.basis S' b).map hbc.equiv).linearIndependent

/- English proof (authored)
The relative differentials of S′ over S vanish by formal unramifiedness. Exactness of the transitivity sequence then makes the scalar-extension map onto the differentials of S′ over k surjective. The tensors of 1 with the original basis vectors span its source, and their images are the stated family. That family therefore spans the target.
-/
private theorem top_le_span_kaehlerMap_basis (b : Module.Basis ι S (KaehlerDifferential k S)) :
    ⊤ ≤ Submodule.span S'
        (Set.range fun i : ι => KaehlerDifferential.map k k S S' (b i)) := by
  have hsub : Subsingleton (KaehlerDifferential S S') :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hexact := KaehlerDifferential.exact_mapBaseChange_map k S S'
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange k S S') := by
    intro x
    obtain ⟨y, hy⟩ := (hexact x).mp (Subsingleton.elim _ _)
    exact ⟨y, hy⟩
  have hspan : ⊤ ≤ Submodule.span S' (Set.range fun i : ι => (1 : S') ⊗ₜ[S] b i) :=
    top_le_span_range_one_tmul S S' (KaehlerDifferential k S) ι (⇑b) b.span_eq
  have hle : Submodule.span S' (Set.range fun i : ι => (1 : S') ⊗ₜ[S] b i) ≤
      Submodule.comap (KaehlerDifferential.mapBaseChange k S S')
        (Submodule.span S'
          (Set.range fun i : ι => KaehlerDifferential.map k k S S' (b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : KaehlerDifferential.mapBaseChange k S S' ((1 : S') ⊗ₜ[S] b i) ∈
        Submodule.span S'
          (Set.range fun j : ι => KaehlerDifferential.map k k S S' (b j)) := by
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact h1
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hspan Submodule.mem_top)

noncomputable def inducedBasis (b : Module.Basis ι S (KaehlerDifferential k S)) :
    Module.Basis ι S' (KaehlerDifferential k S') :=
  Module.Basis.mk (linearIndependent_kaehlerMap_basis k ι S S' b) (top_le_span_kaehlerMap_basis k ι S S' b)

@[simp]
/- English proof (authored)
The induced basis is built from the independent spanning family of images of the original basis vectors. Its i-th vector is the image of the i-th original basis vector.
-/
theorem inducedBasis_apply (b : Module.Basis ι S (KaehlerDifferential k S)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.map k k S S' (b i) :=
  Module.Basis.mk_apply (linearIndependent_kaehlerMap_basis k ι S S' b)
    (top_le_span_kaehlerMap_basis k ι S S' b) i

/- English proof (authored)
The induced basis vector is the image of the original one. By hypothesis the original vector is the differential of the chosen element. Naturality sends that differential to the differential of the element's image in S′.
-/
theorem inducedBasis_apply_D (b : Module.Basis ι S (KaehlerDifferential k S)) (x : ι → S)
    (hx : ∀ i : ι, b i = KaehlerDifferential.D k S (x i)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.D k S' (algebraMap S S' (x i)) := by
  rw [inducedBasis_apply, hx i, KaehlerDifferential.map_D]

end

end JacobianCriterion
end FunctorialResolution.EmbeddedResolution
