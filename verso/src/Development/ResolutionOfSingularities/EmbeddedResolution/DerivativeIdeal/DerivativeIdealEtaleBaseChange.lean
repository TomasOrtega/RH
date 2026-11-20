import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private def derivationCompAlgebraMap (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k T T) :
    Derivation k S T :=
  Derivation.mk' (D.toLinearMap.comp (IsScalarTower.toAlgHom k S T).toLinearMap) (by
    intro a b
    show D (algebraMap S T (a * b)) = a • D (algebraMap S T b) + b • D (algebraMap S T a)
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def])

/- English proof (authored)
The restricted derivation is constructed by precomposing the given derivation with the structure map from S to T. Evaluating this composite on s gives the asserted value.
-/
private theorem derivation_comp_algebraMap_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k T T) (s : S) :
    derivationCompAlgebraMap k S T D s = D (algebraMap S T s) := rfl

private def algebraMapCompDerivation (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k S S) :
    Derivation k S T :=
  Derivation.mk' ((IsScalarTower.toAlgHom k S T).toLinearMap.comp D.toLinearMap) (by
    intro a b
    show algebraMap S T (D (a * b)) = a • algebraMap S T (D b) + b • algebraMap S T (D a)
    rw [D.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
      Algebra.smul_def])

/- English proof (authored)
The derivation with values in T is constructed by applying the structure map to every value of the original derivation. Its value at s is the image of the original value at s.
-/
private theorem algebraMap_comp_derivation_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl

/- English proof (authored)
Each derivation factors through a linear map on the differential module. The coordinate differentials form a basis by formal étaleness. The hypothesis gives equality of the two linear maps on every basis vector, hence on the whole module. Composing with the universal differential gives equality of the derivations.
-/
theorem derivation_ext_of_coord (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
    [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (M : Type*) [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (D₁ D₂ : Derivation k S M)
    (h : ∀ i : ι, D₁ (coord k ι S i) = D₂ (coord k ι S i)) : D₁ = D₂ := by
  have key : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    refine (basisKaehler k ι S).ext ?_
    intro i
    rw [basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  refine Derivation.ext fun x => ?_
  rw [← Derivation.liftKaehlerDifferential_comp_D D₁ x,
    ← Derivation.liftKaehlerDifferential_comp_D D₂ x, key]

/- English proof (authored)
Restrict the partial derivation for the extra coordinate j to S. On each coordinate of S it vanishes, since that coordinate maps to a coordinate in the first block. Derivations on S are determined by the coordinate values, so the restricted derivation is zero.
-/
theorem partialDeriv_inr_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (j : κ) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inr j) (algebraMap S T s) = 0 := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inr j)) = 0 := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro i
    rw [derivation_comp_algebraMap_apply, hcoord i,
      partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inr j) (Sum.inl i) (by simp)]
    have h0 : ((0 : Derivation k S T)) (coord k ι S i) = 0 := rfl
    rw [h0]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply] at h2
  have h0 : ((0 : Derivation k S T)) s = 0 := rfl
  rw [h0] at h2
  exact h2

/- English proof (authored)
Compare the partial derivation for the old coordinate in T restricted to S with the corresponding partial derivation in S followed by the structure map on its values. Both take one on the indicated coordinate and zero on all the other coordinates of S. Since coordinate values determine a derivation, these maps agree on every s.
-/
theorem partialDeriv_inl_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i))
      = algebraMapCompDerivation k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]
    by_cases hij : i = j
    · subst hij
      rw [partialDeriv_coord_self, partialDeriv_coord_self, map_one]
    · rw [partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij),
        partialDeriv_coord_of_ne k ι S i j hij, map_zero]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply] at h2
  exact h2

/- English proof (authored)
The old partial derivations span all derivations of S. After applying the structure map, each of their values on J is a value of the corresponding partial derivation in T on the extended ideal. This gives containment of the extended derivative ideal in the new derivative ideal. Conversely the partial derivations in T span all derivations there. The partials for old coordinates give images of original derivatives on elements from J, and partials for extra coordinates give zero on those images. Thus all derivatives of the generators of the extended J lie in the extended derivative ideal. The Leibniz rule extends this to the ideal they generate, because that ideal is itself contained in the extended derivative ideal. This gives the other containment.
-/
theorem map_derivIdeal_sum (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (J : Ideal S) :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)
    | zero =>
        have h0 : ((0 : Derivation k S S)) y = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) y = a y + b y := rfl
        rw [h0, map_add]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) y = c * a y := rfl
        rw [h0, map_mul]
        exact Ideal.mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
            exact Ideal.mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            rw [partialDeriv_inr_algebraMap k ι κ S T hcoord j y]
            exact Submodule.zero_mem _
    | zero =>
        have h0 : ((0 : Derivation k T T)) (algebraMap S T y) = 0 := rfl
        rw [h0]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) (algebraMap S T y)
            = a (algebraMap S T y) + b (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
    refine ⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩
    intro D y hy
    exact Ideal.mem_comap.mpr (key1 D y hy)
  · rw [derivIdeal_le_iff]
    refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
    intro D' z hz
    have hspan : Ideal.map (algebraMap S T) J
        = Ideal.span ((algebraMap S T) '' (J : Set S)) := by
      rw [← Ideal.map_span, Ideal.span_eq]
    rw [hspan] at hz
    refine derivation_apply_mem_of_mem_span D' ?_ ?_ hz
    · rw [← hspan]
      exact Ideal.map_mono (le_derivIdeal k J)
    · rintro g ⟨y, hy, rfl⟩
      exact key2 D' y hy

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
