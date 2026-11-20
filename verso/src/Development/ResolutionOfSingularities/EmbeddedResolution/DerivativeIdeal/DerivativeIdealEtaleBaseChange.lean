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

/- English proof (translation)
Both sides reduce to the same expression.
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

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem algebraMap_comp_derivation_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl

/- English proof (translation)
Establish `key : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential`. Use `(basisKaehler k ι S).ext ?_` and prove the remaining obligations. Introduce `i`. Rewrite using `[basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]`. Conclude with `h i`.

Use `Derivation.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[← Derivation.liftKaehlerDifferential_comp_D D₁ x, ← Derivation.liftKaehlerDifferential_comp_D D₂ x, key]`.
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

/- English proof (translation)
Establish `key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inr j)) = 0`. Use `derivation_ext_of_coord k ι S T _ _ ?_` and prove the remaining obligations. Introduce `i`. Rewrite using `[derivation_comp_algebraMap_apply, hcoord i, partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inr j) (Sum.inl i) (by simp)]`. Establish `h0 : ((0 : Derivation k S T)) (coord k ι S i) = 0` using `rfl`.

Rewrite using `[h0]`. Establish `h2` using `DFunLike.congr_fun key s`. Rewrite `h2` using `[derivation_comp_algebraMap_apply]`. Establish `h0 : ((0 : Derivation k S T)) s = 0` using `rfl`. Rewrite `h2` using `[h0]`.

Conclude with `h2`.
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

/- English proof (translation)
Establish `key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i)) = algebraMapCompDerivation k S T (partialDeriv k ι S i)`. Use `derivation_ext_of_coord k ι S T _ _ ?_` and prove the remaining obligations. Introduce `j`. Rewrite using `[derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[partialDeriv_coord_self, partialDeriv_coord_self, map_one]`. Rewrite using `[partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij), partialDeriv_coord_of_ne k ι S i j hij, map_zero]`. Establish `h2` using `DFunLike.congr_fun key s`. Rewrite `h2` using `[derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply]`.

Conclude with `h2`.
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

/- English proof (translation)
Establish `key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J → algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J)`. Introduce `D y hy`. Establish `hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S))`. Rewrite using `[span_range_partialDeriv]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hsp using Submodule.span_induction with`. Consider the case `mem D hD`. Take `⟨i, rfl⟩` from `hD`. Rewrite using `[← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]`. Conclude with `derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)`.

Consider the case `zero`. Establish `h0 : ((0 : Derivation k S S)) y = 0` using `rfl`. Rewrite using `[h0, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb`.

Establish `h0 : (a + b) y = a y + b y` using `rfl`. Rewrite using `[h0, map_add]`. Conclude with `Ideal.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Establish `h0 : (c • a) y = c * a y` using `rfl`.

Rewrite using `[h0, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ ha`. Establish `key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J → D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J)`. Introduce `D' y hy`. Establish `hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T))`.

Rewrite using `[span_range_partialDeriv]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hsp using Submodule.span_induction with`. Consider the case `mem D hD`. Take `⟨x, rfl⟩` from `hD`.

Consider the cases of `x with`. Consider the case `inl i`. Rewrite using `[partialDeriv_inl_algebraMap k ι κ S T hcoord i y]`. Conclude with `Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)`. Consider the case `inr j`.

Rewrite using `[partialDeriv_inr_algebraMap k ι κ S T hcoord j y]`. Conclude with `Submodule.zero_mem _`. Consider the case `zero`. Establish `h0 : ((0 : Derivation k T T)) (algebraMap S T y) = 0` using `rfl`. Rewrite using `[h0]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `h0 : (a + b) (algebraMap S T y) = a (algebraMap S T y) + b (algebraMap S T y)` using `rfl`. Rewrite using `[h0]`. Conclude with `Ideal.add_mem _ ha hb`.

Consider the case `smul c a _ ha`. Establish `h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y)` using `rfl`. Rewrite using `[h0]`. Conclude with `Ideal.mul_mem_left _ _ ha`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap, derivIdeal_le_iff]`. Use `⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩` and prove the remaining obligations. Introduce `D y hy`. Conclude with `Ideal.mem_comap.mpr (key1 D y hy)`. Rewrite using `[derivIdeal_le_iff]`.

Use `⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩` and prove the remaining obligations. Introduce `D' z hz`. Establish `hspan : Ideal.map (algebraMap S T) J = Ideal.span ((algebraMap S T) '' (J : Set S))`. Rewrite using `[← Ideal.map_span, Ideal.span_eq]`. Rewrite `hz` using `[hspan]`.

Use `derivation_apply_mem_of_mem_span D' ?_ ?_ hz` and prove the remaining obligations. Rewrite using `[← hspan]`. Conclude with `Ideal.map_mono (le_derivIdeal k J)`. Introduce and unpack `g ⟨y, hy, rfl⟩`. Conclude with `key2 D' y hy`.
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
