import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Use `ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int` as an intermediate fact. Establish `: Module.Finite ℤ K` using `finite_of_finite_type_of_isJacobsonRing ℤ _`. Take `⟨p, hp⟩` from `CharP.exists K`. Establish `hp0 : p ≠ 0`. Introduce and unpack `rfl`.

Use `CharP.charP_to_charZero K` as an intermediate fact. Conclude with `Int.not_isField (isField_of_isIntegral_of_isField (algebraMap ℤ K).injective_int (Field.toIsField _))`. Establish `: Fact p.Prime` using `⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩`. Set `` to `ZMod.algebra K p`. Establish `: Module.Finite (ZMod p) K` using `Module.Finite.of_restrictScalars_finite ℤ _ _`.

Conclude with `Module.finite_of_finite (ZMod p)`.
-/
theorem finite_field_of_finiteType_int (K : Type*) [Field K] [Algebra.FiniteType ℤ K] :
    Finite K := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ _
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := CharP.charP_to_charZero K
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (algebraMap ℤ K).injective_int (Field.toIsField _))
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  let := ZMod.algebra K p
  have : Module.Finite (ZMod p) K := Module.Finite.of_restrictScalars_finite ℤ _ _
  exact Module.finite_of_finite (ZMod p)

/- English proof (translation)
Use `ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int` as an intermediate fact. Conclude with `LocallyOfFiniteType.jacobsonSpace π`.
-/
theorem jacobsonSpace_of_locallyOfFiniteType_int {X : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] : JacobsonSpace X := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  exact LocallyOfFiniteType.jacobsonSpace π

/- English proof (translation)
Use `isClosed_singleton_iff_isClosedImmersion.mp hx` as an intermediate fact. Establish `h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ π)` using `inferInstance`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (X.fromSpecResidueField x ≫ π)`. Rewrite `h` using `[← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `e : φ.hom = algebraMap ℤ (X.residueField x)` using `RingHom.ext_int _ _`.

Establish `h' : (algebraMap ℤ (X.residueField x)).FiniteType` using `e ▸ h`. Establish `: Algebra.FiniteType ℤ (X.residueField x)` using `RingHom.finiteType_algebraMap.mp h'`. Conclude with `finite_field_of_finiteType_int _`.
-/
theorem finite_residueField_of_isClosed_of_locallyOfFiniteType_int {X : Scheme.{0}}
    (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ (X.residueField x) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ (X.residueField x)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ (X.residueField x) := RingHom.finiteType_algebraMap.mp h'
  exact finite_field_of_finiteType_int _

section Top

variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]

/- English proof (translation)
Introduce `y hy`. Assume the negation of the conclusion as `hyV`. Take `⟨x, ⟨hxU, hxV⟩, hx⟩` from `nonempty_inter_closedPoints (Z := U ∩ Vᶜ) ⟨y, hy, hyV⟩ (hU.isLocallyClosed.inter hV.isClosed_compl.isLocallyClosed)`. Conclude with `hxV (h x hx hxU)`.
-/
theorem subset_of_isOpen_of_closedPoints {U V : Set T} (hU : IsOpen U) (hV : IsOpen V)
    (h : ∀ x, IsClosed ({x} : Set T) → x ∈ U → x ∈ V) : U ⊆ V := by
  intro y hy
  by_contra hyV
  obtain ⟨x, ⟨hxU, hxV⟩, hx⟩ := nonempty_inter_closedPoints (Z := U ∩ Vᶜ) ⟨y, hy, hyV⟩
    (hU.isLocallyClosed.inter hV.isClosed_compl.isLocallyClosed)
  exact hxV (h x hx hxU)

/- English proof (translation)
Establish `hO : IsOpen (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1)` using `hW.inter (isOpen_iInter_of_finite fun i => hU i.1)`. Take `⟨x, ⟨hxc, hxW, hxU⟩, hx⟩` from `nonempty_inter_closedPoints (Z := closure {ξ} ∩ (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1)) ⟨ξ, subset_closure rfl, hξ, Set.mem_iInter.mpr fun i => i.2⟩ (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)`. Establish `hs : ξ ⤳ x` using `specializes_iff_mem_closure.mpr hxc`. Conclude with `⟨x, hx, hs, hxW, fun i => ⟨fun h => hs.mem_open (hU i) h, fun h => Set.mem_iInter.mp hxU ⟨i, h⟩⟩⟩`.
-/
theorem exists_isClosed_specializes_mem_iff (ξ : T) {ι : Type*} [Finite ι] (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) {W : Set T} (hW : IsOpen W) (hξ : ξ ∈ W) :
    ∃ x : T, IsClosed ({x} : Set T) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i := by
  have hO : IsOpen (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1) :=
    hW.inter (isOpen_iInter_of_finite fun i => hU i.1)
  obtain ⟨x, ⟨hxc, hxW, hxU⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := closure {ξ} ∩ (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1))
    ⟨ξ, subset_closure rfl, hξ, Set.mem_iInter.mpr fun i => i.2⟩
    (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hx, hs, hxW, fun i =>
    ⟨fun h => hs.mem_open (hU i) h, fun h => Set.mem_iInter.mp hxU ⟨i, h⟩⟩⟩

/- English proof (translation)
Establish `hc : (⋃ i, closure (S i)) = Set.univ`. Rewrite using `[← Set.univ_subset_iff, ← closure_closedPoints (X := T), (isClosed_iUnion_of_finite fun i => isClosed_closure).closure_subset_iff]`. Introduce `x hx`. Take `⟨i, hi⟩` from `h x hx`. Conclude with `Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩`.

Use `Fintype.ofFinite ι` as an intermediate fact. Take `⟨Z, hZ, hZ'⟩` from `isIrreducible_iff_sUnion_isClosed.mp (IrreducibleSpace.isIrreducible_univ T) (Finset.univ.image fun i => closure (S i)) (by`. Introduce `z hz`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hz`. Conclude with `isClosed_closure)`.

Use the proof step `(by`. Introduce `x _`. Take `⟨i, hi⟩` from `Set.mem_iUnion.mp (hc ▸ Set.mem_univ x : x ∈ ⋃ i, closure (S i))`. Conclude with `⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hi⟩)`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hZ`.

Conclude with `⟨i, fun x => hZ' (Set.mem_univ x)⟩`.
-/
theorem exists_dense_of_closedPoints_cover [IrreducibleSpace T] {ι : Type*} [Finite ι]
    (S : ι → Set T) (h : ∀ x, IsClosed ({x} : Set T) → ∃ i, x ∈ S i) : ∃ i, Dense (S i) := by
  have hc : (⋃ i, closure (S i)) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints (X := T),
      (isClosed_iUnion_of_finite fun i => isClosed_closure).closure_subset_iff]
    intro x hx
    obtain ⟨i, hi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
  classical
  have := Fintype.ofFinite ι
  obtain ⟨Z, hZ, hZ'⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ T) (Finset.univ.image fun i => closure (S i))
    (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact isClosed_closure)
    (by
      intro x _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc ▸ Set.mem_univ x : x ∈ ⋃ i, closure (S i))
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
  exact ⟨i, fun x => hZ' (Set.mem_univ x)⟩

end Top

/- English proof (translation)
Introduce `X π _`. Establish `hJ` using `jacobsonSpace_of_locallyOfFiniteType_int π`. Use `⟨hJ, finite_residueField_of_isClosed_of_locallyOfFiniteType_int π, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `U V h`. Conclude with `TopologicalSpace.Opens.ext (subset_antisymm (subset_of_isOpen_of_closedPoints U.isOpen V.isOpen fun x hx => (h x hx).1) (subset_of_isOpen_of_closedPoints V.isOpen U.isOpen fun x hx => (h x hx).2))`.

Introduce `ξ ι _ U W hξ`. Conclude with `exists_isClosed_specializes_mem_iff ξ (fun i => (U i : Set X)) (fun i => (U i).isOpen) W.isOpen hξ`. Introduce `ι _ Sg _ h`. Conclude with `exists_dense_of_closedPoints_cover Sg h`.
-/
theorem jacobson_tools_of_locallyOfFiniteType_int :
    ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧
      (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
      (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧
      (∀ (ξ : X) (ι : Type) [Finite ι] (U : ι → X.Opens) (W : X.Opens), ξ ∈ W →
        ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧
      (∀ (ι : Type) [Finite ι] (Sg : ι → Set X), IrreducibleSpace X →
        (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) := by
  intro X π _
  have hJ := jacobsonSpace_of_locallyOfFiniteType_int π
  refine ⟨hJ, finite_residueField_of_isClosed_of_locallyOfFiniteType_int π, ?_, ?_, ?_⟩
  · intro U V h
    exact TopologicalSpace.Opens.ext (subset_antisymm
      (subset_of_isOpen_of_closedPoints U.isOpen V.isOpen fun x hx => (h x hx).1)
      (subset_of_isOpen_of_closedPoints V.isOpen U.isOpen fun x hx => (h x hx).2))
  · intro ξ ι _ U W hξ
    exact exists_isClosed_specializes_mem_iff ξ (fun i => (U i : Set X)) (fun i => (U i).isOpen)
      W.isOpen hξ
  · intro ι _ Sg _ h
    exact exists_dense_of_closedPoints_cover Sg h

end GlobalTheory
