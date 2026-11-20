import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.BaseIntPf

/- English proof (translation)
Use `letI := φ.hom.toAlgebra`. Establish `: Module.Flat A B` using `hf`. Establish `: IsLocalHom (algebraMap A B)` using `‹IsLocalHom φ.hom›`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)` as an intermediate fact. Conclude with `⟨FaithfulSMul.algebraMap_injective A B, hs⟩`.
-/
theorem bij_of_flat_surj {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B] (φ : A ⟶ B)
    [IsLocalHom φ.hom] (hf : φ.hom.Flat) (hs : Function.Surjective φ.hom) : Function.Bijective φ.hom := by
  letI := φ.hom.toAlgebra
  have : Module.Flat A B := hf
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom φ.hom›
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact ⟨FaithfulSMul.algebraMap_injective A B, hs⟩

/- English proof (translation)
Establish `: ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)`. Introduce `x`. Establish `hb` using `bij_of_flat_surj (f.stalkMap x) (Flat.stalkMap f x) (f.stalkMap_surjective x)`. Conclude with `isReduced_of_injective (RingEquiv.ofBijective _ hb).symm (RingEquiv.injective _)`. Conclude with `isReduced_of_isReduced_stalk X`.
-/
theorem reduced_of_flat_preimm {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    have hb := bij_of_flat_surj (f.stalkMap x) (Flat.stalkMap f x) (f.stalkMap_surjective x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ hb).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

/- English proof (translation)
Rewrite using `[specializes_iff_mem_closure]`. Establish `h1 : Set.range c.base ⊆ closure {c.base (genericPoint Z)}`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `specializes_iff_mem_closure.mp (((genericPoint_spec Z).specializes (Set.mem_univ z)).map c.continuous)`. Establish `h2` using `closure_minimal h1 isClosed_closure`.

Rewrite `h2` using `[c.denseRange.closure_range]`. Conclude with `h2 (Set.mem_univ x)`.
-/
theorem gen_spec {Z S : Scheme.{0}} [IrreducibleSpace Z] [IrreducibleSpace S] (c : Z ⟶ S) [IsDominant c] (x : S) :
    c.base (genericPoint Z) ⤳ x := by
  rw [specializes_iff_mem_closure]
  have h1 : Set.range c.base ⊆ closure {c.base (genericPoint Z)} := by
    rintro _ ⟨z, rfl⟩
    exact specializes_iff_mem_closure.mp (((genericPoint_spec Z).specializes (Set.mem_univ z)).map c.continuous)
  have h2 := closure_minimal h1 isClosed_closure
  rw [c.denseRange.closure_range] at h2
  exact h2 (Set.mem_univ x)

/- English proof (translation)
Introduce `Z S c _ _ _ hZ hS x`. Use `hZ.1` as an intermediate fact. Use `hS.1` as an intermediate fact. Establish `: Flat (S.fromSpecStalk x)` using `GlobalTheory.GenericExt.flat_fromSpecStalk S x`. Establish `: IsReduced (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})` using `reduced_of_flat_preimm (pullback.fst c (S.fromSpecStalk x))`.

Establish `hT : IsIrreducible (Set.range (pullback.fst c (S.fromSpecStalk x)).base)`. Establish `hη : genericPoint Z ∈ Set.range (pullback.fst c (S.fromSpecStalk x)).base`. Rewrite using `[Scheme.Pullback.range_fst, Scheme.range_fromSpecStalk]`. Conclude with `gen_spec c x`. Rewrite using `[← isIrreducible_iff_closure]`.

Establish `: closure (Set.range (pullback.fst c (S.fromSpecStalk x)).base) = Set.univ`. Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises. Rewrite using `[← (genericPoint_spec Z).def]`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr hη)`. Rewrite using `[this]`.

Conclude with `IrreducibleSpace.isIrreducible_univ Z`. Establish `: IrreducibleSpace (Set.range (pullback.fst c (S.fromSpecStalk x)).base)` using `Subtype.irreducibleSpace hT`. Establish `: IrreducibleSpace (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})` using `((pullback.fst c (S.fromSpecStalk x)).isEmbedding.toHomeomorph).irreducibleSpace_iff.mpr inferInstance`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced _`.
-/
theorem BaseInt_of : LateralTheory.E.BaseAICPf.BaseInt := by
  intro Z S c _ _ _ hZ hS x
  have := hZ.1; have := hS.1
  have : Flat (S.fromSpecStalk x) := GlobalTheory.GenericExt.flat_fromSpecStalk S x
  have : IsReduced (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) := reduced_of_flat_preimm (pullback.fst c (S.fromSpecStalk x))
  have hT : IsIrreducible (Set.range (pullback.fst c (S.fromSpecStalk x)).base) := by
    have hη : genericPoint Z ∈ Set.range (pullback.fst c (S.fromSpecStalk x)).base := by
      rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecStalk]
      exact gen_spec c x
    rw [← isIrreducible_iff_closure]
    have : closure (Set.range (pullback.fst c (S.fromSpecStalk x)).base) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec Z).def]
      exact closure_mono (Set.singleton_subset_iff.mpr hη)
    rw [this]; exact IrreducibleSpace.isIrreducible_univ Z
  have : IrreducibleSpace (Set.range (pullback.fst c (S.fromSpecStalk x)).base) := Subtype.irreducibleSpace hT
  have : IrreducibleSpace (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    ((pullback.fst c (S.fromSpecStalk x)).isEmbedding.toHomeomorph).irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.E.BaseIntPf
