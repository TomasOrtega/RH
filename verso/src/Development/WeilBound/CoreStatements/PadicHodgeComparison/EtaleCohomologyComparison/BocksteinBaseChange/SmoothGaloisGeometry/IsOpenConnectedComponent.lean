import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ExistsGalMapApply

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace

namespace CrystallineSemistableComparison.GeoC

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isOpen_connectedComponent {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx
      apply hZ'
      rw [connectedComponent_eq hyx]
      exact hZ.1.isConnected.subset_connectedComponent hy
  rw [← isClosed_compl_iff, h]
  refine Set.Finite.isClosed_biUnion
    (NoetherianSpace.finite_irreducibleComponents.subset fun Z hZ => hZ.1) fun Z hZ => ?_
  exact isClosed_of_mem_irreducibleComponents Z hZ.1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem image_connectedComponent {X : Type*} [TopologicalSpace X] (h : X ≃ₜ X) (x : X) :
    h '' connectedComponent x = connectedComponent (h x) := by
  refine (h.continuous.image_connectedComponent_subset x).antisymm ?_
  intro y hy
  refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
  have := h.symm.continuous.image_connectedComponent_subset (h x) ⟨y, hy, rfl⟩
  rwa [h.symm_apply_apply] at this

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem galMap_comp_inv (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p σ⁻¹ = 𝟙 _ := by
  rw [← GlobalTheory.EtC.galMap_mul, mul_inv_cancel, GlobalTheory.EtC.galMap_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem galMap_inv_comp (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.galMap Ω p σ⁻¹ ≫ GlobalTheory.Et.galMap Ω p σ = 𝟙 _ := by
  rw [← GlobalTheory.EtC.galMap_mul, inv_mul_cancel, GlobalTheory.EtC.galMap_one]

instance (σ : Ω ≃ₐ[k] Ω) : IsIso (GlobalTheory.Et.galMap Ω p σ) :=
  ⟨⟨GlobalTheory.Et.galMap Ω p σ⁻¹, galMap_comp_inv p σ, galMap_inv_comp p σ⟩⟩

def galHomeo (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.geom Ω p ≃ₜ GlobalTheory.Et.geom Ω p where
  toFun := GlobalTheory.Et.galMap Ω p σ
  invFun := GlobalTheory.Et.galMap Ω p σ⁻¹
  left_inv x := by rw [← Scheme.Hom.comp_apply, galMap_comp_inv]; rfl
  right_inv x := by rw [← Scheme.Hom.comp_apply, galMap_inv_comp]; rfl
  continuous_toFun := (GlobalTheory.Et.galMap Ω p σ).continuous
  continuous_invFun := (GlobalTheory.Et.galMap Ω p σ⁻¹).continuous

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem galMap_mul_apply (σ τ : Ω ≃ₐ[k] Ω) (y : GlobalTheory.Et.geom Ω p) :
    GlobalTheory.Et.galMap Ω p (σ * τ) y = GlobalTheory.Et.galMap Ω p τ (GlobalTheory.Et.galMap Ω p σ y) := by
  rw [GlobalTheory.EtC.galMap_mul, Scheme.Hom.comp_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem galMap_one_apply (y : GlobalTheory.Et.geom Ω p) : GlobalTheory.Et.galMap Ω p 1 y = y := by
  rw [GlobalTheory.EtC.galMap_one]; rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails.

Supply the required witnesses or components. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_components [IsGalois k Ω] [Smooth p] [ConnectedSpace X] [CompactSpace X] :
    ∃ (r : ℕ) (U : Fin r → (GlobalTheory.Et.geom Ω p).Opens),
      (∀ s, IsIntegral (U s).toScheme) ∧ (∀ y, ∃ s, y ∈ U s) ∧
      (∀ s s', s ≠ s' → Disjoint (U s : Set (GlobalTheory.Et.geom Ω p)) (U s')) ∧
      (∀ (σ : Ω ≃ₐ[k] Ω) s, ∃ s', GlobalTheory.Et.galMap Ω p σ '' (U s : Set (GlobalTheory.Et.geom Ω p)) = U s') ∧
      (∀ s s', ∃ σ : Ω ≃ₐ[k] Ω, GlobalTheory.Et.galMap Ω p σ '' (U s : Set (GlobalTheory.Et.geom Ω p)) = U s') := by
  set ψ := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hψ
  set Y := GlobalTheory.Et.geom Ω p
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  have : CompactSpace Y := by dsimp only [Y, GlobalTheory.Et.geom]; infer_instance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p ψ)
  have : IsNoetherian Y := {}
  have hopen : ∀ y : Y, IsOpen (connectedComponent y) := isOpen_connectedComponent
  have : DiscreteTopology (_root_.ConnectedComponents Y) := ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents Y) := finite_of_compact_of_discrete
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (_root_.ConnectedComponents Y)
  let C : Fin r → Set Y := fun s => ConnectedComponents.mk ⁻¹' {e.symm s}
  have hC : ∀ y : Y, C (e (ConnectedComponents.mk y)) = connectedComponent y := fun y => by
    simp only [C, Equiv.symm_apply_apply, connectedComponents_preimage_singleton]
  have hCrep : ∀ s, ∃ y : Y, C s = connectedComponent y := fun s => by
    obtain ⟨y, hy⟩ := ConnectedComponents.surjective_coe (e.symm s)
    exact ⟨y, by rw [← hC y, hy, Equiv.apply_symm_apply]⟩
  have hCopen : ∀ s, IsOpen (C s) := fun s => by
    obtain ⟨y, hy⟩ := hCrep s; rw [hy]; exact hopen y
  let U : Fin r → Y.Opens := fun s => ⟨C s, hCopen s⟩
  have hg : ∀ (σ : Ω ≃ₐ[k] Ω) (y : Y),
      GlobalTheory.Et.galMap Ω p σ '' connectedComponent y = connectedComponent (GlobalTheory.Et.galMap Ω p σ y) :=
    fun σ y => image_connectedComponent (galHomeo p σ) y
  refine ⟨r, U, fun s => ?_, fun y => ⟨e (ConnectedComponents.mk y), ?_⟩, fun s s' hss' => ?_,
    fun σ s => ?_, fun s s' => ?_⟩
  · obtain ⟨y, hy⟩ := hCrep s
    have : ConnectedSpace (U s).toScheme := by
      change ConnectedSpace (C s)
      rw [hy]
      exact isConnected_iff_connectedSpace.1 isConnected_connectedComponent
    exact GlobalTheory.isIntegral_of_smooth_field ((U s).ι ≫ pullback.snd p ψ)
  · change y ∈ C _
    rw [hC]; exact mem_connectedComponent
  · change Disjoint (C s) (C s')
    refine Set.disjoint_left.2 fun y h1 h2 => hss' ?_
    simp only [C, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact e.symm.injective (h1.symm.trans h2)
  · obtain ⟨y, hy⟩ := hCrep s
    refine ⟨e (ConnectedComponents.mk (GlobalTheory.Et.galMap Ω p σ y)), ?_⟩
    change _ '' C s = C _
    rw [hy, hC, hg]
  · obtain ⟨y₀, hy₀⟩ := hCrep s
    obtain ⟨y₁, hy₁⟩ := hCrep s'

    let Z : Set Y := {y | ∃ σ : Ω ≃ₐ[k] Ω, y ∈ connectedComponent (GlobalTheory.Et.galMap Ω p σ y₀)}
    have hZstab : ∀ (τ : Ω ≃ₐ[k] Ω) y, y ∈ Z → GlobalTheory.Et.galMap Ω p τ y ∈ Z := by
      rintro τ y ⟨σ, hσ⟩
      refine ⟨σ * τ, ?_⟩
      rw [galMap_mul_apply, ← hg]
      exact ⟨y, hσ, rfl⟩
    have hZo : IsOpen Z := by
      have : Z = ⋃ σ : Ω ≃ₐ[k] Ω, connectedComponent (GlobalTheory.Et.galMap Ω p σ y₀) := by
        ext y; simp [Z]
      rw [this]; exact isOpen_iUnion fun σ => hopen _
    have hZc : IsOpen Zᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      refine ⟨connectedComponent y, fun w hw hwZ => hy ?_, hopen y, mem_connectedComponent⟩
      obtain ⟨σ, hσ⟩ := hwZ
      refine ⟨σ, ?_⟩
      rw [connectedComponent_eq hσ, ← connectedComponent_eq hw]
      exact mem_connectedComponent
    have hy₀Z : y₀ ∈ Z := ⟨1, by rw [galMap_one_apply]; exact mem_connectedComponent⟩
    have hZ : Z = Set.univ := by
      by_contra hne
      obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem Z).1 hne
      have : Algebra.IsIntegral k Ω := inferInstance
      have : IsIntegralHom ψ := IsIntegralHom.SpecMap_iff.2 (fun x => Algebra.IsIntegral.isIntegral x)
      have : Surjective ψ := ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
      have hcl := (pullback.fst p ψ).isClosedMap
      have hsurj := (pullback.fst p ψ).surjective
      set A := pullback.fst p ψ '' Z
      set B := pullback.fst p ψ '' Zᶜ
      have hAB : A = Bᶜ := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
          obtain ⟨σ, hσ⟩ := GeoB.exists_galMap_apply p a c hca.symm
          exact hc (hσ ▸ hZstab σ a ha)
        · intro hx
          obtain ⟨a, rfl⟩ := hsurj x
          by_cases ha : a ∈ Z
          · exact ⟨a, ha, rfl⟩
          · exact absurd ⟨a, ha, rfl⟩ hx
      have hAcl : IsClopen A :=
        ⟨hcl _ (isOpen_compl_iff.1 hZc), hAB ▸ (hcl _ hZo.isClosed_compl).isOpen_compl⟩
      rcases isClopen_iff.1 hAcl with h | h
      · exact (Set.eq_empty_iff_forall_notMem.1 h) _ ⟨y₀, hy₀Z, rfl⟩
      · have : pullback.fst p ψ b ∈ A := h ▸ Set.mem_univ _
        rw [hAB] at this
        exact this ⟨b, hb, rfl⟩
    have : y₁ ∈ Z := hZ ▸ Set.mem_univ _
    obtain ⟨σ, hσ⟩ := this
    refine ⟨σ, ?_⟩
    change _ '' C s = C s'
    rw [hy₀, hy₁, hg, connectedComponent_eq hσ]

end CrystallineSemistableComparison.GeoC
