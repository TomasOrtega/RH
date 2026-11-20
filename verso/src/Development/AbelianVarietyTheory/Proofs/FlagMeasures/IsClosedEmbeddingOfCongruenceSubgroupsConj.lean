import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

/- English proof (translation)
Establish `hcl : IsClosed (U ∩ Set.range φ)`. Establish `e : U ∩ Set.range φ = φ '' (φ ⁻¹' U)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, g, rfl⟩`.

Conclude with `⟨g, hy, rfl⟩`. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨hg, g, rfl⟩`. Rewrite using `[e]`. Conclude with `(hc.image hφ).isClosed`.

Use `closure_subset_iff_isClosed.mp fun x hx => ?_` and prove the remaining obligations. Establish `hO : IsOpen ((fun s => s⁻¹ * x) ⁻¹' U)` using `hU.preimage (by fun_prop)`. Establish `hxO : x ∈ (fun s => s⁻¹ * x) ⁻¹' U` using `by show x⁻¹ * x ∈ U`. Rewrite using `[inv_mul_cancel]` and apply the resulting hypothesis. Take `⟨s, hsU, g, rfl⟩` from `mem_closure_iff.mp hx _ hO hxO`.

Establish `hy : (φ g)⁻¹ * x ∈ closure (Set.range φ)` using `map_mem_closure (f := fun s => (φ g)⁻¹ * s) (by fun_prop) hx (by rintro _ ⟨k, rfl⟩; exact ⟨g⁻¹ * k, by simp⟩)`. Establish `hyU : (φ g)⁻¹ * x ∈ U ∩ Set.range φ`. Rewrite using `[← hcl.closure_eq]`. Conclude with `hU.inter_closure ⟨hsU, hy⟩`. Take `⟨-, k, hk⟩` from `hyU`.

Conclude with `⟨g * k, by rw [map_mul, hk, mul_inv_cancel_left]⟩`.
-/
theorem isClosed_range_of_isCompact_preimage {G H : Type} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (φ : G →* H) (hφ : Continuous φ) (U : Set H)
    (hU : IsOpen U) (h1 : (1 : H) ∈ U) (hc : IsCompact (φ ⁻¹' U)) : IsClosed (Set.range φ) := by
  have hcl : IsClosed (U ∩ Set.range φ) := by
    have e : U ∩ Set.range φ = φ '' (φ ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨hy, g, rfl⟩
        exact ⟨g, hy, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨hg, g, rfl⟩
    rw [e]
    exact (hc.image hφ).isClosed
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  have hO : IsOpen ((fun s => s⁻¹ * x) ⁻¹' U) := hU.preimage (by fun_prop)
  have hxO : x ∈ (fun s => s⁻¹ * x) ⁻¹' U := by
    show x⁻¹ * x ∈ U
    rwa [inv_mul_cancel]
  obtain ⟨s, hsU, g, rfl⟩ := mem_closure_iff.mp hx _ hO hxO
  have hy : (φ g)⁻¹ * x ∈ closure (Set.range φ) :=
    map_mem_closure (f := fun s => (φ g)⁻¹ * s) (by fun_prop) hx
      (by rintro _ ⟨k, rfl⟩; exact ⟨g⁻¹ * k, by simp⟩)
  have hyU : (φ g)⁻¹ * x ∈ U ∩ Set.range φ := by
    rw [← hcl.closure_eq]
    exact hU.inter_closure ⟨hsU, hy⟩
  obtain ⟨-, k, hk⟩ := hyU
  exact ⟨g * k, by rw [map_mul, hk, mul_inv_cancel_left]⟩

/- English proof (translation)
Use `⟨fun t => ⟨fun ht => I.topf_basis t ht, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨N, hN, hsub⟩`. Use `Filter.mem_of_superset ((I.topf_open N hN).mem_nhds ?_) hsub` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`. Use `⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩` and prove the remaining obligations.

Simplify using `using one_mem (Formalism.UG.stabGL (lamAf (F := I.F) I.L))`. Simplify using the standard rewrite rules.
-/
theorem nhds_one_hasBasis_Kg (I : AutInst) : (nhds (1 : I.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) I.Kg := by
  refine ⟨fun t => ⟨fun ht => I.topf_basis t ht, ?_⟩⟩
  rintro ⟨N, hN, hsub⟩
  refine Filter.mem_of_superset ((I.topf_open N hN).mem_nhds ?_) hsub
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simpa using one_mem (Formalism.UG.stabGL (lamAf (F := I.F) I.L))
  · simp

/- English proof (translation)
Establish `hpre : (fun N : ℕ => φ ⁻¹' I.Kg N) = I'.Kg`. Use function extensionality and compare the values at `N`. Use extensionality with `g`. Conclude with `(h N g).symm`. Establish `hb : (nhds (1 : I'.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) fun N => φ ⁻¹' I.Kg N`.

Rewrite using `[hpre]`. Conclude with `nhds_one_hasBasis_Kg I'`. Establish `hind : Topology.IsInducing φ` using `IsTopologicalGroup.isInducing_iff_nhds_one.mpr (hb.eq_of_same_basis ((nhds_one_hasBasis_Kg I).comap φ))`. Establish `hT'` using `GlobalTheory.CongTop.adelic_topology I'`. Use `haveI : T2Space I'.Gf := hT'.1`.

Use `haveI : T2Space I.Gf := (GlobalTheory.CongTop.adelic_topology I).1`. Take `⟨hopen1, ⟨K, hK⟩, -⟩` from `hT'.2.2.2.2.2.2 1 le_rfl`. Establish `hKcl : IsClosed (I'.Kg 1)`. Rewrite using `[← hK]`. Conclude with `K.isClosed_of_isOpen (by rw [hK]; exact hopen1)`.

Establish `hcpt : IsCompact (φ ⁻¹' I.Kg 1)`. Rewrite using `[show φ ⁻¹' I.Kg 1 = I'.Kg 1 from congrFun hpre 1]`. Conclude with `hT'.2.2.2.1.of_isClosed_subset hKcl fun x hx => hx.1`. Establish `hU : IsOpen (I.Kg 1)` using `((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 1 le_rfl).1`. Establish `h1 : (1 : I.Gf) ∈ I.Kg 1` using `mem_of_mem_nhds ((nhds_one_hasBasis_Kg I).mem_of_mem le_rfl)`.

Conclude with `⟨hind.isEmbedding, isClosed_range_of_isCompact_preimage φ hind.continuous (I.Kg 1) hU h1 hcpt⟩`.
-/
theorem isClosedEmbedding_of_preimage_Kg (I I' : AutInst) (φ : I'.Gf →* I.Gf)
    (h : ∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ φ g ∈ I.Kg N) : Topology.IsClosedEmbedding φ := by
  have hpre : (fun N : ℕ => φ ⁻¹' I.Kg N) = I'.Kg := by
    funext N
    ext g
    exact (h N g).symm
  have hb : (nhds (1 : I'.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) fun N => φ ⁻¹' I.Kg N := by
    rw [hpre]
    exact nhds_one_hasBasis_Kg I'
  have hind : Topology.IsInducing φ :=
    IsTopologicalGroup.isInducing_iff_nhds_one.mpr
      (hb.eq_of_same_basis ((nhds_one_hasBasis_Kg I).comap φ))
  have hT' := GlobalTheory.CongTop.adelic_topology I'
  haveI : T2Space I'.Gf := hT'.1
  haveI : T2Space I.Gf := (GlobalTheory.CongTop.adelic_topology I).1
  obtain ⟨hopen1, ⟨K, hK⟩, -⟩ := hT'.2.2.2.2.2.2 1 le_rfl
  have hKcl : IsClosed (I'.Kg 1) := by
    rw [← hK]
    exact K.isClosed_of_isOpen (by rw [hK]; exact hopen1)
  have hcpt : IsCompact (φ ⁻¹' I.Kg 1) := by
    rw [show φ ⁻¹' I.Kg 1 = I'.Kg 1 from congrFun hpre 1]
    exact hT'.2.2.2.1.of_isClosed_subset hKcl fun x hx => hx.1
  have hU : IsOpen (I.Kg 1) := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 1 le_rfl).1
  have h1 : (1 : I.Gf) ∈ I.Kg 1 := mem_of_mem_nhds ((nhds_one_hasBasis_Kg I).mem_of_mem le_rfl)
  exact ⟨hind.isEmbedding, isClosed_range_of_isCompact_preimage φ hind.continuous (I.Kg 1) hU h1 hcpt⟩

/- English proof (translation)
Introduce `I I' j xf hj`. Set `ψ : I'.Gf →* I.Gf` to `(MulAut.conj xf⁻¹).toMonoidHom.comp j`. Establish `hψ : ∀ g, ψ g = xf⁻¹ * j g * xf` using `fun g => by simp [ψ, MulAut.conj_apply]`. Establish `hc : Topology.IsClosedEmbedding ψ` using `isClosedEmbedding_of_preimage_Kg I I' ψ fun N g => by rw [hψ]; exact hj N g`. Establish `e : (j : I'.Gf → I.Gf) = ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)) ∘ ψ`.

Use function extensionality and compare the values at `g`. Simplify using `[hψ, mul_assoc]`. Rewrite using `[e]`. Conclude with `((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)).isClosedEmbedding.comp hc`.
-/
theorem isClosedEmbedding_of_conj_Kg : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf),
    (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  intro I I' j xf hj
  let ψ : I'.Gf →* I.Gf := (MulAut.conj xf⁻¹).toMonoidHom.comp j
  have hψ : ∀ g, ψ g = xf⁻¹ * j g * xf := fun g => by simp [ψ, MulAut.conj_apply]
  have hc : Topology.IsClosedEmbedding ψ :=
    isClosedEmbedding_of_preimage_Kg I I' ψ fun N g => by rw [hψ]; exact hj N g
  have e : (j : I'.Gf → I.Gf) = ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)) ∘ ψ := by
    funext g
    simp [hψ, mul_assoc]
  rw [e]
  exact ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)).isClosedEmbedding.comp hc

end GlobalTheory.StabUnfold
