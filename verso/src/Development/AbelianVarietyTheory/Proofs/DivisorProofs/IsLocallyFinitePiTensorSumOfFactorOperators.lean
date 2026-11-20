import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

/- English proof (translation)
Take `⟨t, rfl⟩` from `hy`. Proceed by induction on `t using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r x`. Establish `hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j`. Introduce `j`.

Distinguish the cases in `h : j = w`. Substitute `h` using the available equality. Simplify using `only [Function.update_self]`. Conclude with `hN j _ (x j).2`. Simplify using `only [Function.update_of_ne h, LinearMap.id_apply]`.

Conclude with `(x j).2`. Use `⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩` and prove the remaining obligations. Simplify using `[atPl, PiTensorProduct.map_tprod]`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`.

Conclude with `Submodule.add_mem _ ha hb`.
-/
theorem atPl_mem_range_map {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)) (N : ∀ i, Submodule ℂ (V i)) (hN : ∀ i, ∀ y ∈ N i, L i y ∈ N i)
    (w : ι) (y : ⨂[ℂ] i, V i) (hy : y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype)) :
    atPl w (L w) y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j := by
      intro j
      by_cases h : j = w
      · subst h
        simp only [Function.update_self]
        exact hN j _ (x j).2
      · simp only [Function.update_of_ne h, LinearMap.id_apply]
        exact (x j).2
    refine ⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩
    simp [atPl, PiTensorProduct.map_tprod]
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

/- English proof (translation)
Introduce `ι _ _ V _ _ L hL v`. Proceed by induction on `v using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f => choose N hNf hfN hN using fun i => hL i (f i)`. Use `⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩`.

Introduce `y hy`. Rewrite using `[sumPl, LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy`. Consider the case `add a b ha hb`. Take `⟨N₁, h₁, ha₁, hs₁⟩` from `ha`.

Take `⟨N₂, h₂, hb₂, hs₂⟩` from `hb`. Use `⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨y₁, hy₁, y₂, hy₂, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)`.
-/
theorem locFin_sumPl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) →
    GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  intro ι _ _ V _ _ L hL v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩
    · intro y hy
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)

/- English proof (translation)
The claim follows from `locFin_sumPl`.
-/
example : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := locFin_sumPl

end GlobalTheory.RealLift
