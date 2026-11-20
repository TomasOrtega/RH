import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.DualFormInverse

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `⟨fun t => if t = p then α else 0, fun t => ?_, fun s => ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs`. Conclude with `hα`. Conclude with `S.zero_mem`. Rewrite using `[Fintype.sum_eq_single p]`.

Simplify using the standard rewrite rules. Introduce `t ht`. Simplify using `[ht]`.
-/
theorem exists_one {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p : ι} {α : K}
    (hα : α ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p := by
  refine ⟨fun t => if t = p then α else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    · exact hα
    · exact S.zero_mem
  · rw [Fintype.sum_eq_single p]
    · simp
    · intro t ht
      simp [ht]

/- English proof (translation)
Use `⟨fun t => if t = p then α else if t = q then β else 0, fun t => ?_, fun s => ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs exacts [hα, hβ, S.zero_mem]`. Rewrite using `[Fintype.sum_eq_add p q hpq]`. Simplify using `[hpq.symm]`. Introduce and unpack `t ⟨h1, h2⟩`.

Simplify using `[h1, h2]`.
-/
theorem exists_two {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p q : ι} (hpq : p ≠ q)
    {α β : K} (hα : α ∈ S) (hβ : β ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p + β * g s q := by
  refine ⟨fun t => if t = p then α else if t = q then β else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    exacts [hα, hβ, S.zero_mem]
  · rw [Fintype.sum_eq_add p q hpq]
    · simp [hpq.symm]
    · rintro t ⟨h1, h2⟩
      simp [h1, h2]

/- English proof (translation)
Use `choose κ hκS hκ using hinv`. Introduce `x hx`. Establish `hX : ∀ u, h (G u) x ∈ SP K 𝔭` using `fun u => by`. Rewrite using `[mem_SP_iff_locF]`. Conclude with `hx (G u) (LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨u, rfl⟩))`.

Establish `hyx : ∀ s, h (G s) (x - ∑ t, (∑ u, κ u t * h (G u) x) • G t) = 0`. Introduce `s`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [form_smul_right]`. Establish `e : ∀ t, (∑ u, κ u t * h (G u) x) * h (G s) (G t) = ∑ u, h (G u) x * (κ u t * h (G s) (G t))` using `fun t => by`.

Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun u _ => by ring`. Rewrite using `[Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, hκ]`. Simplify using the standard rewrite rules.

Establish `hxy` using `eq_zero_of_orth hs hnd G hG hyx`. Rewrite `hxy` using `[sub_eq_zero]`. Rewrite using `[hxy]`. Use `Submodule.sum_mem _ fun t _ => smul_mem_locF_of_SP ?_ (Submodule.subset_span ⟨t, rfl⟩)` and prove the remaining obligations. Conclude with `(SP K 𝔭).sum_mem fun u _ => (SP K 𝔭).mul_mem (hκS u t) (hX u)`.
-/
theorem dualF_le_of_inv {ι : Type} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hnd : Nondeg h) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (G : ι → V)
    (hG : Submodule.span K (Set.range G) = ⊤)
    (hinv : ∀ u, ∃ κ : ι → K, (∀ t, κ t ∈ SP K 𝔭) ∧
      ∀ s, ∑ t, κ t * h (G s) (G t) = if s = u then 1 else 0) :
    dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range G))) ≤
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range G)) := by
  choose κ hκS hκ using hinv
  intro x hx
  have hX : ∀ u, h (G u) x ∈ SP K 𝔭 := fun u => by
    rw [mem_SP_iff_locF]
    exact hx (G u) (LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨u, rfl⟩))
  have hyx : ∀ s, h (G s) (x - ∑ t, (∑ u, κ u t * h (G u) x) • G t) = 0 := by
    intro s
    rw [map_sub, map_sum]
    simp only [form_smul_right]
    have e : ∀ t, (∑ u, κ u t * h (G u) x) * h (G s) (G t) =
        ∑ u, h (G u) x * (κ u t * h (G s) (G t)) := fun t => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ]
    simp
  have hxy := eq_zero_of_orth hs hnd G hG hyx
  rw [sub_eq_zero] at hxy
  rw [hxy]
  refine Submodule.sum_mem _ fun t _ => smul_mem_locF_of_SP ?_ (Submodule.subset_span ⟨t, rfl⟩)
  exact (SP K 𝔭).sum_mem fun u _ => (SP K 𝔭).mul_mem (hκS u t) (hX u)

end Formalism.L2.SG.Pf.DualFormInverse
