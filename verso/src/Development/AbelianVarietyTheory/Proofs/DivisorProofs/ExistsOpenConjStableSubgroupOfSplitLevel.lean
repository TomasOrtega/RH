import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

/- English proof (translation)
Take `⟨hKo, hKc⟩` from `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n`. Establish `hUtop : UL n w = ⊤` using `by unfold UL; rw [if_pos hw]`. Establish `hUo : IsOpen (UL n w : Set (GLw n w))` using `by rw [hUtop]; exact isOpen_univ`. Establish `hmemU : ∀ x : GLw n w, x ∈ UL n w` using `fun x => by rw [hUtop]; trivial`. Distinguish the cases in `hKL : K' = KL n w`.

Use `⟨GlobalTheory.LFun.KGL w n, hKo, ?_, ?_, fun _ => rfl⟩` and prove the remaining obligations. Introduce `x hx`. Use `Subgroup.mem_map.2 ⟨⟨x, hmemU x⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hKL, KL, Subgroup.mem_subgroupOf]`. Conclude with `hx`.

Introduce `k hk x hx`. Conclude with `(GlobalTheory.LFun.KGL w n).mul_mem ((GlobalTheory.LFun.KGL w n).mul_mem ((GlobalTheory.LFun.KGL w n).inv_mem hk) hx) hk`. Use `set S : Subgroup (GLw n w) := K'.map (UL n w).subtype with hSdef`. Establish `hSo : IsOpen (S : Set (GLw n w))`. Rewrite using `[hSdef, Subgroup.coe_map]`.

Conclude with `hUo.isOpenMap_subtype_val _ hK.1`. Use `haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hKc`. Establish `hWo : IsOpen ((S.subgroupOf (GlobalTheory.LFun.KGL w n) : Subgroup _) : Set (GlobalTheory.LFun.KGL w n))`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hSo.preimage continuous_subtype_val`.

Take `⟨V, hV⟩` from `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one ⟨Subgroup.isClosed_of_isOpen _ hWo, hWo⟩ (Subgroup.one_mem _)`. Use `⟨V.toSubgroup.map (GlobalTheory.LFun.KGL w n).subtype, ?_, ?_, ?_, fun h => absurd h hKL⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map]`. Conclude with `hKo.isOpenMap_subtype_val _ V.isOpen'`. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Use `hV hv` as an intermediate fact. Rewrite `this` using `[SetLike.mem_coe, Subgroup.mem_subgroupOf]`. Conclude with `this`. Introduce and unpack `k hk _ ⟨v, hv, rfl⟩`. Use `⟨(⟨k, hk⟩ : GlobalTheory.LFun.KGL w n)⁻¹ * v * (⟨k, hk⟩ : GlobalTheory.LFun.KGL w n), ?_, ?_⟩` and prove the remaining obligations.

Use `V.isNormal'.conj_mem v hv (⟨k, hk⟩ : GlobalTheory.LFun.KGL w n)⁻¹` as an intermediate fact. Simplify using `using this`. Simplify using the standard rewrite rules.
-/
theorem exists_open_conjStable_sub_level (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (K' : Subgroup (UL n w)) (hw : IsSplitAt w) (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w n) := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hUtop : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hUo : IsOpen (UL n w : Set (GLw n w)) := by rw [hUtop]; exact isOpen_univ
  have hmemU : ∀ x : GLw n w, x ∈ UL n w := fun x => by rw [hUtop]; trivial
  by_cases hKL : K' = KL n w
  · refine ⟨GlobalTheory.LFun.KGL w n, hKo, ?_, ?_, fun _ => rfl⟩
    · intro x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hmemU x⟩, ?_, rfl⟩
      rw [hKL, KL, Subgroup.mem_subgroupOf]
      exact hx
    · intro k hk x hx
      exact (GlobalTheory.LFun.KGL w n).mul_mem ((GlobalTheory.LFun.KGL w n).mul_mem ((GlobalTheory.LFun.KGL w n).inv_mem hk) hx) hk
  · set S : Subgroup (GLw n w) := K'.map (UL n w).subtype with hSdef
    have hSo : IsOpen (S : Set (GLw n w)) := by
      rw [hSdef, Subgroup.coe_map]
      exact hUo.isOpenMap_subtype_val _ hK.1
    haveI : CompactSpace (GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hKc
    have hWo : IsOpen ((S.subgroupOf (GlobalTheory.LFun.KGL w n) : Subgroup _) : Set (GlobalTheory.LFun.KGL w n)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hSo.preimage continuous_subtype_val
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ hWo, hWo⟩ (Subgroup.one_mem _)
    refine ⟨V.toSubgroup.map (GlobalTheory.LFun.KGL w n).subtype, ?_, ?_, ?_, fun h => absurd h hKL⟩
    · rw [Subgroup.coe_map]
      exact hKo.isOpenMap_subtype_val _ V.isOpen'
    · rintro _ ⟨v, hv, rfl⟩
      have := hV hv
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at this
      exact this
    · rintro k hk _ ⟨v, hv, rfl⟩
      refine ⟨(⟨k, hk⟩ : GlobalTheory.LFun.KGL w n)⁻¹ * v * (⟨k, hk⟩ : GlobalTheory.LFun.KGL w n), ?_, ?_⟩
      · have := V.isNormal'.conj_mem v hv (⟨k, hk⟩ : GlobalTheory.LFun.KGL w n)⁻¹
        simpa using this
      · simp

end GlobalTheory.BCT.CtLevel
