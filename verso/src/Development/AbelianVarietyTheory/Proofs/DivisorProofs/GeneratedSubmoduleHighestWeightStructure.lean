import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.GenHW

/- English proof (translation)
Introduce `R S M Λ v hv`. Establish `hKS : KStable M.act (GlobalTheory.BlockReps.gen M.act v)` using `GlobalTheory.BlockReps.stable_gen (act := M.act) v`. Use `set G := GlobalTheory.BlockReps.gen M.act v with hG`. Use `set ρ := restrAct M.act G hKS with hρ`. Establish `hρapp : ∀ Z, IsKC Z → ∀ x : G, ((ρ Z x : G) : M.V) = M.act Z x`.

Introduce `Z hZ x`. Rewrite using `[hρ, restrAct_apply, kpart_of_isKC hZ]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨W, hWf, hvW, hWs⟩` from `M.kfin v`. Conclude with `Submodule.finiteDimensional_of_le (GlobalTheory.BlockReps.gen_le hvW hWs)`.

Introduce `Y Z hY hZ`. Use extensionality with `x`. Establish `hYZ` using `GlobalTheory.TensorHW.isKC_comm hY hZ`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]`. Rewrite using `[hρapp _ hYZ, hρapp _ hY, hρapp _ hZ, hρapp _ hZ, hρapp _ hY, M.lie]`.

Simplify using the standard rewrite rules. Introduce `w`. Establish `h` using `GlobalTheory.BlockReps.decomp hKS w.2 (M.wts w)`. Establish `hle : (⨆ μ, G ⊓ wtSub M.act μ) ≤ (⨆ μ : Ix R S → ℚ, wtSub ρ μ).map G.subtype`. Use `iSup_le fun μ x hx => ⟨⟨x, hx.1⟩, Submodule.mem_iSup_of_mem μ ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.TensorHW.mem_wt]`. Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]`. Conclude with `GlobalTheory.TensorHW.mem_wt.1 hx.2 a`.

Take `⟨y, hy, hyw⟩` from `Submodule.mem_map.1 (hle h)`. Rewrite `hy` using `[Subtype.val_injective hyw]`. Then use the resulting hypothesis. Use `⟨fun h => hv.1 (congrArg Subtype.val h), ?_⟩` and prove the remaining obligations. Establish `hv2` using `GlobalTheory.TensorHW.mem_hw.1 hv.2`. Rewrite using `[GlobalTheory.TensorHW.mem_hw]`.

Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]`. Conclude with `hv2.1 a`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hab))]`. Conclude with `hv2.2 a b hab`. Use `set N := GlobalTheory.BlockReps.gen ρ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hN`. Establish `hNs : KStable ρ N` using `GlobalTheory.BlockReps.stable_gen (act := ρ) _`. Establish `hmap : KStable M.act (N.map G.subtype)`.

Introduce and unpack `X hX _ ⟨y, hy, rfl⟩`. Conclude with `⟨ρ X y, hNs X hX y hy, hρapp X hX y⟩`. Establish `hle : G ≤ N.map G.subtype` using `GlobalTheory.BlockReps.gen_le ⟨⟨v, GlobalTheory.BlockReps.mem_gen v⟩, GlobalTheory.BlockReps.mem_gen _, rfl⟩ hmap`. Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨y, hy, hyw⟩` from `Submodule.mem_map.1 (hle w.2)`.

Rewrite `hy` using `[Subtype.val_injective hyw]`. Then use the resulting hypothesis.
-/
theorem block_span_hw : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    FiniteDimensional ℂ (GlobalTheory.BlockReps.gen M.act v) ∧
    IsKLieAct (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ∧
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) μ) ∧
    IsHW (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) Λ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ ∧
    GlobalTheory.BlockReps.gen (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ = ⊤ := by
  intro R S M Λ v hv
  have hKS : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set G := GlobalTheory.BlockReps.gen M.act v with hG
  set ρ := restrAct M.act G hKS with hρ
  have hρapp : ∀ Z, IsKC Z → ∀ x : G, ((ρ Z x : G) : M.V) = M.act Z x := by
    intro Z hZ x
    rw [hρ, restrAct_apply, kpart_of_isKC hZ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
    exact Submodule.finiteDimensional_of_le (GlobalTheory.BlockReps.gen_le hvW hWs)
  · intro Y Z hY hZ
    ext x
    have hYZ := GlobalTheory.TensorHW.isKC_comm hY hZ
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [hρapp _ hYZ, hρapp _ hY, hρapp _ hZ, hρapp _ hZ, hρapp _ hY, M.lie]
    simp
  · intro w
    have h := GlobalTheory.BlockReps.decomp hKS w.2 (M.wts w)
    have hle : (⨆ μ, G ⊓ wtSub M.act μ) ≤ (⨆ μ : Ix R S → ℚ, wtSub ρ μ).map G.subtype := by
      refine iSup_le fun μ x hx => ⟨⟨x, hx.1⟩, Submodule.mem_iSup_of_mem μ ?_, rfl⟩
      rw [GlobalTheory.TensorHW.mem_wt]
      intro a
      apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact GlobalTheory.TensorHW.mem_wt.1 hx.2 a
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle h)
    rwa [Subtype.val_injective hyw] at hy
  · refine ⟨fun h => hv.1 (congrArg Subtype.val h), ?_⟩
    have hv2 := GlobalTheory.TensorHW.mem_hw.1 hv.2
    rw [GlobalTheory.TensorHW.mem_hw]
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact hv2.1 a
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hab))]
      exact hv2.2 a b hab
  · set N := GlobalTheory.BlockReps.gen ρ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hN
    have hNs : KStable ρ N := GlobalTheory.BlockReps.stable_gen (act := ρ) _
    have hmap : KStable M.act (N.map G.subtype) := by
      rintro X hX _ ⟨y, hy, rfl⟩
      exact ⟨ρ X y, hNs X hX y hy, hρapp X hX y⟩
    have hle : G ≤ N.map G.subtype :=
      GlobalTheory.BlockReps.gen_le ⟨⟨v, GlobalTheory.BlockReps.mem_gen v⟩, GlobalTheory.BlockReps.mem_gen _, rfl⟩ hmap
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle w.2)
    rwa [Subtype.val_injective hyw] at hy

end GlobalTheory.GenHW
