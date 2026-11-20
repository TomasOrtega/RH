import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
open GlobalTheory.BorelCoh CategoryTheory
open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

/- English proof (translation)
Use `set Wt := ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W with hWt`. Establish `hst_sup : ∀ A B : Submodule ℂ M, (∀ o, ∀ x ∈ A, act o x ∈ A) → (∀ o, ∀ x ∈ B, act o x ∈ B) → ∀ o, ∀ x ∈ A ⊔ B, act o x ∈ A ⊔ B`. Introduce `A B hA hB o x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hA o y hy) (hB o z hz)`. Set `s : Set (Submodule ℂ M)` to `{C | (∀ o, ∀ x ∈ C, act o x ∈ C) ∧ C ≤ Wt ∧ Disjoint V C}`. Take `⟨C, -, ⟨hCst, hCW, hCd⟩, hCmax⟩` from `zorn_le_nonempty₀ s (by`. Introduce `c hcs hc y hy`. Establish `hne : c.Nonempty` using `⟨y, hy⟩`.

Establish `hdir : DirectedOn (· ≤ ·) c` using `hc.directedOn`. Use `⟨sSup c, ⟨?_, sSup_le fun z hz => (hcs hz).2.1, ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Introduce `o x hx`. Take `⟨z, hz, hxz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hx`. Conclude with `(Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcs hz).1 o x hxz⟩`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxV hx`. Take `⟨z, hz, hxz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hx`. Conclude with `(Submodule.disjoint_def.1 (hcs hz).2.2) x hxV hxz) ⊥`. Use the proof step `⟨fun o x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero], bot_le, disjoint_bot_right⟩`.

Establish `hWle : Wt ≤ V ⊔ C`. Use `iSup₂_le fun S hS => ?_` and prove the remaining obligations. Take `⟨hSst, hSne, hSmin⟩` from `hS`. Establish `hinst : ∀ o, ∀ x ∈ S ⊓ (V ⊔ C), act o x ∈ S ⊓ (V ⊔ C)` using `fun o x hx => ⟨hSst o x hx.1, hst_sup V C hVst hCst o x hx.2⟩`. Break down `hSmin _ inf_le_left hinst with h | h` into its components or cases.

Establish `hSW : S ≤ Wt` using `le_iSup₂_of_le S ⟨hSst, hSne, hSmin⟩ le_rfl`. Establish `hmem : C ⊔ S ∈ s` using `⟨hst_sup C S hCst hSst, sup_le hCW hSW, Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (by rw [disjoint_comm, disjoint_iff]; exact h)⟩`. Conclude with `(le_sup_right.trans (hCmax hmem le_sup_left)).trans le_sup_right`. Conclude with `h ▸ inf_le_right`. Establish `hW : Wt = V ⊔ C` using `le_antisymm hWle (sup_le hV hCW)`.

Take `⟨D, hD⟩` from `Submodule.exists_isCompl Wt`. Establish `hc : IsCompl V (C ⊔ D)`. Prove the components needed by the constructor for the conclusion. Conclude with `Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (hW ▸ hD.disjoint)`. Rewrite using `[codisjoint_iff, ← sup_assoc, ← hW, hD.sup_eq_top]`.

Establish `hl : ∀ v ∈ V, (V.linearProjOfIsCompl (C ⊔ D) hc v : M) = v` using `fun v hv => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)`. Establish `hr : ∀ w ∈ C ⊔ D, V.linearProjOfIsCompl (C ⊔ D) hc w = 0` using `fun w hw => Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩`. Use `⟨V.subtype ∘ₗ V.linearProjOfIsCompl (C ⊔ D) hc, ?_, fun x => (V.linearProjOfIsCompl _ hc x).2, hl⟩` and prove the remaining obligations. Introduce `o x hx`. Rewrite `hx` using `[hW]`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Establish `hz' : z ∈ C ⊔ D` using `Submodule.mem_sup_left hz`. Establish `hz'' : act o z ∈ C ⊔ D` using `Submodule.mem_sup_left (hCst o z hz)`. Use `show (V.linearProjOfIsCompl _ hc (act o (y + z)) : M) = act o (V.linearProjOfIsCompl _ hc (y + z))`. Rewrite using `[map_add, map_add, map_add, hr _ hz'', hr _ hz', add_zero, add_zero, hl _ (hVst o y hy), hl _ hy]`.
-/
theorem exists_equivariant_proj_of_le_sum_irreducible {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := by
  set Wt := ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W with hWt
  have hst_sup : ∀ A B : Submodule ℂ M, (∀ o, ∀ x ∈ A, act o x ∈ A) → (∀ o, ∀ x ∈ B, act o x ∈ B) →
      ∀ o, ∀ x ∈ A ⊔ B, act o x ∈ A ⊔ B := by
    intro A B hA hB o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hA o y hy) (hB o z hz)

  let s : Set (Submodule ℂ M) := {C | (∀ o, ∀ x ∈ C, act o x ∈ C) ∧ C ≤ Wt ∧ Disjoint V C}
  obtain ⟨C, -, ⟨hCst, hCW, hCd⟩, hCmax⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, sSup_le fun z hz => (hcs hz).2.1, ?_⟩, fun z hz => le_sSup hz⟩
    · intro o x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcs hz).1 o x hxz⟩
    · rw [Submodule.disjoint_def]
      intro x hxV hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.disjoint_def.1 (hcs hz).2.2) x hxV hxz) ⊥
    ⟨fun o x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero], bot_le, disjoint_bot_right⟩

  have hWle : Wt ≤ V ⊔ C := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSst, hSne, hSmin⟩ := hS
    have hinst : ∀ o, ∀ x ∈ S ⊓ (V ⊔ C), act o x ∈ S ⊓ (V ⊔ C) := fun o x hx =>
      ⟨hSst o x hx.1, hst_sup V C hVst hCst o x hx.2⟩
    rcases hSmin _ inf_le_left hinst with h | h
    · have hSW : S ≤ Wt := le_iSup₂_of_le S ⟨hSst, hSne, hSmin⟩ le_rfl
      have hmem : C ⊔ S ∈ s := ⟨hst_sup C S hCst hSst, sup_le hCW hSW,
        Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (by rw [disjoint_comm, disjoint_iff]; exact h)⟩
      exact (le_sup_right.trans (hCmax hmem le_sup_left)).trans le_sup_right
    · exact h ▸ inf_le_right
  have hW : Wt = V ⊔ C := le_antisymm hWle (sup_le hV hCW)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl Wt
  have hc : IsCompl V (C ⊔ D) := by
    constructor
    · exact Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (hW ▸ hD.disjoint)
    · rw [codisjoint_iff, ← sup_assoc, ← hW, hD.sup_eq_top]
  have hl : ∀ v ∈ V, (V.linearProjOfIsCompl (C ⊔ D) hc v : M) = v := fun v hv =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)
  have hr : ∀ w ∈ C ⊔ D, V.linearProjOfIsCompl (C ⊔ D) hc w = 0 := fun w hw =>
    Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
  refine ⟨V.subtype ∘ₗ V.linearProjOfIsCompl (C ⊔ D) hc, ?_, fun x => (V.linearProjOfIsCompl _ hc x).2, hl⟩
  intro o x hx
  rw [hW] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have hz' : z ∈ C ⊔ D := Submodule.mem_sup_left hz
  have hz'' : act o z ∈ C ⊔ D := Submodule.mem_sup_left (hCst o z hz)
  show (V.linearProjOfIsCompl _ hc (act o (y + z)) : M) = act o (V.linearProjOfIsCompl _ hc (y + z))
  rw [map_add, map_add, map_add, hr _ hz'', hr _ hz', add_zero, add_zero, hl _ (hVst o y hy), hl _ hy]

/- English proof (translation)
Introduce `M O ι _ _ _ _ act V h1 h2 h3 h4 i`. Establish `hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W)` using `fun j => le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl`. Take `⟨p, hpe, hpV, hpid⟩` from `exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)`. Conclude with `⟨p, hpe, fun x _ => hpV x, hpid, fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩`.
-/
theorem exists_equivariant_proj_of_irreducible_family : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by
  intro M O ι _ _ _ _ act V h1 h2 h3 h4 i
  have hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) := fun j =>
    le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl
  obtain ⟨p, hpe, hpV, hpid⟩ := exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)
  exact ⟨p, hpe, fun x _ => hpV x, hpid,
    fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩

end GlobalTheory.BorelCoh
