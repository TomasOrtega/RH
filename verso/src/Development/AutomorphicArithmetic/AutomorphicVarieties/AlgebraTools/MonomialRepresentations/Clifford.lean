import Mathlib

open Polynomial Matrix

namespace UpperTheory.V.AlgebraTools

section

variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V) (N : Subgroup G) [hN : N.Normal]

private def cliffTr (g : G) (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) where
  toSubmodule := W.toSubmodule.comap (ρ g)
  apply_mem_toSubmodule n v hv := by
    have h := W.apply_mem_toSubmodule ⟨g * n * g⁻¹, hN.conj_mem _ n.2 g⟩ hv
    have e : ρ (g * n * g⁻¹) (ρ g v) = ρ g (ρ n v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    change ρ g (ρ n v) ∈ W.toSubmodule
    rw [← e]
    exact h

/- English proof (translation)
Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use extensionality with `v`. Express the relevant statement in the definitionally equal form `ρ g (ρ h v) ∈ W.toSubmodule ↔ _`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hgh, map_one]`. Both sides reduce to the same expression.
-/
private theorem cliffTr_mul (g h : G) (hgh : g * h = 1)
    (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    cliffTr ρ N h (cliffTr ρ N g W) = W := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change ρ g (ρ h v) ∈ W.toSubmodule ↔ _
  rw [← Module.End.mul_apply, ← map_mul, hgh, map_one]
  rfl

private def cliffIso (g : G) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) ≃o
      Subrepresentation (ρ.comp N.subtype : Representation K N V) :=
  Equiv.toOrderIso
    { toFun := cliffTr ρ N g
      invFun := cliffTr ρ N g⁻¹
      left_inv := cliffTr_mul ρ N g g⁻¹ (by simp)
      right_inv := cliffTr_mul ρ N g⁻¹ g (by simp) }
    (fun _ _ h _ hv => h hv) (fun _ _ h _ hv => h hv)

end

end UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `K G V _ _ _ _ _ ρ N _ hirr`. Rewrite using `[Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule, ← sSup_simples_eq_top_iff_isSemisimpleModule]`. Set `e` to `Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)`. Set `A` to `{m : Submodule (MonoidAlgebra K N) (Representation.asModule (ρ.comp N.subtype)) | IsSimpleModule (MonoidAlgebra K N) m}`. Establish `hA : ∀ m, m ∈ A ↔ IsAtom m` using `fun m => isSimpleModule_iff_isAtom`.

Express the relevant statement in the definitionally equal form `sSup A = ⊤`. Establish `inv : ∀ g : G, ∀ v : V, v ∈ e.symm (sSup A) → ρ g v ∈ e.symm (sSup A)`. Introduce `g v hv`. Set `φ` to `e.symm.trans ((UpperTheory.V.AlgebraTools.cliffIso ρ N g).trans e)`. Establish `hφ : φ (sSup A) = sSup A`.

Rewrite using `[OrderIso.map_sSup]`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup₂_le fun a ha => le_sSup ?_` and prove the remaining obligations. Conclude with `(hA _).2 ((φ.isAtom_iff a).2 ((hA a).1 ha))`. Use `sSup_le fun b hb => ?_` and prove the remaining obligations.

Establish `hb' : φ.symm b ∈ A` using `(hA _).2 ((φ.symm.isAtom_iff b).2 ((hA b).1 hb))`. Establish `h` using `le_iSup₂ (f := fun a (_ : a ∈ A) => φ a) (φ.symm b) hb'`. Simplify using `using h`. Establish `h : v ∈ e.symm (φ (sSup A))` using `by rw [hφ]; exact hv`. Conclude with `h`.

Set `T : Subrepresentation ρ` to `⟨(e.symm (sSup A)).toSubmodule, fun g v hv => inv g v hv⟩`. Break down `eq_bot_or_eq_top T with hT | hT` into its components or cases. It suffices to derive a contradiction. Establish `hmono : StrictMono (Subrepresentation.toSubmodule : Subrepresentation (ρ.comp N.subtype) → Submodule K V)` using `fun x y h => h`. Use `haveI := hmono.wellFoundedLT`.

Use `haveI : IsAtomic (Subrepresentation (ρ.comp N.subtype)) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt`. Establish `hne : (⊤ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊥`. Introduce `h`. Apply `(bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises.

Conclude with `(congrArg Subrepresentation.toSubmodule h).symm`. Take `⟨a, ha, -⟩` from `(eq_bot_or_exists_atom_le (⊤ : Subrepresentation (ρ.comp N.subtype))).resolve_left hne`. Establish `h1 : a ≤ e.symm (sSup A)`. Establish `h0 : e a ≤ sSup A` using `le_sSup ((hA _).2 ((e.isAtom_iff a).2 ha))`. Simplify using `using e.symm.monotone h0`.

Establish `h2 : (e.symm (sSup A)).toSubmodule = ⊥` using `congrArg Subrepresentation.toSubmodule hT`. Apply `ha.1` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises. Apply `le_antisymm _ bot_le` to reduce the goal to its premises. Introduce `v hv`.

Establish `h3 : v ∈ (e.symm (sSup A)).toSubmodule` using `h1 hv`. Rewrite `h3` using `[h2]`. Conclude with `h3`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Establish `h3 : (show V from v) ∈ T.toSubmodule` using `by rw [hT]; exact Submodule.mem_top`.

Conclude with `h3`.
-/
theorem UpperTheory.V.AlgebraTools.clifford :
    ∀ (K G V : Type) [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V)
      (N : Subgroup G) [N.Normal], ρ.IsIrreducible → Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  intro K G V _ _ _ _ _ ρ N _ hirr
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)
  let A := {m : Submodule (MonoidAlgebra K N) (Representation.asModule (ρ.comp N.subtype)) |
    IsSimpleModule (MonoidAlgebra K N) m}
  have hA : ∀ m, m ∈ A ↔ IsAtom m := fun m => isSimpleModule_iff_isAtom
  change sSup A = ⊤
  have inv : ∀ g : G, ∀ v : V, v ∈ e.symm (sSup A) → ρ g v ∈ e.symm (sSup A) := by
    intro g v hv
    let φ := e.symm.trans ((UpperTheory.V.AlgebraTools.cliffIso ρ N g).trans e)
    have hφ : φ (sSup A) = sSup A := by
      rw [OrderIso.map_sSup]
      apply le_antisymm
      · refine iSup₂_le fun a ha => le_sSup ?_
        exact (hA _).2 ((φ.isAtom_iff a).2 ((hA a).1 ha))
      · refine sSup_le fun b hb => ?_
        have hb' : φ.symm b ∈ A := (hA _).2 ((φ.symm.isAtom_iff b).2 ((hA b).1 hb))
        have h := le_iSup₂ (f := fun a (_ : a ∈ A) => φ a) (φ.symm b) hb'
        simpa using h
    have h : v ∈ e.symm (φ (sSup A)) := by rw [hφ]; exact hv
    exact h
  let T : Subrepresentation ρ := ⟨(e.symm (sSup A)).toSubmodule, fun g v hv => inv g v hv⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · exfalso
    have hmono : StrictMono (Subrepresentation.toSubmodule :
        Subrepresentation (ρ.comp N.subtype) → Submodule K V) :=
      fun x y h => h
    haveI := hmono.wellFoundedLT
    haveI : IsAtomic (Subrepresentation (ρ.comp N.subtype)) :=
      isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    have hne : (⊤ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊥ := by
      intro h
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.ext
      exact (congrArg Subrepresentation.toSubmodule h).symm
    obtain ⟨a, ha, -⟩ :=
      (eq_bot_or_exists_atom_le (⊤ : Subrepresentation (ρ.comp N.subtype))).resolve_left hne
    have h1 : a ≤ e.symm (sSup A) := by
      have h0 : e a ≤ sSup A := le_sSup ((hA _).2 ((e.isAtom_iff a).2 ha))
      simpa using e.symm.monotone h0
    have h2 : (e.symm (sSup A)).toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hT
    apply ha.1
    apply Subrepresentation.ext
    apply le_antisymm _ bot_le
    intro v hv
    have h3 : v ∈ (e.symm (sSup A)).toSubmodule := h1 hv
    rw [h2] at h3
    exact h3
  · refine eq_top_iff.2 fun v _ => ?_
    have h3 : (show V from v) ∈ T.toSubmodule := by rw [hT]; exact Submodule.mem_top
    exact h3
