import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

/- English proof (translation)
Introduce `G V _ _ _ ρ A B E hBA hirr hEA hEB`. Use `haveI : IsSimpleOrder (Subrepresentation (GlobalTheory.SmGL.subQuot A B)) := hirr`. Use `le_antisymm (sup_le hEA hBA) ?_` and prove the remaining obligations. Set `P` to `Submodule.comap A.toSubmodule.subtype B.toSubmodule`. Set `S : Submodule ℂ (A.toSubmodule ⧸ P)` to `Submodule.map P.mkQ (Submodule.comap A.toSubmodule.subtype (E ⊔ B).toSubmodule)`.

Establish `hS : ∀ (g : G) ⦃q : A.toSubmodule ⧸ P⦄, q ∈ S → GlobalTheory.SmGL.subQuot A B g q ∈ S`. Introduce `g q hq`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hq`. Conclude with `Submodule.mem_map.mpr ⟨⟨ρ g y, A.apply_mem_toSubmodule g y.2⟩, (E ⊔ B).apply_mem_toSubmodule g (v := (y : V)) hy, rfl⟩`. Set `W : Subrepresentation (GlobalTheory.SmGL.subQuot A B)` to `⟨S, hS⟩`.

Take `⟨e, heE, heB⟩` from `SetLike.not_le_iff_exists.mp hEB`. Establish `hea : e ∈ A.toSubmodule` using `hEA heE`. Establish `heEB : e ∈ (E ⊔ B).toSubmodule` using `(le_sup_left : E ≤ E ⊔ B) heE`. Break down `IsSimpleOrder.eq_bot_or_eq_top W with hW | hW` into its components or cases. It suffices to derive a contradiction.

Set `Z : Subrepresentation (GlobalTheory.SmGL.subQuot A B)` to `⟨⊥, fun g q hq => by`. Rewrite `hq`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hq, map_zero]⟩`. Establish `hmem : Submodule.Quotient.mk (p` using `P) ⟨e, hea⟩ ∈ W := by show _ ∈ S`. Conclude with `Submodule.mem_map.mpr ⟨⟨e, hea⟩, heEB, rfl⟩`.

Rewrite `hmem` using `[hW]`. Establish `hZ : Submodule.Quotient.mk (p` using `P) ⟨e, hea⟩ ∈ Z := (bot_le : ⊥ ≤ Z) hmem`. Establish `hZ' : Submodule.Quotient.mk (p` using `P) ⟨e, hea⟩ ∈ (⊥ : Submodule ℂ (A.toSubmodule ⧸ P)) := hZ`. Establish `h0 : Submodule.Quotient.mk (p` using `P) ⟨e, hea⟩ = 0 := (Submodule.mem_bot ℂ).mp hZ'`. Establish `heP : (⟨e, hea⟩ : A.toSubmodule) ∈ P` using `(Submodule.Quotient.mk_eq_zero P).mp h0`.

Conclude with `heB heP`. Introduce `x hx`. Establish `hxA : x ∈ A.toSubmodule` using `hx`. Set `T : Subrepresentation (GlobalTheory.SmGL.subQuot A B)` to `⟨⊤, fun _ _ _ => Submodule.mem_top⟩`. Establish `hT : Submodule.Quotient.mk (p` using `P) ⟨x, hxA⟩ ∈ W := by`.

Rewrite using `[hW]`. Conclude with `(le_top : T ≤ ⊤) (show Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ (⊤ : Submodule ℂ (A.toSubmodule ⧸ P)) from Submodule.mem_top)`. Establish `hT' : Submodule.Quotient.mk (p` using `P) ⟨x, hxA⟩ ∈ S := hT`. Take `⟨y, hy, hyx⟩` from `Submodule.mem_map.mp hT'`. Rewrite `hyx` using `[Submodule.mkQ_apply, Submodule.Quotient.eq]`.

Establish `hb : (y : V) - x ∈ B.toSubmodule` using `hyx`. Establish `hb' : (y : V) - x ∈ (E ⊔ B).toSubmodule` using `(le_sup_right : B ≤ E ⊔ B) hb`. Establish `hy' : (y : V) ∈ (E ⊔ B).toSubmodule` using `hy`. Establish `hsub` using `(E ⊔ B).toSubmodule.sub_mem hy' hb'`. Rewrite `hsub` using `[sub_sub_cancel]`.

Conclude with `hsub`.
-/
theorem sup_eq_of_isIrreducible_subQuot :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B →
      E ⊔ B = A := by
  intro G V _ _ _ ρ A B E hBA hirr hEA hEB
  haveI : IsSimpleOrder (Subrepresentation (GlobalTheory.SmGL.subQuot A B)) := hirr
  refine le_antisymm (sup_le hEA hBA) ?_
  let P := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let S : Submodule ℂ (A.toSubmodule ⧸ P) :=
    Submodule.map P.mkQ (Submodule.comap A.toSubmodule.subtype (E ⊔ B).toSubmodule)
  have hS : ∀ (g : G) ⦃q : A.toSubmodule ⧸ P⦄, q ∈ S →
      GlobalTheory.SmGL.subQuot A B g q ∈ S := by
    intro g q hq
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr
      ⟨⟨ρ g y, A.apply_mem_toSubmodule g y.2⟩, (E ⊔ B).apply_mem_toSubmodule g (v := (y : V)) hy, rfl⟩
  let W : Subrepresentation (GlobalTheory.SmGL.subQuot A B) := ⟨S, hS⟩
  obtain ⟨e, heE, heB⟩ := SetLike.not_le_iff_exists.mp hEB
  have hea : e ∈ A.toSubmodule := hEA heE
  have heEB : e ∈ (E ⊔ B).toSubmodule := (le_sup_left : E ≤ E ⊔ B) heE
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · exfalso
    let Z : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊥, fun g q hq => by
        rw [Submodule.mem_bot] at hq ⊢
        rw [hq, map_zero]⟩
    have hmem : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ W := by
      show _ ∈ S
      exact Submodule.mem_map.mpr ⟨⟨e, hea⟩, heEB, rfl⟩
    rw [hW] at hmem
    have hZ : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ Z := (bot_le : ⊥ ≤ Z) hmem
    have hZ' : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ (⊥ : Submodule ℂ (A.toSubmodule ⧸ P)) := hZ
    have h0 : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ = 0 := (Submodule.mem_bot ℂ).mp hZ'
    have heP : (⟨e, hea⟩ : A.toSubmodule) ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h0
    exact heB heP
  · intro x hx
    have hxA : x ∈ A.toSubmodule := hx
    let T : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
    have hT : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ W := by
      rw [hW]
      exact (le_top : T ≤ ⊤)
        (show Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ (⊤ : Submodule ℂ (A.toSubmodule ⧸ P)) from
          Submodule.mem_top)
    have hT' : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ S := hT
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hT'
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hyx
    have hb : (y : V) - x ∈ B.toSubmodule := hyx
    have hb' : (y : V) - x ∈ (E ⊔ B).toSubmodule := (le_sup_right : B ≤ E ⊔ B) hb
    have hy' : (y : V) ∈ (E ⊔ B).toSubmodule := hy
    have hsub := (E ⊔ B).toSubmodule.sub_mem hy' hb'
    rw [sub_sub_cancel] at hsub
    exact hsub

end GlobalTheory.CompanionTheory.GenCore
