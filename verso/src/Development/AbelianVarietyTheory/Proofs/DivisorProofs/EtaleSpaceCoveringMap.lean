import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGraph
open GlobalTheory.PrimLift

namespace GlobalTheory.PrimLift.SphericalEisensteinCover

variable {X : Type} [TopologicalSpace X] {P : Set X → (X → ℂ) → Prop}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨hy, rfl⟩`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨Etale.proj P e, h1, ?_⟩` and prove the remaining obligations.

Use `show Etale.mk P _ (g _) = e`. Rewrite using `[← h2]`. Both sides reduce to the same expression.
-/
theorem mem_graph_iff {O : Set X} {g : X → ℂ} (e : Etale P) :
    e ∈ (fun y => Etale.mk P y (g y)) '' O ↔ Etale.proj P e ∈ O ∧ e.val = g (Etale.proj P e) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Etale.proj P e, h1, ?_⟩
    show Etale.mk P _ (g _) = e
    rw [← h2]
    rfl

/- English proof (translation)
Rewrite using `[continuous_def]`. Introduce `V hV`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `e he`. Take `⟨O1, f1, h1, hP1⟩` from `hcov (Etale.proj P e)`.

Establish `hP' : P (O1 ∩ V) (fun y => f1 y + (e.val - f1 (Etale.proj P e)))` using `hadd _ _ _ (hmono _ _ _ hP1 ((hopen _ _ hP1).inter hV) Set.inter_subset_left)`. Use `⟨_, ?_, Etale.isOpen_graph hP', ?_⟩` and prove the remaining obligations. Introduce `e' he'`. Conclude with `((mem_graph_iff e').1 he').1.2`. Rewrite using `[mem_graph_iff]`.

Use `⟨⟨h1, he⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem continuous_proj
    (hopen : ∀ O f, P O f → IsOpen O)
    (hmono : ∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f)
    (hadd : ∀ O f (c : ℂ), P O f → P O (fun y => f y + c))
    (hcov : ∀ x, ∃ O f, x ∈ O ∧ P O f) :
    Continuous (Etale.proj P) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro e he
  obtain ⟨O1, f1, h1, hP1⟩ := hcov (Etale.proj P e)
  have hP' : P (O1 ∩ V) (fun y => f1 y + (e.val - f1 (Etale.proj P e))) :=
    hadd _ _ _ (hmono _ _ _ hP1 ((hopen _ _ hP1).inter hV) Set.inter_subset_left)
  refine ⟨_, ?_, Etale.isOpen_graph hP', ?_⟩
  · intro e' he'
    exact ((mem_graph_iff e').1 he').1.2
  · rw [mem_graph_iff]
    refine ⟨⟨h1, he⟩, ?_⟩
    simp

end GlobalTheory.PrimLift.SphericalEisensteinCover

open GlobalTheory.PrimLift.SphericalEisensteinCover in
/- English proof (translation)
Establish `hproj` using `continuous_proj hopen hmono hadd hcov`. Introduce `x`. Take `⟨O, f, hxO, hP⟩` from `hcov x`. Use `letI : TopologicalSpace ℂ := ⊥`. Use `haveI : DiscreteTopology ℂ := ⟨rfl⟩`.

Establish `hO : IsOpen O` using `hopen _ _ hP`. Set `H : Etale.proj P ⁻¹' O ≃ₜ O × ℂ` to `{ toFun := fun e => (⟨Etale.proj P e.1, e.2⟩, e.1.val - f (Etale.proj P e.1)) invFun := fun p => ⟨Etale.mk P p.1.1 (f p.1.1 + p.2), p.1.2⟩ left_inv := by`. Introduce `e`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Etale.mk P _ _ = e.1`.

Rewrite using `[add_sub_cancel]`. Both sides reduce to the same expression. Use `right_inv := by`. Introduce `p`. Apply the tactic sequence `ext <;> simp`.

Use `continuous_toFun := by`. Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations. Conclude with `(hproj.comp continuous_subtype_val).subtype_mk _`. Rewrite using `[continuous_discrete_rng]`. Introduce `c`.

Establish `hG` using `Etale.isOpen_graph (hadd _ _ c hP)`. Use `hG.preimage continuous_subtype_val using 1` and compare the differences between its conclusion and the goal. Use extensionality with `e`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, mem_graph_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨e.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨_, h⟩`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Use `continuous_invFun := by`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Apply `continuous_generateFrom_iff.mpr` to reduce the goal to its premises.

Introduce and unpack `S ⟨O', g, hP'', rfl⟩`. Establish `hU : ∀ c : ℂ, IsOpen {y : O | (y : X) ∈ O ∩ O' ∧ f y + c = g y}`. Introduce `c`. Establish `hOO' : IsOpen (O ∩ O')` using `hO.inter (hopen _ _ hP'')`. Establish `h1 : P (O ∩ O') (fun y => f y + c)` using `hmono _ _ _ (hadd _ _ c hP) hOO' Set.inter_subset_left`.

Establish `h2 : P (O ∩ O') g` using `hmono _ _ _ hP'' hOO' Set.inter_subset_right`. Conclude with `(heq _ _ _ h1 h2).preimage continuous_subtype_val`. Establish `: (fun p : O × ℂ => Etale.mk P p.1.1 (f p.1.1 + p.2)) ⁻¹' ((fun y => Etale.mk P y (g y)) '' O') = ⋃ c : ℂ, {y : O | (y : X) ∈ O ∩ O' ∧ f y + c = g y} ×ˢ {c}`. Use extensionality with `⟨y, c⟩`. Simplify using `only [Set.mem_preimage, mem_graph_iff, Etale.proj_mk, Etale.val_mk, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨c, ⟨⟨y.2, h1⟩, h2⟩, rfl⟩`. Introduce and unpack `⟨c', ⟨⟨_, h1⟩, h2⟩, rfl⟩`. Conclude with `⟨h1, h2⟩`.

Use `show IsOpen ((fun p : O × ℂ => Etale.mk P p.1.1 (f p.1.1 + p.2)) ⁻¹' ((fun y => Etale.mk P y (g y)) '' O'))`. Rewrite using `[this]`. Conclude with `isOpen_iUnion fun c => (hU c).prod (isOpen_discrete _) }`. Use `IsEvenlyCovered.to_isEvenlyCovered_preimage (I := ℂ) ⟨inferInstance, O, hxO, hO, hO.preimage hproj, H, fun e => rfl⟩` and prove the remaining obligations.
-/
theorem GlobalTheory.PrimLift.Etale.isCoveringMap_proj
    {X : Type} [TopologicalSpace X] (P : Set X → (X → ℂ) → Prop)
    (hopen : ∀ O f, P O f → IsOpen O)
    (hmono : ∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f)
    (hadd : ∀ O f (c : ℂ), P O f → P O (fun y => f y + c))
    (hcov : ∀ x, ∃ O f, x ∈ O ∧ P O f)
    (heq : ∀ O f g, P O f → P O g → IsOpen {y | y ∈ O ∧ f y = g y}) :
    IsCoveringMap (GlobalTheory.PrimLift.Etale.proj P) := by
  have hproj := continuous_proj hopen hmono hadd hcov
  intro x
  obtain ⟨O, f, hxO, hP⟩ := hcov x
  letI : TopologicalSpace ℂ := ⊥
  haveI : DiscreteTopology ℂ := ⟨rfl⟩
  have hO : IsOpen O := hopen _ _ hP
  let H : Etale.proj P ⁻¹' O ≃ₜ O × ℂ :=
    { toFun := fun e => (⟨Etale.proj P e.1, e.2⟩, e.1.val - f (Etale.proj P e.1))
      invFun := fun p => ⟨Etale.mk P p.1.1 (f p.1.1 + p.2), p.1.2⟩
      left_inv := by
        intro e
        apply Subtype.ext
        show Etale.mk P _ _ = e.1
        rw [add_sub_cancel]
        rfl
      right_inv := by
        intro p
        ext <;> simp
      continuous_toFun := by
        refine Continuous.prodMk ?_ ?_
        · exact (hproj.comp continuous_subtype_val).subtype_mk _
        · rw [continuous_discrete_rng]
          intro c
          have hG := Etale.isOpen_graph (hadd _ _ c hP)
          convert hG.preimage continuous_subtype_val using 1
          ext e
          simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_graph_iff]
          constructor
          · intro h
            refine ⟨e.2, ?_⟩
            rw [← h]
            ring
          · rintro ⟨_, h⟩
            rw [h]
            ring
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_generateFrom_iff.mpr
        rintro S ⟨O', g, hP'', rfl⟩
        have hU : ∀ c : ℂ, IsOpen {y : O | (y : X) ∈ O ∩ O' ∧ f y + c = g y} := by
          intro c
          have hOO' : IsOpen (O ∩ O') := hO.inter (hopen _ _ hP'')
          have h1 : P (O ∩ O') (fun y => f y + c) :=
            hmono _ _ _ (hadd _ _ c hP) hOO' Set.inter_subset_left
          have h2 : P (O ∩ O') g := hmono _ _ _ hP'' hOO' Set.inter_subset_right
          exact (heq _ _ _ h1 h2).preimage continuous_subtype_val
        have : (fun p : O × ℂ => Etale.mk P p.1.1 (f p.1.1 + p.2)) ⁻¹'
            ((fun y => Etale.mk P y (g y)) '' O') =
            ⋃ c : ℂ, {y : O | (y : X) ∈ O ∩ O' ∧ f y + c = g y} ×ˢ {c} := by
          ext ⟨y, c⟩
          simp only [Set.mem_preimage, mem_graph_iff, Etale.proj_mk, Etale.val_mk, Set.mem_iUnion,
            Set.mem_prod, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨c, ⟨⟨y.2, h1⟩, h2⟩, rfl⟩
          · rintro ⟨c', ⟨⟨_, h1⟩, h2⟩, rfl⟩
            exact ⟨h1, h2⟩
        show IsOpen ((fun p : O × ℂ => Etale.mk P p.1.1 (f p.1.1 + p.2)) ⁻¹'
            ((fun y => Etale.mk P y (g y)) '' O'))
        rw [this]
        exact isOpen_iUnion fun c => (hU c).prod (isOpen_discrete _) }
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := ℂ)
    ⟨inferInstance, O, hxO, hO, hO.preimage hproj, H, fun e => rfl⟩
