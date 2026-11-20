import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology

namespace GlobalTheory.JSW.Cut

open Pointwise

variable {F : Type} [NormedField F] {n : ℕ}

/- English proof (translation)
Take `⟨u, hu, k, hk, rfl⟩` from `hx`. Take `⟨u', hu', k', hk', he⟩` from `hy`. Establish `hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Establish `hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹)`.

Combine the equalities or inequalities in the displayed calculation. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, l, hl, rfl⟩`. Use `⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l, mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx']`. Use `group`. Introduce and unpack `⟨v, hv, l, hl, rfl⟩`. Use `⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l, mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩` and prove the remaining obligations. Rewrite using `[hy']`.

Use `group`.
-/
theorem cell_eq_of_mem (B' : Subgroup (GL (Fin n) F)) {x y g : GL (Fin n) F}
    (hx : g ∈ cell x (B' : Set (GL (Fin n) F))) (hy : g ∈ cell y (B' : Set (GL (Fin n) F))) :
    cell x (B' : Set (GL (Fin n) F)) = cell y (B' : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hx
  obtain ⟨u', hu', k', hk', he⟩ := hy
  have hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹) := by
    calc y = u'⁻¹ * (u' * y * k') * k'⁻¹ := by group
      _ = (u'⁻¹ * u) * x * (k * k'⁻¹) := by rw [← he]; group
  have hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹) := by
    calc x = u⁻¹ * (u * x * k) * k⁻¹ := by group
      _ = (u⁻¹ * u') * y * (k' * k⁻¹) := by rw [he]; group
  ext g
  constructor
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l,
      mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩
    rw [hx']; group
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l,
      mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩
    rw [hy']; group

/- English proof (translation)
Take `⟨t, ht⟩` from `hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F))) (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)`. Use `set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS`. Establish `hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F))`. Introduce `x hx`. Take `⟨b, -, rfl⟩` from `Finset.mem_image.1 hx`.

Conclude with `⟨1, one_mem _, b, b.2, by simp⟩`. Establish `hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F))`. Use extensionality with `g`. Simplify using `only [Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, k, hk, rfl⟩`. Take `⟨b, hbt, hkb⟩` from `Set.mem_iUnion₂.1 (ht hk)`. Take `⟨k', hk', hkk⟩` from `hkb`. Use `⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩` and prove the remaining obligations. Rewrite using `[← hkk]`.

Simplify using `[smul_eq_mul, mul_assoc]`. Introduce and unpack `⟨x, hx, u, hu, k, hk, rfl⟩`. Take `⟨b, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩`. Use `set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf`.

Use `set C : Finset (Set (GL (Fin n) F)) := S.image f with hC`. Set `rep : C → GL (Fin n) F` to `fun c => Classical.choose (Finset.mem_image.1 c.2)`. Establish `rep_mem : ∀ c : C, rep c ∈ S` using `fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1`. Establish `rep_eq : ∀ c : C, f (rep c) = c` using `fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2`. Use `⟨C.attach.image rep, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hSmem _ (rep_mem c)`. Rewrite using `[hunion]`. Use extensionality with `g`.

Simplify using `only [Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hg⟩`. Establish `hc : f x ∈ C` using `Finset.mem_image.2 ⟨x, hx, rfl⟩`. Use `⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `rep_eq ⟨f x, hc⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `g ∈ f (rep ⟨f x, hc⟩)`. Rewrite using `[this]`. Conclude with `hg`. Introduce and unpack `⟨x, hx, hg⟩`.

Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `⟨rep c, rep_mem c, hg⟩`. Introduce `x hx y hy hxy`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hx)`. Take `⟨d, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hy)`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `g hgc hgd`. Apply `hxy` to reduce the goal to its premises. Establish `h1` using `cell_eq_of_mem B' hgc hgd`. Establish `hcd : c = d`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← rep_eq c, ← rep_eq d]`. Conclude with `h1`. Rewrite using `[hcd]`.
-/
theorem cell_finite_disjoint_union (B B' : Subgroup (GL (Fin n) F)) (hB : IsCompact (B : Set (GL (Fin n) F)))
    (hB' : IsOpen (B' : Set (GL (Fin n) F))) (hle : B' ≤ B) (h₀ : GL (Fin n) F) :
    ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ cell h₀ (B : Set (GL (Fin n) F))) ∧
      cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, cell x (B' : Set (GL (Fin n) F))) ∧
      (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => cell x (B' : Set (GL (Fin n) F)) := by
  classical

  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F)))
    (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)
  set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS
  have hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F)) := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨1, one_mem _, b, b.2, by simp⟩
  have hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F)) := by
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      obtain ⟨b, hbt, hkb⟩ := Set.mem_iUnion₂.1 (ht hk)
      obtain ⟨k', hk', hkk⟩ := hkb
      refine ⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩
      rw [← hkk]; simp [smul_eq_mul, mul_assoc]
    · rintro ⟨x, hx, u, hu, k, hk, rfl⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩

  set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf
  set C : Finset (Set (GL (Fin n) F)) := S.image f with hC
  let rep : C → GL (Fin n) F := fun c => Classical.choose (Finset.mem_image.1 c.2)
  have rep_mem : ∀ c : C, rep c ∈ S := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1
  have rep_eq : ∀ c : C, f (rep c) = c := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact hSmem _ (rep_mem c)
  · rw [hunion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hg⟩
      have hc : f x ∈ C := Finset.mem_image.2 ⟨x, hx, rfl⟩
      refine ⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      have := rep_eq ⟨f x, hc⟩
      change g ∈ f (rep ⟨f x, hc⟩)
      rw [this]; exact hg
    · rintro ⟨x, hx, hg⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨rep c, rep_mem c, hg⟩
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [Function.onFun, Set.disjoint_left]
    intro g hgc hgd
    apply hxy
    have h1 := cell_eq_of_mem B' hgc hgd
    have hcd : c = d := by
      apply Subtype.ext
      rw [← rep_eq c, ← rep_eq d]
      exact h1
    rw [hcd]

/- English proof (translation)
Introduce `B B' hB hB' hle h₀` and use `cell_finite_disjoint_union B B' hB hB' hle h₀`.
-/
theorem cell_finite_disjoint_union' : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) :=
  fun B B' hB hB' hle h₀ => cell_finite_disjoint_union B B' hB hB' hle h₀

end GlobalTheory.JSW.Cut
