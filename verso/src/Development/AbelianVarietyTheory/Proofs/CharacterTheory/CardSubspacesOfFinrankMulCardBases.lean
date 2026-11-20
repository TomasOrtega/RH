import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.SubspaceNumber

/- English proof (translation)
Use `symm`. Establish `hspan : ∀ t : Fin a → W, LinearIndependent F t → Submodule.span F (Set.range (W.subtype ∘ t)) = W`. Introduce `t ht`. Establish `h1 : Submodule.span F (Set.range t) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises.

Rewrite using `[finrank_span_eq_card ht, Fintype.card_fin, hW]`. Rewrite using `[Set.range_comp, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_subtype]`. Use `Nat.card_congr (Equiv.ofBijective (fun t => ⟨⟨W.subtype ∘ t.1, t.2.map' _ W.ker_subtype⟩, hspan t.1 t.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `t u h`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrFun (congrArg (fun x => x.1.1) h) i`. Introduce and unpack `⟨⟨s, hs⟩, h⟩`. Establish `hm : ∀ i, s i ∈ W` using `fun i => by`.

Rewrite using `[← h]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Conclude with `⟨⟨fun i => ⟨s i, hm i⟩, LinearIndependent.of_comp W.subtype hs⟩, rfl⟩`.
-/
theorem card_fibre {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (a : ℕ) (W : Submodule F V) (hW : Module.finrank F W = a) :
    Nat.card {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} = Nat.card {t : Fin a → W // LinearIndependent F t} := by
  symm
  have hspan : ∀ t : Fin a → W, LinearIndependent F t →
      Submodule.span F (Set.range (W.subtype ∘ t)) = W := by
    intro t ht
    have h1 : Submodule.span F (Set.range t) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card ht, Fintype.card_fin, hW]
    rw [Set.range_comp, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_subtype]
  refine Nat.card_congr (Equiv.ofBijective
    (fun t => ⟨⟨W.subtype ∘ t.1, t.2.map' _ W.ker_subtype⟩, hspan t.1 t.2⟩) ⟨?_, ?_⟩)
  · intro t u h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg (fun x => x.1.1) h) i
  · rintro ⟨⟨s, hs⟩, h⟩
    have hm : ∀ i, s i ∈ W := fun i => by
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨⟨fun i => ⟨s i, hm i⟩, LinearIndependent.of_comp W.subtype hs⟩, rfl⟩

/- English proof (translation)
Introduce `F _ _ V _ _ _ a ha`. Use `haveI : Fintype F := Fintype.ofFinite F`. Use `haveI : Finite V := Module.finite_of_finite F`. Use `haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective`. Use `haveI : Fintype {W : Submodule F V // Module.finrank F W = a} := Fintype.ofFinite _`.

Set `f : {s : Fin a → V // LinearIndependent F s} → {W : Submodule F V // Module.finrank F W = a}` to `fun s => ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩`. Establish `hfib : ∀ W, Nat.card {s // f s = W} = ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i)`. Introduce and unpack `⟨W, hW⟩`. Establish `e : {s // f s = ⟨W, hW⟩} ≃ {s : {s : Fin a → V // LinearIndependent F s} // Submodule.span F (Set.range s.1) = W}` using `Equiv.subtypeEquivRight (fun s => Subtype.ext_iff)`. Rewrite using `[Nat.card_congr e, card_fibre a W hW, card_linearIndependent hW.ge, hW, Finset.prod_range, Nat.card_eq_fintype_card]`.

Establish `h` using `card_linearIndependent (K := F) (V := V) ha`. Rewrite `h` using `[← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]`. Rewrite `h` using `[hfib]`. Rewrite `h` using `[Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]`. Rewrite using `[h, Finset.prod_range]`.
-/
theorem card_subspaces_mul :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V →
      Nat.card {W : Submodule F V // Module.finrank F W = a} *
        ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) =
      ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  intro F _ _ V _ _ _ a ha
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // Module.finrank F W = a} := Fintype.ofFinite _
  let f : {s : Fin a → V // LinearIndependent F s} →
      {W : Submodule F V // Module.finrank F W = a} := fun s =>
    ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfib : ∀ W, Nat.card {s // f s = W} =
      ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) := by
    rintro ⟨W, hW⟩
    have e : {s // f s = ⟨W, hW⟩} ≃ {s : {s : Fin a → V // LinearIndependent F s} //
      Submodule.span F (Set.range s.1) = W} :=
      Equiv.subtypeEquivRight (fun s => Subtype.ext_iff)
    rw [Nat.card_congr e, card_fibre a W hW, card_linearIndependent hW.ge, hW,
      Finset.prod_range, Nat.card_eq_fintype_card]
  have h := card_linearIndependent (K := F) (V := V) ha
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma] at h
  simp_rw [hfib] at h
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [h, Finset.prod_range]

end GlobalTheory.SubspaceNumber
