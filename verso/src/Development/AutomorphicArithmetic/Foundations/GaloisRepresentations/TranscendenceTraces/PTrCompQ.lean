import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hHl hC hWC l _ n i W Z S r p _ _ w' w hr hp hl`. Establish `hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤))`. Simplify using `using hl.map p.appTop.hom`. Establish `hcomp : trHl l (r ≫ p) (Wt.mul r w' w) n i = trHl l p w n i ∘ₗ trHl l r w' n i`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hlk : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤))`.

Rewrite using `[Nat.cast_pow]`. Conclude with `hl.pow k`. Rewrite using `[LinearMap.comp_apply, hHl l n i p w hp hl, hHl l n i r w' hr hlZ, hHl l n i (r ≫ p) _ (hWC r p w' w hr hp) hl]`. Conclude with `hC (l ^ k) n i r p w' w hr hp hlk _`. Unfold `trHQ`.

Rewrite using `[hcomp, LinearMap.baseChange_comp]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trCompQ_of :
    TrHl → TrComp → WtComp → TrCompQ := by
  intro hHl hC hWC l _ n i W Z S r p _ _ w' w hr hp hl
  have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
    simpa using hl.map p.appTop.hom
  have hcomp : trHl l (r ≫ p) (Wt.mul r w' w) n i = trHl l p w n i ∘ₗ trHl l r w' n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hlk : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    rw [LinearMap.comp_apply, hHl l n i p w hp hl, hHl l n i r w' hr hlZ,
      hHl l n i (r ≫ p) _ (hWC r p w' w hr hp) hl]
    exact hC (l ^ k) n i r p w' w hr hp hlk _
  unfold trHQ
  rw [hcomp, LinearMap.baseChange_comp]
