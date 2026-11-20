import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

/- English proof (translation)
Introduce `K G _ _ _ n H ρ`. Establish `h` using `UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)`. Use `Iff.trans ?_ h` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h1 N hN`.

Conclude with `h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv`. Introduce `h1 N hN`. Conclude with `h1 N fun g v hv => hN g g.2 v hv`.
-/
theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
