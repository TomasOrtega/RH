import Formalism.EllipticTorsion.Statement

namespace Formalism.ELL

/- English proof (translation)
Introduce `K _ l`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;>`. Apply the tactic sequence `simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring`.
-/
theorem legendre_invariant : LegendreInv := by
  intro K _ l
  refine ⟨?_, ?_⟩ <;>
  simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

/- English proof (translation)
Introduce `K _ a`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;>`. Apply the tactic sequence `simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring`.
-/
theorem deuring_invariant : DeuringInv := by
  intro K _ a
  refine ⟨?_, ?_⟩ <;>
  simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

end Formalism.ELL
