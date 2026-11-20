import Formalism.EllipticTorsion.Statement

namespace Formalism.ELL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem legendre_invariant : LegendreInv := by
  intro K _ l
  refine ⟨?_, ?_⟩ <;>
  simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem deuring_invariant : DeuringInv := by
  intro K _ a
  refine ⟨?_, ?_⟩ <;>
  simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

end Formalism.ELL
