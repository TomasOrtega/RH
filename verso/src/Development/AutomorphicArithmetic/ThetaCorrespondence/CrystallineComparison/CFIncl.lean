import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
/- English proof (translation)
Introduce `f`. Establish `e : Per.IsCrisDR l f ↔ Incl.IsCrisDRF (p` using `l) (R := Cmp6.OC l) f := ⟨fun h => ⟨h.on0, h.bdd⟩, fun h => ⟨h.on0, h.bdd⟩⟩`. Rewrite using `[e]`. Conclude with `Incl.incl_F l f`.
-/
theorem crystalline_deRham_inclusion_compat : ∀ f : Per.Bcris l →+* Per.BdR l,
    Per.IsCrisDR l f ↔ Per6.IsCrisDR l (((equivDeRham l).toRingHom.comp f).comp (equivCrystalline l).symm.toRingHom) := by
  intro f
  have e : Per.IsCrisDR l f ↔ Incl.IsCrisDRF (p := l) (R := Cmp6.OC l) f :=
    ⟨fun h => ⟨h.on0, h.bdd⟩, fun h => ⟨h.on0, h.bdd⟩⟩
  rw [e]
  exact Incl.incl_F l f

end Formalism.BasicNotions.CmpTie
