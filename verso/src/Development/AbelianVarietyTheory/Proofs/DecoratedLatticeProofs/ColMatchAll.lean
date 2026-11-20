import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

/- English proof (translation)
Introduce `B X I h hX l Z hJ u a`. Establish `KO` using `GlobalTheory.Mem.Col2.KerRat.kernelsOver_of_family I l Z h hJ (GlobalTheory.Core.Ht2.family_laws I h hX l Z) u a`. Use `⟨?_, fun c x φ F z hx hF => ?_⟩` and prove the remaining obligations. Take `⟨⟨b⟩, hb⟩` from `KO.period`. Take `⟨hY, hK, hF, -, -⟩` from `hb b`.

Conclude with `⟨⟨b, hY, hK, hF⟩⟩`. Take `⟨hY, hK, hF', hM, heq⟩` from `KO.period.2 c.b`. Establish `ex : x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ` using `Subtype.ext (funext hx)`. Establish `eF : F = GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a z`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `t p`. Conclude with `hF p`. Substitute `ex` using the available equality. Substitute `eF` using the available equality. Rewrite using `[heq φ z]`.

Both sides reduce to the same expression.
-/
theorem colMatchAll : ColMatchAll := by
  intro B X I h hX l Z hJ u a
  have KO := GlobalTheory.Mem.Col2.KerRat.kernelsOver_of_family I l Z h hJ (GlobalTheory.Core.Ht2.family_laws I h hX l Z) u a
  refine ⟨?_, fun c x φ F z hx hF => ?_⟩
  · obtain ⟨⟨b⟩, hb⟩ := KO.period
    obtain ⟨hY, hK, hF, -, -⟩ := hb b
    exact ⟨⟨b, hY, hK, hF⟩⟩
  · obtain ⟨hY, hK, hF', hM, heq⟩ := KO.period.2 c.b
    have ex : x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ := Subtype.ext (funext hx)
    have eF : F = GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a z := by
      apply Subtype.ext; funext t p; exact hF p
    subst ex; subst eF
    rw [heq φ z]
    rfl

end GlobalTheory.Core.Ht2

end
