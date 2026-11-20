import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X Y u t₁ t₂ h1 h2 h`. Take `⟨l, m, l', m', c⟩` from `t₁`. Take `⟨l₂, m₂, l₂', m₂', c₂⟩` from `t₂`. Simplify using `only at h1 h2`. Substitute `h1 h2` using the available equality.

Establish `hc : c = c₂`. Rewrite using `[← Quot.out_eq c, ← Quot.out_eq c₂]`. Conclude with `Quot.sound h`. Substitute `hc` using the available equality. Both sides reduce to the same expression.
-/
theorem eqC_holds : EqC := by
  intro D X Y u t₁ t₂ h1 h2 h
  obtain ⟨l, m, l', m', c⟩ := t₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := t₂
  simp only at h1 h2
  subst h1 h2
  have hc : c = c₂ := by
    rw [← Quot.out_eq c, ← Quot.out_eq c₂]
    exact Quot.sound h
  subst hc
  rfl
end GlobalTheory.TypeAsm
