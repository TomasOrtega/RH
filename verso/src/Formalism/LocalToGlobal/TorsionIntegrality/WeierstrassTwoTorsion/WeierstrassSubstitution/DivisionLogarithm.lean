import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementO
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

/- English proof (translation)
Introduce `R _ W n hn`. Take `⟨hcc, hc1⟩` from `(zSerSpec R W).1 n`. Establish `hu : IsUnit (coeff 1 (zSer W n))` using `by rw [hc1]; exact hn`. Take `⟨h0, hr, hl, h1, -, -⟩` from `compInvSpec R (zSer W n) hcc hu`. Use `⟨h0, ?_, hr, hl, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[hc1]`. Rewrite using `[mul_comm]`. Conclude with `h1`. Introduce `S _ φ`. Establish `key` using `compInvMap R S φ (zSer W n) hcc hu`.

Rewrite `key` using `[zSerMap R S φ W n]`. Conclude with `key`. Introduce `h2`. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem division_spec : DivSpec.{u, v} := by
  intro R _ W n hn
  obtain ⟨hcc, hc1⟩ := (zSerSpec R W).1 n
  have hu : IsUnit (coeff 1 (zSer W n)) := by rw [hc1]; exact hn
  obtain ⟨h0, hr, hl, h1, -, -⟩ := compInvSpec R (zSer W n) hcc hu
  refine ⟨h0, ?_, hr, hl, ?_, ?_⟩
  · rw [hc1] at h1
    rw [mul_comm]; exact h1
  · intro S _ φ
    have key := compInvMap R S φ (zSer W n) hcc hu
    rw [zSerMap R S φ W n] at key
    exact key
  · intro h2
    subst h2
    rfl

section Double

variable {A : Type u} [CommRing A]

end Double

end Formalism.L2.Th1.A
