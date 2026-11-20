import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.PartSupp

open Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

/- English proof (translation)
Introduce `k`. Take `⟨m, hm, hc, s, hs, h⟩` from `hz k`. Conclude with `⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩`.
-/
theorem zeroAt_mul_left (D : Formalism.BasicNotions.D7) {q : ℕ} {e z : AE D} (he : e ∈ OhE D) (hz : ZeroAt D q z) :
    ZeroAt D q (e * z) := by
  intro k
  obtain ⟨m, hm, hc, s, hs, h⟩ := hz k
  exact ⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩

/- English proof (translation)
Introduce `i j`. Use `zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `show cutM _ _ _ i j - _ = _`. Rewrite using `[cutM_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trivAt_part_of_trivAt (D : Formalism.BasicNotions.D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ}
    (h : TrivAt D q (g : GL (Fin N) (AE D))) : TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

/- English proof (translation)
Introduce `{D} {_} P y hy q hq h` and use `trivAt_part_of_trivAt D P y (hy q hq h)`.
-/
theorem suppInert_part_of_suppInert : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N),
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun {D} {_} P y hy q hq h => trivAt_part_of_trivAt D P y (hy q hq h)

end GlobalTheory.NormSum.PartSupp
