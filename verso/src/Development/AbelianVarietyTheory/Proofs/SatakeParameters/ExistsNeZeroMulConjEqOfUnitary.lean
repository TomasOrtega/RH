import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryUnramifiedUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterCmInfinityType

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.NormOneHilbert90Units

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hz : (z : D.host.E) * star (z : D.host.E) = 1` using `z.2.2`. Establish `key : ∀ a : D.host.E, (z : D.host.E) * star (a + (z : D.host.E) * star a) = a + (z : D.host.E) * star a`. Introduce `a`. Rewrite using `[star_add, star_mul, star_star]`. Take the linear combination `a * hz`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : D.host.E, star x ≠ x := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `NumberField.IsCMField.complexConj_ne_one D.host.E` to reduce the goal to its premises. Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[← Formalism.BasicNotions.Examples₂.cmStar_apply]`. Conclude with `h x`. Distinguish the cases in `h1 : (1 : D.host.E) + (z : D.host.E) * star (1 : D.host.E) = 0`. Use `⟨x + (z : D.host.E) * star x, ?_, ?_⟩` and prove the remaining obligations. Introduce `h2`.

Establish `hz1 : (z : D.host.E) = -1` using `by rw [star_one] at h1; linear_combination h1`. Rewrite `h2` using `[hz1]`. Conclude with `hx (by linear_combination -h2)`. Rewrite using `[← Formalism.BasicNotions.Examples₂.star_eq_conj]`. Conclude with `key x`.

Conclude with `⟨_, h1, by rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key 1⟩`.
-/
theorem exists_ne_zero_mul_conj_eq_of_unitary (D : D7) (z : unitary D.host.E) :
    ∃ w : D.host.E, w ≠ 0 ∧ (z : D.host.E) * D.host.conj w = w := by
  have hz : (z : D.host.E) * star (z : D.host.E) = 1 := z.2.2
  have key : ∀ a : D.host.E, (z : D.host.E) * star (a + (z : D.host.E) * star a) = a + (z : D.host.E) * star a := by
    intro a
    rw [star_add, star_mul, star_star]
    linear_combination a * hz
  obtain ⟨x, hx⟩ : ∃ x : D.host.E, star x ≠ x := by
    by_contra h
    push_neg at h
    apply NumberField.IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    rw [← Formalism.BasicNotions.Examples₂.cmStar_apply]
    exact h x
  by_cases h1 : (1 : D.host.E) + (z : D.host.E) * star (1 : D.host.E) = 0
  · refine ⟨x + (z : D.host.E) * star x, ?_, ?_⟩
    · intro h2
      have hz1 : (z : D.host.E) = -1 := by rw [star_one] at h1; linear_combination h1
      rw [hz1] at h2
      exact hx (by linear_combination -h2)
    · rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key x
  · exact ⟨_, h1, by rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key 1⟩

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end Comparison₂

end GlobalTheory.NormOneHilbert90Units
