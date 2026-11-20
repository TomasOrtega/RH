import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigAtLeast

noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
  exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Extract witnesses or component facts from the available result. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem sigOK_of (hlt : WittLBlt) (heq : WittLBeq) : SigOK := by
  intro D n V s hr hs
  by_contra hne
  push Not at hne
  choose ε fr hfr hng using hne
  obtain ⟨h1, h2, h3⟩ := hr
  have hb : ∀ τ, V.rank - n ≤ cnt (ε τ) true ∧ V.rank - n ≤ cnt (ε τ) false := by
    intro τ
    have hc := cnt_add (ε τ)
    unfold GoodSig at hng
    have := hng τ
    push Not at this
    obtain ⟨a, b, c, d⟩ := this
    constructor <;> omega
  have hS : SigAtLeast D V (V.rank - n) := fun τ =>
    ⟨ε τ, fr τ, (hfr τ).1, (hfr τ).2.1, (hb τ).1, (hb τ).2⟩
  have hw : V.rank - n ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
    rcases Nat.lt_or_ge (2 * (V.rank - n)) V.rank with h | h
    · exact hlt D V _ h hS
    · exact heq D V _ (by omega) hS
  omega

end PositivityTheory.Rg.Sw.Glob
