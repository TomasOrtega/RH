import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)

variable {n : ℕ}

/- English proof (translation)
Introduce `a b c d`. Establish `h` using `X.gl b a d c`. Simplify using `only [neg_mul_neg]`. Rewrite using `[h]`. Apply the tactic sequence `rcases eq_or_ne a d with h1 | h1 <;> rcases eq_or_ne b c with h2 | h2`.

Substitute `h1` using the available equality. Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Substitute `h1` using the available equality.

Simplify using `[h2, Ne.symm h2]`. Substitute `h2` using the available equality. Simplify using `[h1, Ne.symm h1]`. Simplify using `[h1, h2, Ne.symm h1, Ne.symm h2]`.
-/
theorem glRel_tau (X : GMod n) : GlRel (fun a b => -X.E b a) := by
  intro a b c d
  have h := X.gl b a d c
  simp only [neg_mul_neg]
  rw [h]
  rcases eq_or_ne a d with h1 | h1 <;> rcases eq_or_ne b c with h2 | h2
  · subst h1; subst h2; simp; abel
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1, Ne.symm h1]
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def tauMod (X : GMod n) : GMod n := ⟨X.V, fun a b => -X.E b a, glRel_tau X⟩

def QdetTau : Prop :=
  ∀ (n : ℕ) (X : GMod n) (u : ℂ), qdet (tauMod X).E u = ((-1 : ℂ) ^ n) • qdet X.E (-u + ((n : ℂ) - 1))

end CompanionTheory.RgExh.Hk
