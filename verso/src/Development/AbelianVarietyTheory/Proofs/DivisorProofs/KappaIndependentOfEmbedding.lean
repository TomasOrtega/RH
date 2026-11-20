import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Establish `hτ : toGG D (Sum.inl τ) ∈ D.R.Psi` using `(D.eTau τ).2`. Establish `h1 : toGG D (Sum.inl τ) * g ∈ D.R.Psi ↔ g ∈ D.R.Psi` using `Subgroup.mul_mem_cancel_left _ hτ`. Establish `h2 : toGG D (Sum.inl τ) * g * D.R.cc ∈ D.R.Psi ↔ g * D.R.cc ∈ D.R.Psi`. Rewrite using `[mul_assoc]`. Conclude with `Subgroup.mul_mem_cancel_left _ hτ`.

Unfold `ofGG`. Distinguish the cases in `hg : g ∈ D.R.Psi`. Rewrite using `[dif_pos hg, dif_pos (h1.2 hg)]`. Both sides reduce to the same expression. Rewrite using `[dif_neg hg, dif_neg (fun h => hg (h1.1 h))]`.

Distinguish the cases in `hc : g * D.R.cc ∈ D.R.Psi`. Rewrite using `[dif_pos hc, dif_pos (h2.2 hc)]`. Both sides reduce to the same expression. Rewrite using `[dif_neg hc, dif_neg (fun h => hc (h2.1 h))]`.
-/
theorem elim_ofGG_translate (D : D7) (a b : ℝ) (τ : D.what₂.Tau) (g : D.R.GG) :
    (ofGG D (toGG D (Sum.inl τ) * g)).elim (fun _ => a) (fun _ => b) =
      (ofGG D g).elim (fun _ => a) (fun _ => b) := by
  have hτ : toGG D (Sum.inl τ) ∈ D.R.Psi := (D.eTau τ).2
  have h1 : toGG D (Sum.inl τ) * g ∈ D.R.Psi ↔ g ∈ D.R.Psi :=
    Subgroup.mul_mem_cancel_left _ hτ
  have h2 : toGG D (Sum.inl τ) * g * D.R.cc ∈ D.R.Psi ↔
      g * D.R.cc ∈ D.R.Psi := by
    rw [mul_assoc]; exact Subgroup.mul_mem_cancel_left _ hτ
  unfold ofGG
  by_cases hg : g ∈ D.R.Psi
  · rw [dif_pos hg, dif_pos (h1.2 hg)]; rfl
  · rw [dif_neg hg, dif_neg (fun h => hg (h1.1 h))]
    by_cases hc : g * D.R.cc ∈ D.R.Psi
    · rw [dif_pos hc, dif_pos (h2.2 hc)]; rfl
    · rw [dif_neg hc, dif_neg (fun h => hc (h2.1 h))]

/- English proof (translation)
Introduce `D Y p τ τ'`. Unfold `kap frobEmb`. Simplify using `only [elim_ofGG_translate]`.
-/
theorem kap_indep : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (p : ℕ) (τ τ' : D.what₂.Tau),
    kap Y p τ = kap Y p τ' := by
  intro D Y p τ τ'
  unfold kap frobEmb
  simp only [elim_ofGG_translate]

end GlobalTheory.Mean4
