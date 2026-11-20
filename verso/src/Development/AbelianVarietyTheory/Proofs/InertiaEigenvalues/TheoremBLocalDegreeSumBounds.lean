import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDegPosAndSumLe
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.QDDeg

/- English proof (translation)
Introduce `D h1 i hi s hs`. Establish `hl : (D.nd.l i).Prime`. Apply the tactic sequence `rcases hi with h | h <;> rw [h]`. Conclude with `D.host.hyp.1`. Conclude with `D.host.hyp.2.1`.

Establish `hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ)`. Apply the tactic sequence `rcases hi with h | h <;> simp [h]`. Take `⟨hpos, hsum⟩` from `GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le D.host.E (D.nd.l i) hl`. Establish `hfr : Module.finrank ℚ D.host.E = 2 * D.R.f`. Rewrite using `[D.host.finrank_cmField]`.

Unfold `Ranks.f Ranks.n`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(hsum s hs).trans hfr.le, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul, ← Finset.sum_const]`. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations.

Establish `he : w.asIdeal.ramificationIdx ℤ = 2` using `((h1 _ hmem).2 w (hs w hw)).1`. Establish `hp` using `hpos w`. Unfold `Formalism.MainNotions.N.locDeg at hp ⊢`. Rewrite `hp`, the goal using `[he]`. Use linear arithmetic over natural numbers and integers.
-/
theorem locDeg_sum_le_and_ge : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := by
  intro D h1 i hi s hs
  have hl : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  obtain ⟨hpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le D.host.E (D.nd.l i) hl
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  refine ⟨(hsum s hs).trans hfr.le, ?_⟩
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  have he : w.asIdeal.ramificationIdx ℤ = 2 := ((h1 _ hmem).2 w (hs w hw)).1
  have hp := hpos w
  unfold Formalism.MainNotions.N.locDeg at hp ⊢
  rw [he] at hp ⊢
  omega

end GlobalTheory.Proof.QDDeg
