import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDegPosAndSumLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.TypePrimesQD

/- English proof (translation)
Establish `hpos : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Establish `hfin : (placesOver E l).Finite` using `Set.finite_of_ncard_pos (by omega)`. Take `⟨hdpos, hsum⟩` from `GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl`. Establish `hle` using `hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)`. Establish `hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v`.

Use `Finset.sum_le_sum fun v hv => ?_` and prove the remaining obligations. Establish `h2` using `hram v (hfin.mem_toFinset.1 hv)`. Establish `hp` using `hdpos v`. Unfold `Formalism.MainNotions.N.locDeg at hp ⊢`. Rewrite `hp`, the goal using `[h2]`.

Use linear arithmetic over natural numbers and integers. Rewrite `hge` using `[Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_split_of_ram_two (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2)
    (hsplit : (placesOver E l).ncard = Module.finrank ℚ E) : False := by
  classical
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (placesOver E l).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨hdpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl
  have hle := hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)
  have hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have h2 := hram v (hfin.mem_toFinset.1 hv)
    have hp := hdpos v
    unfold Formalism.MainNotions.N.locDeg at hp ⊢
    rw [h2] at hp ⊢
    omega
  rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit] at hge
  omega

/- English proof (translation)
Introduce `D h1 i hl`. Establish `key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k`. Introduce `k hk`. Establish `hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ)`. Apply the tactic sequence `rcases hl with h | h <;> simp [h]`.

Establish `hram` using `(h1 _ hmem).2`. Rewrite `hram` using `[hk]`. Conclude with `not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k) (fun v hv => (hram v hv).1) (D.nd.g_split k)`. Conclude with `⟨key 0, key 1⟩`.
-/
theorem qd_ne_typePrimes : ∀ (D : D7), Formalism.MainNotions.EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  intro D h1 i hl
  have key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k := by
    intro k hk
    have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
      rcases hl with h | h <;> simp [h]
    have hram := (h1 _ hmem).2
    rw [hk] at hram
    exact not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k)
      (fun v hv => (hram v hv).1) (D.nd.g_split k)
  exact ⟨key 0, key 1⟩

end GlobalTheory.Proof.TypePrimesQD
