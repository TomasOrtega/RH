import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.L2.Col

/- English proof (translation)
Establish `hY : ∀ j, j ≤ R.m → R.rankY j ≤ R.N R.m`. Introduce `j hj`. Establish `: j * R.t ≤ R.m * R.t` using `Nat.mul_le_mul_right _ hj`. Unfold `Ranks.rankY Ranks.r Ranks.N`. Rewrite using `[mul_add, mul_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hm` using `R.two_le_m`. Simplify using `only [gamRanks, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hn`. Break down `hn with ⟨j, hj, rfl⟩ | rfl | rfl | rfl` into its components or cases. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hj.2) _`.

Conclude with `hY _ le_rfl`. Conclude with `hY _ (Nat.sub_le _ _)`. Simplify `hY 1 (by omega)` using `[Ranks.rankY, Ranks.nV]`.
-/
theorem le_N_of_mem_gamRanks (R : Ranks) {n : ℕ} (hn : n ∈ gamRanks R) : n ≤ R.N R.m := by
  have hY : ∀ j, j ≤ R.m → R.rankY j ≤ R.N R.m := by
    intro j hj
    have : j * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ hj
    unfold Ranks.rankY Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have hm := R.two_le_m
  simp only [gamRanks, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj.2) _
  · exact hY _ le_rfl
  · exact hY _ (Nat.sub_le _ _)
  · simpa [Ranks.rankY, Ranks.nV] using hY 1 (by omega)

/- English proof (translation)
Introduce `X R hX M hM`. Establish `hE : Module.finrank ℚ X.E = 2 * X.f`. Rewrite using `[← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]`. Use `DGam_dvd (posStar_of_ok hX) R fun a ha => ?_` and prove the remaining obligations. Take `⟨n, hn, N, h1, -, rfl⟩` from `Set.mem_iUnion₂.1 ha`.

Use `haveI := autO_finite (posStar_of_ok hX) h1`. Use `GlobalTheory.DGamOnRecord.card_dvd_of_minkMult hM ?_ _` and prove the remaining obligations. Rewrite using `[hE]`. Conclude with `Nat.mul_le_mul_left _ (le_N_of_mem_gamRanks R hn)`.
-/
theorem DGam_dvd_of_minkMult : ∀ {X : Fields} (R : Ranks), X.Ok →
    ∀ M, Formalism.MainNotions.MinkMult (2 * X.f * R.N R.m) M → DGam X.E R ∣ M := by
  intro X R hX M hM
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  refine DGam_dvd (posStar_of_ok hX) R fun a ha => ?_
  obtain ⟨n, hn, N, h1, -, rfl⟩ := Set.mem_iUnion₂.1 ha
  haveI := autO_finite (posStar_of_ok hX) h1
  refine GlobalTheory.DGamOnRecord.card_dvd_of_minkMult hM ?_ _
  rw [hE]
  exact Nat.mul_le_mul_left _ (le_N_of_mem_gamRanks R hn)

end GlobalTheory.Mem.Col2
