import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqMulOfQuadraticBoundNormalLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.Mum.PosMult

/- English proof (translation)
Introduce `R _ P a`. Use `P.isAb.proper` as an intermediate fact. Establish `hL` using `P.isLB`. Establish `hA : IsAmpleLB P.L` using `isAmpleLB_of_relAmple_of_isAffine P.A hL P.ample`. Establish `hNb : (LB.LinComb P.L (K` using `Fin 1) ![a.left] ![-1]).IsLB := LB.isLB_linComb hL _ _`.

Take `⟨n₀, hn₀⟩` from `Filter.eventually_atTop.1 (hA.eventually_isAmpleLB_tens_lbPow_succ hNb)`. Use `⟨n₀ + 1, fun N hN => ?_⟩` and prove the remaining obligations. Establish `key` using `hn₀ (N - 1) (by omega)`. Establish `hN1 : N - 1 + 1 = N` using `by omega`. Rewrite `key` using `[hN1]`.

Establish `hM` using `LB.isLB_linComb hL (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]`. Rewrite using `[relAmple_iff_isAmpleLB_of_isAffine P.A hM]`. Use `key.of_lbIso hM ((cls_eq_iff hM (isLB_tens hNb (isLB_lbPow hL N))).1 ?_)` and prove the remaining obligations. Rewrite using `[cls_tens hNb (isLB_lbPow hL N), cls_lbPow hL, cls_linComb hL, cls_linComb hL]`. Simplify using `[Fin.sum_univ_two, pull_id]`.

Normalize the expressions using the abelian group laws.
-/
theorem eventually_relAmple : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (a : P.A ⟶ P.A), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]) := by
  intro R _ P a
  have := P.isAb.proper
  have hL := P.isLB
  have hA : IsAmpleLB P.L := isAmpleLB_of_relAmple_of_isAffine P.A hL P.ample
  have hNb : (LB.LinComb P.L (K := Fin 1) ![a.left] ![-1]).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hA.eventually_isAmpleLB_tens_lbPow_succ hNb)
  refine ⟨n₀ + 1, fun N hN => ?_⟩
  have key := hn₀ (N - 1) (by omega)
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1] at key
  have hM := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM]
  refine key.of_lbIso hM ((cls_eq_iff hM (isLB_tens hNb (isLB_lbPow hL N))).1 ?_)
  rw [cls_tens hNb (isLB_lbPow hL N), cls_lbPow hL, cls_linComb hL, cls_linComb hL]
  simp [Fin.sum_univ_two, pull_id]
  abel

/- English proof (translation)
Introduce `R _ _ _ hR D a a' h h' _`. Take `⟨N₀, hN₀⟩` from `eventually_relAmple R D.toPre.P a`. Take `⟨C, hC⟩` from `GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound D.toPre.X h h'`. Use `⟨max N₀ (C + 1), le_trans (by omega) (le_max_right _ _), hN₀ _ (le_max_left _ _), ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.exists_pow_eq_mul_of_quadraticBound_normalLocal R hR D.toPre.X h h' C hC _ (le_max_right _ _)`.
-/
theorem exists_pos_mult : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧ ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR D a a' h h' _
  obtain ⟨N₀, hN₀⟩ := eventually_relAmple R D.toPre.P a
  obtain ⟨C, hC⟩ := GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound D.toPre.X h h'
  refine ⟨max N₀ (C + 1), le_trans (by omega) (le_max_right _ _), hN₀ _ (le_max_left _ _), ?_⟩
  exact GlobalTheory.T.exists_pow_eq_mul_of_quadraticBound_normalLocal R hR D.toPre.X h h' C hC _ (le_max_right _ _)

end GlobalTheory.Mum.PosMult
