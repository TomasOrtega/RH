import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtaleStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OEndDegree

/- English proof (translation)
Introduce `E _ _ k _ _ _ A _ act g hB hg d a`. Use `haveI := hB.comm`. Use `haveI : GeometricallyIntegral A.hom := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected`. Use `haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom`. Take `⟨H, m, s, c, hH, hs, hc, hsec⟩` from `GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback E k A act g hB hg d a`.

Take `⟨C, hC⟩` from `GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale k A.left A.hom g hg H m s hH hs`. Use `⟨C * c ^ g, fun n K hn hb => ?_⟩` and prove the remaining obligations. Establish `hK : 1 ≤ K`. Break down `Nat.eq_zero_or_pos K with rfl | h` into its components or cases. It suffices to derive a contradiction.

Apply `hb` to reduce the goal to its premises. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `hn i` as an intermediate fact. Rewrite `this` using `[Nat.le_zero, Int.natAbs_eq_zero]`. Rewrite using `[this, zero_smul]`.

Conclude with `h`. Take `⟨hfin, het, hker⟩` from `GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero E k A act g hB hg _ hb`. Use `⟨hker, ?_⟩` and prove the remaining obligations. Establish `hrank` using `GlobalTheory.finrank_eq_card_kernel_points_of_etale k A hB (act.act (∑ i, n i • a i))`. Establish `hφ : (act.act (∑ i, n i • a i)).left ≫ A.hom = A.hom` using `Over.w _`.

Establish `hq : 1 ≤ c * K ^ 2` using `Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))`. Establish `h` using `hC (act.act (∑ i, n i • a i)).left hφ _ (c * K ^ 2) hq hrank (hsec n K hK hn)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_ker_le : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  obtain ⟨H, m, s, c, hH, hs, hc, hsec⟩ := GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback E k A act g hB hg d a
  obtain ⟨C, hC⟩ := GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale k A.left A.hom g hg H m s hH hs
  refine ⟨C * c ^ g, fun n K hn hb => ?_⟩
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · exfalso; apply hb
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hn i
      rw [Nat.le_zero, Int.natAbs_eq_zero] at this
      rw [this, zero_smul]
    · exact h
  obtain ⟨hfin, het, hker⟩ := GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero E k A act g hB hg _ hb
  refine ⟨hker, ?_⟩
  have hrank := GlobalTheory.finrank_eq_card_kernel_points_of_etale k A hB (act.act (∑ i, n i • a i))
  have hφ : (act.act (∑ i, n i • a i)).left ≫ A.hom = A.hom := Over.w _
  have hq : 1 ≤ c * K ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have h := hC (act.act (∑ i, n i • a i)).left hφ _ (c * K ^ 2) hq hrank (hsec n K hK hn)
  calc _ ≤ C * (c * K ^ 2) ^ g := h
    _ = C * c ^ g * K ^ (2 * g) := by ring

end GlobalTheory.OEndDegree
