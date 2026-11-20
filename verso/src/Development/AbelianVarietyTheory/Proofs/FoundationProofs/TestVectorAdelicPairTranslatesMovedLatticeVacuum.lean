import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactorStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.Expand
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.expand

/- English proof (translation)
Introduce `D cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'`. Break down `Nat.eq_zero_or_pos Q with hQ | hQ` into its components or cases. Conclude with `⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩`. Establish `hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L`. Introduce `N g L hL`.

Take `⟨Lt, h1, -⟩` from `GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N`. Establish `: L = Lt g`. Use extensionality with `x`. Rewrite using `[hL x, (h1 g).1 x]`. Rewrite using `[this]`.

Conclude with `(h1 g).2`. Establish `hSD0 : ∀ N : ℕ, SD D (stdL D N)`. Introduce `N`. Take `⟨Lt, h1, h2, -⟩` from `GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N`. Rewrite using `[← h2]`.

Conclude with `(h1 1).2`. Take `⟨-, hW, hint, -⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)`. Take `⟨-, -, -, -, -, -, hq⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁') (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)`. Establish `he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d)` using `P.vac.1`. Establish `hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0`.

Introduce `x hx`. Rewrite using `[hW x hx]`. Use function extensionality and compare the values at `z`. Conclude with `he0.2 x hx z`. Establish `heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d` using `⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩`.

Take `⟨c, hc1, hc2, hc3⟩` from `GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor D cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g' L₁ L₁' hL hL'`. Take `⟨k, r, z, hz, hr1, hr2, hF⟩` from `P.pres`. Establish `hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d`. Introduce `i`. Use `⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩` from `hint x hx _ (hz i)`. Rewrite `hm` using `[Hf_nsmul_right, ← Hf_nsmul_left]`. Rewrite using `[Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]`. Establish `hQc : (Q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hQ.ne'`. Establish `key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧ P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) = Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0)`.

Introduce `i`. Take `⟨B, hB, h⟩` from `approx_La (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1.1 _ _ hL hL' (hz i)`. Take `⟨m, hm, hl⟩` from `P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT`. Take `⟨B', h1, h2⟩` from `h (m * Q) (by positivity)`. Use `⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]`. Conclude with `h1`. Rewrite using `[← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hQc, one_smul]`. Use `choose y hy1 hy2 using key`. Establish `hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧ ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1`.

Introduce `i`. Take `⟨m, hm⟩` from `hq _ (hy1 i)`. Conclude with `root_unity (by positivity) (wdPh_pow _ m hm)`. Use `choose u hu1 hu2 hu3 using hu`. Use `⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩` and prove the remaining obligations.

Rewrite using `[← mul_assoc]`. Conclude with `(hr1 i).mul (hu2 i)`. Simplify `hr2 ρ` using `only [map_mul, norm_mul, hu3, mul_one]`. Establish `hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0`. Rewrite using `[hF]`.

Use function extensionality and compare the values at `w`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]`. Use function extensionality and compare the values at `w`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.coe_mul, hu1]`. Simplify using `only [Wd, U]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_expand : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  intro D cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩
  have hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L := by
    intro N g L hL
    obtain ⟨Lt, h1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    have : L = Lt g := by
      ext x; rw [hL x, (h1 g).1 x]
    rw [this]; exact (h1 g).2
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  obtain ⟨-, -, -, -, -, -, hq⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)
  have he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d) := P.vac.1
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor D cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g'
    L₁ L₁' hL hL'
  obtain ⟨k, r, z, hz, hr1, hr2, hF⟩ := P.pres
  have hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d := by
    intro i
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ (hz i)
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧
      P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) =
        Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0) := by
    intro i
    obtain ⟨B, hB, h⟩ := approx_La (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1.1 _ _ hL hL' (hz i)
    obtain ⟨m, hm, hl⟩ := P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT
    obtain ⟨B', h1, h2⟩ := h (m * Q) (by positivity)
    refine ⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩
    · rw [pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]; exact h1
    · rw [← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hQc, one_smul]
  choose y hy1 hy2 using key
  have hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧
      ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hq _ (hy1 i)
    exact root_unity (by positivity) (wdPh_pow _ m hm)
  choose u hu1 hu2 hu3 using hu
  refine ⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩
  · rw [← mul_assoc]; exact (hr1 i).mul (hu2 i)
  · simpa only [map_mul, norm_mul, hu3, mul_one] using hr2 ρ
  · have hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 := by
      rw [hF]; funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_mul, hu1]
    simp only [Wd, U]
    ring

end GlobalTheory.ArchFree.expand
