import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagZ

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hS F _ Ω _ _ K _ _ ι _ y e hP hdim N w b hb k hk Q hQ`. Take `⟨R, hR, hsum⟩` from `psum_eq_sum_hsymm_neg N k hk`. Rewrite using `[hsum, (genNum_linear F K ι (Fin N) (pointIdeal F y) b Q).2.2.1]`. Use `Finset.sum_eq_zero fun a ha => ?_` and prove the remaining obligations. Take `⟨ha1, hak⟩` from `Finset.mem_Icc.mp ha`.

Rewrite using `[genNum_mul_expand]`. Use `Finset.sum_eq_zero fun μ hμ => ?_` and prove the remaining obligations. Establish `hlen : (classList b μ).length = k - a` using `PositivityTheory.HtPt.Pflag.length_classList_of_hom b (hR a) hμ`. Establish `hl : a + (classList b μ ++ Q).length = e`. Rewrite using `[List.length_append, hlen]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[PositivityTheory.HtPt.Pflag.genNum_neg F K ι (pointIdeal F y) e hP hdim b _ a (PositivityTheory.HtPt.Pflag.isHomogeneous_hsymm_real N a) _ hl, PositivityTheory.HtPt.Pflag.genNum_hsymm, hsymm_dualRoots_triv_numZero hS F Ω K ι y e hP hdim N w b hb a ha1 _ hl]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hdim N w b hb k hk Q hQ
  obtain ⟨R, hR, hsum⟩ := psum_eq_sum_hsymm_neg N k hk
  rw [hsum, (genNum_linear F K ι (Fin N) (pointIdeal F y) b Q).2.2.1]
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  rw [genNum_mul_expand]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : (classList b μ).length = k - a :=
    PositivityTheory.HtPt.Pflag.length_classList_of_hom b (hR a) hμ
  have hl : a + (classList b μ ++ Q).length = e := by
    rw [List.length_append, hlen]
    omega
  rw [PositivityTheory.HtPt.Pflag.genNum_neg F K ι (pointIdeal F y) e hP hdim b _ a
      (PositivityTheory.HtPt.Pflag.isHomogeneous_hsymm_real N a) _ hl,
    PositivityTheory.HtPt.Pflag.genNum_hsymm,
    hsymm_dualRoots_triv_numZero hS F Ω K ι y e hP hdim N w b hb a ha1 _ hl]
  simp
