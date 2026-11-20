import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGrowthDualWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedDiagonalAction
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SphericalDual

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Supply the required witnesses or components. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem spherical_whittaker_long_weyl3_transpose_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (GL2LocalData.w3 * GL2LocalData.tinv (dg (unifUnit F ^ a) (unifUnit F ^ b) 1)) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![0, -b, -a]) else 0 := by
  intro F _ _ _ _ ψ₀ hψ₀ z a b
  borelize F
  obtain ⟨k, hk, hdg⟩ := GlobalTheory.CompanionTheory.LocalUnramified.sDg F 1 (unifUnit F ^ (-b)) (unifUnit F ^ (-a))
  have e1 : (GL2LocalData.w3 : GL (Fin 3) F) * GL2LocalData.tinv (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) =
      dg 1 (unifUnit F ^ (-b)) (unifUnit F ^ (-a)) * GL2LocalData.w3 := by
    rw [GlobalTheory.CompanionTheory.GL2Factorization.DualGauge.weyl_transposeInv_diag_GL3, inv_one, _root_.zpow_neg, _root_.zpow_neg]
  have o1 : ord (((1 : Fˣ)) : F) = 0 := by simp [ord]
  rw [ord_unifUnit_zpow, ord_unifUnit_zpow, o1] at hdg
  have hanti : Antitone (![0, -b, -a] : Fin 3 → ℤ) ↔ b ≤ a ∧ 0 ≤ b := by
    constructor
    · intro h
      have h1 := h (show (0 : Fin 3) ≤ 1 by decide)
      have h2 := h (show (1 : Fin 3) ≤ 2 by decide)
      simp at h1 h2
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩ i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
  have hrho : Spherical.rhoPair (![0, -b, -a] : Fin 3 → ℤ) = 2 * a := by
    simp [Spherical.rhoPair, Fin.sum_univ_three]
  have hq : Spherical.sqrtQ F ^ (-(2 * a)) = (residueCard F : ℂ) ^ (-a) := by
    rw [show -(2 * a) = 2 * (-a) by ring, _root_.zpow_mul, zpow_ofNat, Spherical.sqrtQ_sq]
    rfl
  rw [e1, hdg, mul_assoc, Spherical.sphericalWhittaker_mul_right hψ₀ z _
    (mul_mem hk GlobalTheory.CompanionTheory.GL2Factorization.DualGauge.weyl_GL3_mem_integralGL), Spherical.sphericalWhittaker_torusPow hψ₀ z]
  simp only [hanti]
  split_ifs with h
  · rw [Spherical.halfModulus_eq, hrho, hq]
  · rfl

end GlobalTheory.CompanionTheory.SphericalDual
