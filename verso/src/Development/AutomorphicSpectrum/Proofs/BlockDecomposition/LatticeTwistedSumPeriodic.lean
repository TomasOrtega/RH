import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem rt_add_periodic (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    rt (ξ + ξ') = (rt ξ + rt ξ' : Mx D ρ p) := by
  ext i j
  simp [rt, Matrix.map_apply, Matrix.add_apply, map_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem dsum_add_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ : Mx D ρ p → ℂ) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x y : Mx D ρ p) :
    dsum ψ b₀ Φ x (y + rt ξ) = conj (chv ψ b₀ x (rt ξ)) * dsum ψ b₀ Φ x y := by
  obtain ⟨-, h2, h3, -, -, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  unfold dsum
  rw [← tsum_mul_left, ← (Equiv.addRight ξ).tsum_eq
    (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
      conj (chv ψ b₀ x (rt ξ)) * (chv ψ b₀ x (rt η) * Φ (rt η + y)))]
  refine tsum_congr fun η => ?_
  have hn : conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt ξ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3]
    simp
  simp only [Equiv.coe_addRight]
  rw [rt_add_periodic, h2, show rt η + rt ξ + y = rt η + (y + rt ξ) by abel]
  linear_combination (-(chv ψ b₀ x (rt η) * Φ (rt η + (y + rt ξ)))) * hn

/- English proof (translation)
Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem dsum_add_rt_left (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ : Mx D ρ p → ℂ) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x y : Mx D ρ p) :
    dsum ψ b₀ Φ (x + rt ξ) y = dsum ψ b₀ Φ x y := by
  obtain ⟨h1, -, -, -, h5, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  unfold dsum
  refine tsum_congr fun η => ?_
  rw [h1, h5, mul_one]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem ap_periodic (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ φ : Mx D ρ p → ℂ) (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E)
    (v : Mx D ρ p × Mx D ρ p) :
    Ap ψ b₀ Φ φ (v + (rt ξ₁, rt ξ₂)) = Ap ψ b₀ Φ φ v := by
  obtain ⟨-, -, h3, -, -, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  obtain ⟨y, x⟩ := v
  show dsum ψ b₀ Φ (x + rt ξ₂) (y + rt ξ₁) * conj (dsum ψ b₀ φ (x + rt ξ₂) (y + rt ξ₁)) =
    dsum ψ b₀ Φ x y * conj (dsum ψ b₀ φ x y)
  have hn : conj (chv ψ b₀ x (rt ξ₁)) * chv ψ b₀ x (rt ξ₁) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3]
    simp
  rw [dsum_add_rt_left ψ hψ, dsum_add_rt_left ψ hψ, dsum_add_rt ψ hψ, dsum_add_rt ψ hψ, map_mul,
    Complex.conj_conj]
  linear_combination (dsum ψ b₀ Φ x y * conj (dsum ψ b₀ φ x y)) * hn

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ap_periodic_all : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E)
      (v : Mx D ρ p × Mx D ρ p),
      GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v :=
  fun ψ hψ b₀ Φ φ ξ₁ ξ₂ v => ap_periodic ψ hψ b₀ Φ φ ξ₁ ξ₂ v

end GlobalTheory.CompanionTheory.FJE
