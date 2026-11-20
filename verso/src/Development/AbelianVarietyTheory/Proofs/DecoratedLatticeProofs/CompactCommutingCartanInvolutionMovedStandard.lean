import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanInStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGramStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanInvolutionEqOfCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.StdUnn.CartanMove

variable {D : D7}

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt, map_mul, Units.val_mul]`.
-/
theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

/- English proof (translation)
Establish `: Formalism.L2.Theta.mt V 1 = 1` using `by simp [Formalism.L2.Theta.mt]`. Rewrite using `[this]`. Conclude with `Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)`.
-/
theorem compAt_mt_one (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this]
  exact Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

/- English proof (translation)
Rewrite using `[mt_mul']`. Conclude with `GlobalTheory.AdForm.RatMove.compAt_mul θ τ _ _`.
-/
theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  rw [mt_mul']
  exact GlobalTheory.AdForm.RatMove.compAt_mul θ τ _ _

/- English proof (translation)
The claim follows from `GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ`.
-/
theorem compAt_isom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
  GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hs`. Establish `hP : Pᴴ * G * P = G`. Combine the equalities or inequalities in the displayed calculation. Establish `hGPi : G * Pi = Pᴴ * G`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = G := by rw [hiso, h2, hP]`.

Establish `e : G * (Pi * s * P) = Pᴴ * (G * s) * P`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Use `h3.conjTranspose_mul_mul_same ?_` and prove the remaining obligations. Introduce `v w hvw`.

Use `congrArg (fun x => Pi.mulVec x) hvw` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hPi]`.
-/
theorem isCartanInv_conj {k : ℕ} {G s P Pi : Matrix (Fin k) (Fin k) ℂ} (hs : IsCartanInv G s)
    (hPi : Pi * P = 1) (hPPi : P * Pi = 1) (hiso : Piᴴ * G * Pi = G) : IsCartanInv G (Pi * s * P) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hP : Pᴴ * G * P = G := by
    calc Pᴴ * G * P = Pᴴ * (Piᴴ * G * Pi) * P := by rw [hiso]
      _ = (Pi * P)ᴴ * G * (Pi * P) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGPi : G * Pi = Pᴴ * G := by
    calc G * Pi = (Pi * P)ᴴ * G * Pi := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = Pᴴ * (Piᴴ * G * Pi) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * G := by rw [hiso]
  refine ⟨?_, ?_, ?_⟩
  · calc Pi * s * P * (Pi * s * P) = Pi * s * (P * Pi) * s * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, Matrix.mul_one, Matrix.mul_assoc Pi s s, h1, Matrix.mul_one, hPi]
  · calc (Pi * s * P)ᴴ * G * (Pi * s * P) = Pᴴ * (sᴴ * (Piᴴ * G * Pi) * s) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hiso, h2, hP]
  · have e : G * (Pi * s * P) = Pᴴ * (G * s) * P := by
      calc G * (Pi * s * P) = G * Pi * s * P := by simp only [Matrix.mul_assoc]
        _ = Pᴴ * (G * s) * P := by rw [hGPi]; simp only [Matrix.mul_assoc]
    rw [e]
    refine h3.conjTranspose_mul_mul_same ?_
    intro v w hvw
    have := congrArg (fun x => Pi.mulVec x) hvw
    simpa [Matrix.mulVec_mulVec, hPi] using this

end GlobalTheory.StdUnn.CartanMove
end

namespace GlobalTheory.StdUnn.CartanMove

open scoped ComplexOrder

/- English proof (translation)
Introduce `D A μ hμ κ hκ a p hp θ hθ sS hsS hcomm`. Take `⟨k₀, hk₀K, hk₀⟩` from `GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv D θ hθ A.rank μ hμ`. Establish `hstd : IsStdInv A μ (fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀)))`. Introduce `τ`. Establish `h` using `hκ (κ.symm k₀)`.

Rewrite `h` using `[κ.apply_symm_apply k₀]`. Establish `h2` using `congrArg (compAt θ τ) h`. Rewrite `h2` using `[GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul]`. Establish `hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ)` using `GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _`. Rewrite `h2` using `[hr, hk₀]`.

Conclude with `h2.symm`. Use `⟨_, hstd, fun τ => ?_⟩` and prove the remaining obligations. Simplify using `only`. Use `set k₁ := κ.symm k₀ with hk₁`. Use `set P := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))) with hPdef`.

Use `set Pi := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))⁻¹) with hPidef`. Use `set S1 := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k₁) with hS1`. Establish `hPi : Pi * P = 1` using `by rw [hPidef, hPdef, ← compAt_mt_mul, inv_mul_cancel, compAt_mt_one]`. Establish `hPPi : P * Pi = 1` using `by rw [hPidef, hPdef, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]`. Establish `hmem : (p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹ ∈ Khat A a`.

Rewrite using `[hp]`. Establish `e : (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹) * (p : GA D (dblSp A)) = k₁` using `by group`. Rewrite using `[e, hk₁, κ.apply_symm_apply]`. Conclude with `hk₀K`. Establish `hc` using `hcomm _ hmem τ`.

Rewrite `hc` using `[compAt_mt_mul, compAt_mt_mul]`. Establish `hcar' : IsCartanInv (gramAt D (dblSp A) τ) (Pi * sS τ * P)` using `isCartanInv_conj (hsS τ) hPi hPPi (compAt_isom hθ _ _ τ)`. Establish `hcar : IsCartanInv (gramAt D (dblSp A) τ) S1` using `GlobalTheory.T.isCartanInv_standardInvolution_doubledGram D A μ hμ _ hstd τ`. Establish `hcm : S1 * (Pi * sS τ * P) = Pi * sS τ * P * S1`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : S1 = Pi * sS τ * P` using `GlobalTheory.T.cartanInvolution_eq_of_commute _ _ _ _ hcar hcar' hcm`. Rewrite using `[heq, Matrix.mul_assoc (Pi * sS τ) P Pi, hPPi, Matrix.mul_one]`.
-/
theorem cartan_move_std : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  intro D A μ hμ κ hκ a p hp θ hθ sS hsS hcomm
  obtain ⟨k₀, hk₀K, hk₀⟩ := GlobalTheory.T.exists_maximalCompactUnn_component_standardCartanInv D θ hθ A.rank μ hμ
  have hstd : IsStdInv A μ (fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))) := by
    intro τ
    have h := hκ (κ.symm k₀)
    rw [κ.apply_symm_apply k₀] at h
    have h2 := congrArg (compAt θ τ) h
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul] at h2
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [hr, hk₀] at h2
    exact h2.symm
  refine ⟨_, hstd, fun τ => ?_⟩
  dsimp only
  set k₁ := κ.symm k₀ with hk₁
  set P := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))) with hPdef
  set Pi := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))⁻¹) with hPidef
  set S1 := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k₁) with hS1
  have hPi : Pi * P = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, inv_mul_cancel, compAt_mt_one]
  have hPPi : P * Pi = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]
  have hmem : (p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hp]
    have e : (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹) * (p : GA D (dblSp A)) = k₁ := by
      group
    rw [e, hk₁, κ.apply_symm_apply]
    exact hk₀K
  have hc := hcomm _ hmem τ
  rw [compAt_mt_mul, compAt_mt_mul] at hc
  have hcar' : IsCartanInv (gramAt D (dblSp A) τ) (Pi * sS τ * P) :=
    isCartanInv_conj (hsS τ) hPi hPPi (compAt_isom hθ _ _ τ)
  have hcar : IsCartanInv (gramAt D (dblSp A) τ) S1 := GlobalTheory.T.isCartanInv_standardInvolution_doubledGram D A μ hμ _ hstd τ
  have hcm : S1 * (Pi * sS τ * P) = Pi * sS τ * P * S1 := by
    calc S1 * (Pi * sS τ * P) = (Pi * P) * S1 * Pi * sS τ * P := by rw [hPi, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = Pi * (P * S1 * Pi * sS τ) * P := by simp only [Matrix.mul_assoc]
      _ = Pi * (sS τ * (P * S1 * Pi)) * P := by rw [hc]
      _ = Pi * sS τ * P * S1 * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = Pi * sS τ * P * S1 := by rw [hPi, Matrix.mul_one]
  have heq : S1 = Pi * sS τ * P := GlobalTheory.T.cartanInvolution_eq_of_commute _ _ _ _ hcar hcar' hcm
  rw [heq, Matrix.mul_assoc (Pi * sS τ) P Pi, hPPi, Matrix.mul_one]

end GlobalTheory.StdUnn.CartanMove
