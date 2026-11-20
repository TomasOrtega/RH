import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.FlagStabClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.gN`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (y i j)), Complex.sq_norm]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem entry_le_gN (y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    ‖y i j‖ ≤ Formalism.FourierDecayAlt.B.gN y := by
  unfold Formalism.FourierDecayAlt.B.gN
  rw [← Real.sqrt_sq (norm_nonneg (y i j)), Complex.sq_norm]
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (y i j) ≤ ∑ j', Complex.normSq (y i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (y i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (y i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (y i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

def AT (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (T : ℝ) : Set (Mt k r) :=
  {y | Matrix.of y ∈ RStab k r γ ∧ Formalism.FourierDecayAlt.B.gN (Matrix.of y) ≤ T}

/- English proof (translation)
The claim follows from `(Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) (uh_isUnit hγ)).closed`.
-/
theorem rstab_closed {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) :
    IsClosed {y : Mt k r | Matrix.of y ∈ RStab k r γ} :=
  (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) (uh_isUnit hγ)).closed

/- English proof (translation)
Establish `hc : IsClosed (AT (k` using `k) (r := r) γ T) := (rstab_closed hγ).inter (isClosed_le Formalism.FourierDecayAlt.P.s3dx1S_gNc continuous_const)`. Use `Metric.isCompact_of_isClosed_isBounded hc ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := (0 : Mt k r)) (r := max T 0)).subset fun y hy => ?_` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Use `(pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun j => le_trans (entry_le_gN (Matrix.of y) i j) (le_trans hy.2 (le_max_left _ _))` and prove the remaining obligations.
-/
theorem at_compact {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (T : ℝ) :
    IsCompact (AT (k := k) (r := r) γ T) := by
  have hc : IsClosed (AT (k := k) (r := r) γ T) :=
    (rstab_closed hγ).inter (isClosed_le Formalism.FourierDecayAlt.P.s3dx1S_gNc continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hc ?_
  refine (Metric.isBounded_closedBall (x := (0 : Mt k r)) (r := max T 0)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2
    fun j => le_trans (entry_le_gN (Matrix.of y) i j) (le_trans hy.2 (le_max_left _ _))

/- English proof (translation)
The claim follows from `(at_compact hγ T).isClosed.measurableSet`.
-/
theorem at_mset {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (T : ℝ) :
    MeasurableSet (AT (k := k) (r := r) γ T) := (at_compact hγ T).isClosed.measurableSet

def ET (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (T : ℝ) :
    Set (Mt k r) :=
  {m | ∃ y ∈ AT (k := k) (r := r) γ T, Hpk k r * (Matrix.of y)ᴴ * Hpk k r * Matrix.of m ∈ SgS k r z z' γ}

/- English proof (translation)
Establish `: CompactSpace K` using `isCompact_iff_compactSpace.mp hK`. Establish `hc : Continuous (fun p : K × Y => Φ ((p.1 : X), p.2))` using `hΦ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)`. Establish `hC : IsClosed {p : K × Y | Φ ((p.1 : X), p.2) ∈ S}` using `hS.preimage hc`. Establish `himg : {m : Y | ∃ y ∈ K, Φ (y, m) ∈ S} = Prod.snd '' {p : K × Y | Φ ((p.1 : X), p.2) ∈ S}`. Use extensionality with `m`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hm⟩`. Conclude with `⟨(⟨y, hy⟩, m), hm, rfl⟩`. Introduce and unpack `⟨⟨⟨y, hy⟩, m'⟩, hm, rfl⟩`. Conclude with `⟨y, hy, hm⟩`.

Rewrite using `[himg]`. Conclude with `isClosedMap_snd_of_compactSpace _ hC`.
-/
theorem closed_exists_of_compact {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {K : Set X} (hK : IsCompact K) (Φ : X × Y → Z) (hΦ : Continuous Φ) {S : Set Z}
    (hS : IsClosed S) : IsClosed {m : Y | ∃ y ∈ K, Φ (y, m) ∈ S} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × Y => Φ ((p.1 : X), p.2)) :=
    hΦ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hC : IsClosed {p : K × Y | Φ ((p.1 : X), p.2) ∈ S} := hS.preimage hc
  have himg : {m : Y | ∃ y ∈ K, Φ (y, m) ∈ S} = Prod.snd '' {p : K × Y | Φ ((p.1 : X), p.2) ∈ S} := by
    ext m; constructor
    · rintro ⟨y, hy, hm⟩; exact ⟨(⟨y, hy⟩, m), hm, rfl⟩
    · rintro ⟨⟨⟨y, hy⟩, m'⟩, hm, rfl⟩; exact ⟨y, hy, hm⟩
  rw [himg]
  exact isClosedMap_snd_of_compactSpace _ hC

/- English proof (translation)
Establish `hcont : Continuous (fun p : Mt k r × Mt k r => Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r * Matrix.of p.2)` using `((continuous_const.matrix_mul (PI.WUN.continuous_of.comp continuous_fst).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul (PI.WUN.continuous_of.comp continuous_snd)`. Conclude with `closed_exists_of_compact (at_compact hγ T) _ hcont (sgS_closed z z' hz γ)`.
-/
theorem et_closed (z z' : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (T : ℝ) :
    IsClosed (ET (k := k) (r := r) z z' γ T) := by
  have hcont : Continuous (fun p : Mt k r × Mt k r =>
      Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r * Matrix.of p.2) :=
    ((continuous_const.matrix_mul (PI.WUN.continuous_of.comp continuous_fst).matrix_conjTranspose).matrix_mul
      continuous_const).matrix_mul (PI.WUN.continuous_of.comp continuous_snd)
  exact closed_exists_of_compact (at_compact hγ T) _ hcont (sgS_closed z z' hz γ)

/- English proof (translation)
Establish `h1 : Hpk k r * ρᴴ * Hpk k r * ρ = 1`. Establish `: ρᴴ * Hpk k r * ρ = Hpk k r` using `hρ`. Rewrite using `[Matrix.mul_assoc (Hpk k r * ρᴴ), Matrix.mul_assoc, ← Matrix.mul_assoc ρᴴ, this, WeylGroupFacts.hpk_sq]`. Conclude with `(Matrix.inv_eq_left_inv h1).symm`.
-/
theorem uh_inv_eq {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ UH (Hpk k r)) :
    Hpk k r * ρᴴ * Hpk k r = ρ⁻¹ := by
  have h1 : Hpk k r * ρᴴ * Hpk k r * ρ = 1 := by
    have : ρᴴ * Hpk k r * ρ = Hpk k r := hρ
    rw [Matrix.mul_assoc (Hpk k r * ρᴴ), Matrix.mul_assoc, ← Matrix.mul_assoc ρᴴ, this, WeylGroupFacts.hpk_sq]
  exact (Matrix.inv_eq_left_inv h1).symm

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
