import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

/- English proof (translation)
Simplify using `only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]`.
-/
lemma bergman_lerp_self {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (t : ℝ) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) :
    bergman (W.lerp W t) dV V n x = bergman W dV V n x := by
  simp only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)`.
-/
lemma bergman_nonneg {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) : 0 ≤ bergman W dV V n x :=
  Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)

/- English proof (translation)
Introduce `D X _ _ _ _ _ A L W dV hW V _ hV hdim`. Use `dV.isProb` as an intermediate fact. Take `⟨C, hC⟩` from `hUnif A L W W dV hW hW`. Establish `hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D` using `fun n => by positivity`. Use `set g : ℕ → X → ℝ := fun n x => (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg`.

Establish `hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C` using `fun n x => by`. Use `⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩` and prove the remaining obligations. Establish `h` using `hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x`. Rewrite `h` using `[bergman_lerp_self]`. Use `show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C`.

Rewrite using `[inv_mul_le_iff₀ (hpos n)]`. Combine the linear relations using `[mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]`. Establish `hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε`. Introduce `x ε hε`. Establish `h` using `(tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)`.

Use `filter_upwards [h] with n hn`. Use `show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _`. Rewrite using `[inv_mul_le_iff₀ (hpos n)]`. Combine the linear relations using `[mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]`. Establish `hmass : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ`.

Introduce `ε hε`. Establish `h` using `(tendsto_add_atTop_nat 1).eventually (hdim ε hε)`. Use `filter_upwards [h] with n hn`. Establish `hI : ∫ x, g n x ∂dV.μ = (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1))`. Rewrite using `[hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]`.

Rewrite using `[hI, le_inv_mul_iff₀ (hpos n)]`. Combine the linear relations using `[mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]`. Establish `hgi : ∀ n, Integrable (g n) dV.μ` using `fun n => (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _`. Establish `h` using `hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass`. Conclude with `(tendsto_add_atTop_iff_nat 1).1 h`.
-/
theorem BergmanL1Convergence.proof (hL1 : L1Convergence.Statement)
    (hLoc : LocalBergmanBound.Statement) (hUnif : UniformBergmanBound.Statement)
    (hInt : IntegralOfBergman.Statement) (hBI : BergmanIntegrable.Statement)
    (hDI : BergmanDensIntegrable.Statement) : BergmanL1Convergence.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV hdim
  have := dV.isProb
  obtain ⟨C, hC⟩ := hUnif A L W W dV hW hW
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D := fun n => by positivity
  set g : ℕ → X → ℝ := fun n x =>
    (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg
  have hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C := fun n x => by
    refine ⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩
    have h := hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x
    rw [bergman_lerp_self] at h
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]
  have hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε := by
    intro x ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)
    filter_upwards [h] with n hn
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hmass : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ := by
    intro ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hdim ε hε)
    filter_upwards [h] with n hn
    have hI : ∫ x, g n x ∂dV.μ =
        (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1)) := by
      rw [hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]
    rw [hI, le_inv_mul_iff₀ (hpos n)]
    linarith [mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hgi : ∀ n, Integrable (g n) dV.μ := fun n =>
    (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _
  have h := hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass
  exact (tendsto_add_atTop_iff_nat 1).1 h

/- English proof (translation)
The claim follows from `BergmanL1Convergence.proof L1Convergence.proof (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof)) (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof) IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensInte …`.
-/
theorem BergmanL1Convergence.full : BergmanL1Convergence.Statement :=
  BergmanL1Convergence.proof L1Convergence.proof
    (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof))
    (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof)
    IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensIntegrable.proof

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
