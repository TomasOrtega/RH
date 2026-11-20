import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.AutomorphicBallCount
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.AutBall

/- English proof (translation)
Establish `hf' : (0 : ℝ) < f` using `by exact_mod_cast hf`. Establish `hE : 1 ≤ Real.exp (R / f)` using `Real.one_le_exp (div_nonneg hR hf'.le)`. Establish `htt : 0 < t * t` using `mul_pos ht ht`. Establish `h1 : 1 ≤ s * Real.exp (R / f) / (t * t)`. Rewrite using `[le_div_iff₀ htt]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : 1 + 2 * s * Real.exp (R / f) / (t * t) ≤ 3 * s / t ^ 2 * Real.exp (R / f)`. Establish `e1 : 2 * s * Real.exp (R / f) / (t * t) = 2 * (s * Real.exp (R / f) / (t * t))` using `by ring`. Establish `e2 : 3 * s / t ^ 2 * Real.exp (R / f) = 3 * (s * Real.exp (R / f) / (t * t))` using `by ring`. Rewrite using `[e1, e2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : Real.exp (2 * (m : ℝ) * R) = Real.exp (R / f) ^ (2 * (m * f))`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h3, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) h2 _`.
-/
theorem pow_bound (s t R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / (t * t)) ^ (2 * (m * f)) ≤
      (3 * s / t ^ 2) ^ (2 * (m * f)) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hE : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR hf'.le)
  have htt : 0 < t * t := mul_pos ht ht
  have h1 : 1 ≤ s * Real.exp (R / f) / (t * t) := by
    rw [le_div_iff₀ htt]; nlinarith
  have h2 : 1 + 2 * s * Real.exp (R / f) / (t * t) ≤ 3 * s / t ^ 2 * Real.exp (R / f) := by
    have e1 : 2 * s * Real.exp (R / f) / (t * t) = 2 * (s * Real.exp (R / f) / (t * t)) := by ring
    have e2 : 3 * s / t ^ 2 * Real.exp (R / f) = 3 * (s * Real.exp (R / f) / (t * t)) := by ring
    rw [e1, e2]; linarith
  have h3 : Real.exp (2 * (m : ℝ) * R) = Real.exp (R / f) ^ (2 * (m * f)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [h3, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 _

/- English proof (translation)
Introduce `I hn x r hr`. Take `⟨hfin, hle⟩` from `GlobalTheory.RationalCount.count_le I x x r hn hr`. Establish `hsub : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet I x r ⊆ {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * x).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * x).1 v)) ≤ r v}`. Introduce and unpack `a ⟨h1, h2, h3⟩`. Use `⟨h1, h2, fun v => le_trans ?_ (h3 v)⟩` and prove the remaining obligations.

Take `⟨h0, -, -, h4, -⟩` from `(GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 ((x⁻¹ * a * x).1 v) ((x⁻¹ * a * x).1 v) hn`. Establish `h5 : (1 : ℝ) ≤ Real.sqrt 2` using `Real.one_le_sqrt.mpr (by norm_num)`. Conclude with `(le_mul_of_one_le_left h0 h5).trans h4`. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Establish `hc` using `Set.ncard_le_ncard hsub hfin`.

Establish `hf : 0 < I.f` using `Module.finrank_pos (R := ℚ) (M := I.F)`. Establish `hs : 1 ≤ Real.sqrt (I.n : ℝ)` using `Real.one_le_sqrt.mpr (by exact_mod_cast hn)`. Establish `hb` using `pow_bound (Real.sqrt (I.n : ℝ)) (tau1 I x) (∑ v, r v) (I.n ^ 2) I.f hs (GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x) (min_le_left _ _) (Finset.sum_nonneg fun v _ => hr v) hf`. Use `(Nat.cast_le.mpr hc).trans (hle.trans (hb.trans (le_of_eq ?_)))` and prove the remaining obligations. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem autBallCount : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.AutBallCount := by
  intro I hn x r hr
  obtain ⟨hfin, hle⟩ := GlobalTheory.RationalCount.count_le I x x r hn hr
  have hsub : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet I x r ⊆
      {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * x).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * x).1 v)) ≤ r v} := by
    rintro a ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun v => le_trans ?_ (h3 v)⟩
    obtain ⟨h0, -, -, h4, -⟩ :=
      (GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 ((x⁻¹ * a * x).1 v) ((x⁻¹ * a * x).1 v) hn
    have h5 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    exact (le_mul_of_one_le_left h0 h5).trans h4
  refine ⟨hfin.subset hsub, ?_⟩
  have hc := Set.ncard_le_ncard hsub hfin
  have hf : 0 < I.f := Module.finrank_pos (R := ℚ) (M := I.F)
  have hs : 1 ≤ Real.sqrt (I.n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hb := pow_bound (Real.sqrt (I.n : ℝ)) (tau1 I x) (∑ v, r v) (I.n ^ 2) I.f hs
    (GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x) (min_le_left _ _) (Finset.sum_nonneg fun v _ => hr v) hf
  refine (Nat.cast_le.mpr hc).trans (hle.trans (hb.trans (le_of_eq ?_)))
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA
  push_cast
  rfl

end GlobalTheory.AutBall
