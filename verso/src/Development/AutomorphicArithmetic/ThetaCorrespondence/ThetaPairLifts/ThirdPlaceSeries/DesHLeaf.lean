import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaDenominatorsFitFunction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.Close
attribute [local instance] Formalism.BasicNotions.Host.cmStar
/- English proof (translation)
Use `⟨0, fun CF _ => ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩⟩` and prove the remaining obligations. Introduce `_`. Use `⟨0, fun C _ => ?_⟩` and prove the remaining obligations. Establish `hW : PageWin Fm` using `hF.2.1`. Use `⟨max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps)), fun x hx hx0 i p _ d _ => ?_⟩` and prove the remaining obligations.

Establish `hx1 : 1 < x` using `lt_trans Fm.one_lt_family_threshold hx`. Establish `hx0' : (0 : ℝ) < x` using `by linarith`. Establish `h8 : (8 : ℝ) ≤ x ^ (8 * eps)`. Establish `e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps`. Rewrite using `[← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]`.

Establish `e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps` using `Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx0) heps.le`. Establish `e3 : x ^ eps ≤ x ^ (8 * eps)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨⟨hn, -⟩, ⟨-, hm⟩, -⟩` from `hW x hx i`. Establish `hδ : (Fm.L x i).sc.delta1 ≤ 1`.

Unfold `Scale.delta1`. Conclude with `Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le (by linarith [(Fm.L x i).sc.eps_pos])`. Establish `hδ0 : 0 ≤ (Fm.L x i).sc.delta1`. Unfold `Scale.delta1`. Conclude with `Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _`.

Establish `hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ)`. Establish `hs` using `Real.sq_sqrt (mul_nonneg hx0'.le hδ0)`. Establish `hs0` using `Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)`. Establish `hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ)` using `by positivity`. Establish `hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x` using `by nlinarith`.

Establish `hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2` using `by nlinarith`. Establish `hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps)`. Rewrite using `[Real.rpow_add hx0', Real.rpow_two]`. Establish `hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ)`. Unfold `Ranks.f`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`. Establish `hx2 : 0 ≤ x ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4, (Fm.D x i).R.f_le_k⟩, ?_⟩` and prove the remaining obligations. Use `show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b`. Conclude with `(lcLeOfCloud d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le (fun τ j => cloudIcc (Fm.L x i) τ j)).trans (scLeB (Fm.params x hx i))`.
-/
theorem desHLeaf_alt : _root_.GlobalTheory.BigTop.Fun.DescentHeightCondition := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨0, fun C _ => ?_⟩
  have hW : PageWin Fm := hF.2.1
  refine ⟨max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps)), fun x hx hx0 i p _ d _ => ?_⟩
  have hx1 : 1 < x := lt_trans Fm.one_lt_family_threshold hx
  have hx0' : (0 : ℝ) < x := by linarith
  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx0) heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, -⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  refine ⟨⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩, ?_⟩
  show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
  exact (lcLeOfCloud d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
    (fun τ j => cloudIcc (Fm.L x i) τ j)).trans (scLeB (Fm.params x hx i))
end GlobalTheory.BigTop.Fun.Close
end
end
