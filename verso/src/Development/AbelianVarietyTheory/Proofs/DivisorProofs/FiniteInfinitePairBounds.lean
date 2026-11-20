import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsTopGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingExtendScalarsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVertexLatticeOrthonormalCoordsTopNodeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeVertexLatticeGridCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmeticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotalExponentTopWeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingArchimedeanBoundFockNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBoundStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FPair

/- English proof (translation)
Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bil {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W →ₗ[K] K) (s s' : K) (u : V) (v : W) : f (s • u) (s' • v) = s * (s' * f u v) := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨CF0, h6⟩` from `GlobalTheory.T.exists_totalExponent_topWeight_bound`. Use `⟨CF0, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨K0, h6'⟩` from `h6 CF hCF`. Use `⟨max K0 0, fun ε C hC => ?_⟩` and prove the remaining obligations. Take `⟨x₀, hx⟩` from `h6' ε`.

Use `⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩` and prove the remaining obligations. Take `⟨hb1, Dn, hDn, hdiv, hlog⟩` from `hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt`. Take `⟨h5mul, h5div, h5fin, h5sum⟩` from `GlobalTheory.T.placeValuation_localDegree_arithmetic (K := D.what₂.LL)`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (le_trans (by norm_num) hS.size.2.2.2.1 : 1 ≤ D.R.m)`. Establish `hsig : 0 ≤ sig ch.G` using `Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`.

Establish `hlb : 0 ≤ Real.log large₂.sc.b` using `Real.log_nonneg hb1`. Establish `hK : K0 ≤ C` using `(le_max_left _ _).trans hC`. Establish `hC0 : 0 ≤ C` using `(le_max_right _ _).trans hC`. Use `⟨fun w => (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ), ⟨fun w => ?_, ?_, fun s => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (0 : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ)`.

Conclude with `(h5div w Dn Dn hDn dvd_rfl).1` after adjusting the coercions. Use `(h5fin Dn hDn).subset fun w hw => ?_` and prove the remaining obligations. Introduce `h0`. Conclude with `hw (by simp [h0])`. Use `(h5sum Dn hDn s).trans (hlog.trans ?_)` and prove the remaining obligations.

Unfold `bOne`. Establish `e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b` using `by positivity`. Establish `e2 : K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤ C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b`. Use `mul_le_mul_of_nonneg_right hK e1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e3 : C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤ C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b`. Establish `h1 : 0 ≤ C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b` using `by positivity`. Establish `h2 : Real.log large₂.sc.b ≤ D.R.m * (Real.log large₂.sc.b + sig ch.G)` using `by nlinarith`. Use `mul_le_mul_of_nonneg_left h2 h1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `e2.trans e3`. Introduce `w y a a' u v hu hv`. Take `⟨u0, s, hu0, hs, hsa, hsu⟩` from `hu`. Take `⟨v0, s', hv0, hs', hsa', hsv⟩` from `hv`. Establish `hIS` using `fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ`.

Use `⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu0, ← hv0]`. Conclude with `(GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm`. Establish `h4` using `GlobalTheory.T.branchingPairing_integral_upToExponents (labLL D) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m)) (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) _ _ (GlobalTheory.T.isLattice_vertexLattice_gridCorner ch.S.toGridChoice y) (GlobalTheory …`. Distinguish the cases in `hy : GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0 = 0`.

Conclude with `Or.inl hy`. Use `right`. Break down `h4 with h0 | h4` into its components or cases. Conclude with `absurd h0 (mul_ne_zero hs (mul_ne_zero hs' hy))`. Rewrite `h4` using `[h5mul w _ _ hs (mul_ne_zero hs' hy), h5mul w _ _ hs' hy]`.

Use `set p := Formalism.EigenvalueLevelCeiling.plc w`. Use `set E := ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p`. Establish `hp` using `(h5div w (p ^ E) Dn hDn (hdiv p (Formalism.EigenvalueLevelCeiling.plc_prime w))).2`. Rewrite `hp` using `[Nat.cast_pow]`. Establish `h4' : (-(Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ)) ≤ (Formalism.DivisionValues.vw w s : ℝ) + ((Formalism.DivisionValues.vw w s' : ℝ) + (Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0) : ℝ))`.

Conclude with `h4` after adjusting the coercions. Establish `hp' : (Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ)` using `by exact_mod_cast hp`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem finPair : FinPairK := by
  obtain ⟨CF0, h6⟩ := GlobalTheory.T.exists_totalExponent_topWeight_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h6'⟩ := h6 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h6' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, Dn, hDn, hdiv, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  obtain ⟨h5mul, h5div, h5fin, h5sum⟩ := GlobalTheory.T.placeValuation_localDegree_arithmetic (K := D.what₂.LL)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) hS.size.2.2.2.1 : 1 ≤ D.R.m)
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  refine ⟨fun w => (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ), ⟨fun w => ?_, ?_, fun s => ?_⟩, ?_⟩
  · show (0 : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ)
    exact_mod_cast (h5div w Dn Dn hDn dvd_rfl).1
  · refine (h5fin Dn hDn).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])
  · refine (h5sum Dn hDn s).trans (hlog.trans ?_)
    unfold bOne
    have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by positivity
    have e2 : K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by
      have := mul_le_mul_of_nonneg_right hK e1
      linarith
    have e3 : C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have h1 : 0 ≤ C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b := by positivity
      have h2 : Real.log large₂.sc.b ≤ D.R.m * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
      have := mul_le_mul_of_nonneg_left h2 h1
      nlinarith
    exact e2.trans e3
  · intro w y a a' u v hu hv
    obtain ⟨u0, s, hu0, hs, hsa, hsu⟩ := hu
    obtain ⟨v0, s', hv0, hs', hsa', hsv⟩ := hv
    have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
    refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
    · rw [← hu0, ← hv0]
      exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
    · have h4 := GlobalTheory.T.branchingPairing_integral_upToExponents (labLL D) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
        (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) _ _ (GlobalTheory.T.isLattice_vertexLattice_gridCorner ch.S.toGridChoice y) (GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff ch.S.toGridChoice y) w
        (s • u0) (s' • v0) hsu hsv
      erw [bil] at h4
      by_cases hy : GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0 = 0
      · exact Or.inl hy
      right
      rcases h4 with h0 | h4
      · exact absurd h0 (mul_ne_zero hs (mul_ne_zero hs' hy))
      rw [h5mul w _ _ hs (mul_ne_zero hs' hy), h5mul w _ _ hs' hy] at h4
      set p := Formalism.EigenvalueLevelCeiling.plc w
      set E := ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p
      have hp := (h5div w (p ^ E) Dn hDn (hdiv p (Formalism.EigenvalueLevelCeiling.plc_prime w))).2
      rw [Nat.cast_pow] at hp
      have h4' : (-(Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ)) ≤
          (Formalism.DivisionValues.vw w s : ℝ) + ((Formalism.DivisionValues.vw w s' : ℝ) + (Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0) : ℝ)) := by
        exact_mod_cast h4
      have hp' : (Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast hp
      linarith

/- English proof (translation)
Take `⟨CF0, h8⟩` from `GlobalTheory.T.archimedean_branching_constant_bound`. Use `⟨CF0, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨K0, h8'⟩` from `h8 CF hCF`. Use `⟨max K0 0, fun ε C hC => ?_⟩` and prove the remaining obligations. Take `⟨x₀, hx⟩` from `h8' ε`.

Use `⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩` and prove the remaining obligations. Take `⟨hb1, hlog⟩` from `hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt`. Establish `hsig : 0 ≤ sig ch.G` using `Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`. Establish `hlb : 0 ≤ Real.log large₂.sc.b` using `Real.log_nonneg hb1`. Establish `hK : K0 ≤ C` using `(le_max_left _ _).trans hC`.

Establish `hC0 : 0 ≤ C` using `(le_max_right _ _).trans hC`. Establish `hIS` using `fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ`. Use `set P := ∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2 with hP`. Establish `hP0 : 0 ≤ P` using `Finset.prod_nonneg fun τ _ => sq_nonneg _`. Establish `hPa : P ≤ Real.exp (aOne ch.G C large₂.sc.b)`.

Establish `h1 : Real.log P ≤ aOne ch.G C large₂.sc.b`. Use `hlog.trans ?_` and prove the remaining obligations. Unfold `aOne`. Establish `e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b` using `by positivity`. Establish `e2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G` using `by positivity`.

Use `mul_le_mul_of_nonneg_right hK e1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Break down `hP0.lt_or_eq with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h]`.

Conclude with `(Real.exp_pos _).le`. Introduce `σ B B' u v hu hv`. Take `⟨u0, hu0, hB⟩` from `hu`. Take `⟨v0, hv0, hB'⟩` from `hv`. Use `⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hu0, ← hv0]`. Conclude with `(GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm`. Take `⟨hn1, hn2, h7⟩` from `GlobalTheory.T.branchingPairing_archimedean_bound_fockNorm σ ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m)) (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) u0 v0`. Use `h7.trans ?_` and prove the remaining obligations. Establish `hB1 : (pairK (wt ch.G (.top D.R.m)) (fun _ => (1 : Matrix _ _ ℂ)) (GlobalTheory.CoefModel.mapVV σ _ u0) (GlobalTheory.CoefModel.mapVV σ _ u0)).re ≤ B` using `hB`.

Establish `hB2 : (pairK (fun τ => (listedWt ch.G (.grid D.R.m D.R.m) τ).dual) (fun _ => (1 : Matrix _ _ ℂ)) (GlobalTheory.CoefModel.mapVV σ _ v0) (GlobalTheory.CoefModel.mapVV σ _ v0)).re ≤ B'` using `hB'`. Establish `hPa' : (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ Real.exp (aOne ch.G C large₂.sc.b)` using `hPa`. Establish `hP0' : 0 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2)` using `hP0`. Establish `hBn : 0 ≤ B` using `hn1.trans hB1`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul (mul_le_mul_of_nonneg_left hB1 (Real.exp_pos _).le) hB2 hn2` to reduce the goal to its premises. Conclude with `mul_nonneg (Real.exp_pos _).le hBn`.
-/
theorem infPair : InfPairK := by
  obtain ⟨CF0, h8⟩ := GlobalTheory.T.archimedean_branching_constant_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h8'⟩ := h8 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h8' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
  set P := ∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun τ _ => sq_nonneg _
  have hPa : P ≤ Real.exp (aOne ch.G C large₂.sc.b) := by
    have h1 : Real.log P ≤ aOne ch.G C large₂.sc.b := by
      refine hlog.trans ?_
      unfold aOne
      have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
      have e2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
      have := mul_le_mul_of_nonneg_right hK e1
      nlinarith
    rcases hP0.lt_or_eq with h | h
    · calc P = Real.exp (Real.log P) := (Real.exp_log h).symm
        _ ≤ _ := Real.exp_le_exp.2 h1
    · rw [← h]; exact (Real.exp_pos _).le
  intro σ B B' u v hu hv
  obtain ⟨u0, hu0, hB⟩ := hu
  obtain ⟨v0, hv0, hB'⟩ := hv
  refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
  · rw [← hu0, ← hv0]
    exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
  · obtain ⟨hn1, hn2, h7⟩ := GlobalTheory.T.branchingPairing_archimedean_bound_fockNorm σ ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
      (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) u0 v0
    refine h7.trans ?_
    have hB1 : (pairK (wt ch.G (.top D.R.m)) (fun _ => (1 : Matrix _ _ ℂ)) (GlobalTheory.CoefModel.mapVV σ _ u0)
        (GlobalTheory.CoefModel.mapVV σ _ u0)).re ≤ B := hB
    have hB2 : (pairK (fun τ => (listedWt ch.G (.grid D.R.m D.R.m) τ).dual) (fun _ => (1 : Matrix _ _ ℂ))
        (GlobalTheory.CoefModel.mapVV σ _ v0) (GlobalTheory.CoefModel.mapVV σ _ v0)).re ≤ B' := hB'
    have hPa' : (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ Real.exp (aOne ch.G C large₂.sc.b) := hPa
    have hP0' : 0 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) := hP0
    have hBn : 0 ≤ B := hn1.trans hB1
    calc _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * _ * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPa' hn1) hn2
      _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * B * B' := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hB1 (Real.exp_pos _).le) hB2 hn2
          exact mul_nonneg (Real.exp_pos _).le hBn

/- English proof (translation)
Introduce `_` and use `⟨finPair, infPair⟩`.
-/
theorem main : GlobalTheory.FunPr.Hypotheses₂ → FinPairK ∧ InfPairK := fun _ => ⟨finPair, infPair⟩

end GlobalTheory.FPair

end
