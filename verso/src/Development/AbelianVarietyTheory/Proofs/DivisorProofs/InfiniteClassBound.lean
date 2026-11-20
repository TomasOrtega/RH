import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTopVertexClassesLeClassNumberBoundNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormGridModulusLeExpDepthLogNormSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruenceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.ClassCount

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `_`. Take `⟨c1, hT1⟩` from `GlobalTheory.T.principalCongruence_le_topLevel_classSum`. Take `⟨c2, hR1⟩` from `GlobalTheory.T.classSum_vertexLevels_contain_principalCongruence`. Use `⟨max c1 c2, fun CF hCF => ⟨144, fun ε C hC => ?_⟩⟩` and prove the remaining obligations. Take `⟨x1, hx1⟩` from `hT1 CF ((le_max_left _ _).trans hCF) ε`.

Take `⟨x2, hx2⟩` from `hR1 CF ((le_max_right _ _).trans hCF) ε`. Use `⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hFO => ?_⟩` and prove the remaining obligations. Establish `hTop` using `hx1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO`. Establish `hRow` using `hx2 D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO`. Take `⟨hNb, hfb, hN1, hf1, hm2, hrd1, hlrd, hb12⟩` from `GlobalTheory.T.parameterSizeConditions_numericBounds large₂ hS.size`.

Use `set b := large₂.sc.b with hb`. Use `set N := bigN D with hNdef`. Establish `hsig : 0 ≤ sig ch.G` using `Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hlb : 0 ≤ Real.log b` using `Real.log_nonneg (by linarith)`.

Establish `hrd0 : 0 < D.host.rdE` using `by linarith`. Establish `hN0 : (1 : ℝ) ≤ N` using `by exact_mod_cast hN1`. Establish `hf0 : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf1`. Use `set base := 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 with hbase`. Establish `hbase1 : 1 ≤ base`.

Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2` using `one_le_pow₀ hf0`. Establish `: (1 : ℝ) ≤ (N : ℝ) ^ 4` using `one_le_pow₀ hN0`. Establish `: (1 : ℝ) ≤ D.host.rdE ^ 2` using `one_le_pow₀ hrd1`. Establish `: (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2` using `by nlinarith`. Establish `: (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hlbase : Real.log base ≤ 8 * Real.log b`. Establish `h12 : Real.log 12 ≤ Real.log b` using `Real.log_le_log (by norm_num) hb12`. Establish `hlf : Real.log (D.R.f:ℝ) ≤ Real.log b` using `Real.log_le_log (by linarith) hfb`. Establish `hlN : Real.log N ≤ Real.log b` using `Real.log_le_log (by linarith) hNb`.

Establish `e : Real.log base = Real.log 12 + 2 * Real.log (D.R.f:ℝ) + 4 * Real.log N + 2 * Real.log D.host.rdE`. Rewrite using `[hbase, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use the polynomial consequences of the given equalities and inequalities. Use `set M := hBd D N * Real.exp (2 * sig ch.G) ^ (N ^ 2) with hM`. Establish `hM0 : 0 ≤ M` using `by rw [hM, hBd]; positivity`. Establish `factor : ∀ (n : ℕ), n ≤ N → ∀ a : ℝ, 0 ≤ a → a ≤ Real.exp (2 * sig ch.G) → hBd D n * a ^ (n ^ 2) ≤ M`. Introduce `n hn a ha0 ha`.

Establish `h1 : hBd D n ≤ hBd D N` using `hBd_mono hn hbase1 hrd0.le`. Establish `h2 : a ^ (n ^ 2) ≤ Real.exp (2 * sig ch.G) ^ (N ^ 2)` using `(pow_le_pow_left₀ ha0 ha _).trans (pow_le_pow_right₀ (Real.one_le_exp (by linarith)) (by gcongr))`. Conclude with `mul_le_mul h1 h2 (by positivity) (by rw [hBd]; positivity)`. Establish `hmod` using `GlobalTheory.T.absNorm_gridModulus_le_exp_depthLogNormSum ch.G hS.hF`. Establish `fin : ∀ (X : Node), DefNode D.R.m X → ∀ K : Subgroup (GL (Fin (ch.G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (ch.G.V X).gram (ch.G.Λ X) ch.G.modul ≤ K → (Nat.card (FinCl (ch.G.V X) K) : ℝ) ≤ M` using `fun X hX K hK => (GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence ch.G ch.S.N X hX _ (ch.G.pl.modul_ne_bot _) K hK).trans (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G X hX) _ (Nat.cast_nonneg _) hmod)`.

Use `set K0 := 48 * (D.R.f:ℝ) * (N : ℝ) ^ 2 * Real.log b + 2 * (N : ℝ) ^ 2 * sig ch.G with hK0`. Establish `hK00 : 0 ≤ K0` using `by positivity`. Establish `hMK : M ≤ Real.exp K0`. Establish `e1 : hBd D N ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b))`. Rewrite using `[Real.exp_nat_mul]`.

Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations. Rewrite using `[← Real.log_le_iff_le_exp (by positivity)]`. Conclude with `hlbase`. Establish `e2 : Real.exp (2 * sig ch.G) ^ (N ^ 2) = Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G))` using `(Real.exp_nat_mul _ _).symm`. Rewrite using `[hM, e2, hK0]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hm0 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm2`. Establish `key : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ D.R.m * aOne ch.G C b`. Establish `hm00 : (0 : ℝ) ≤ D.R.m` using `by linarith`. Establish `h3 : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ 3 * D.R.m * K0` using `mul_le_mul_of_nonneg_right (by push_cast; linarith) hK00`.

Use `h3.trans ?_` and prove the remaining obligations. Establish `hX : 0 ≤ (D.R.f : ℝ) * N * Real.log b` using `by positivity`. Establish `t1 : 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b ≤ C * D.R.f * N * b * Real.log b`. Combine the equalities or inequalities in the displayed calculation. Establish `hCm : (6 : ℝ) ≤ C * D.R.m`.

Use `mul_le_mul hC hm0 (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t2 : 6 * ((N : ℝ) ^ 2 * sig ch.G) ≤ (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G)` using `mul_le_mul_of_nonneg_right hCm (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hK0]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ D.R.m * (C * D.R.f * N * b * Real.log b + (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G)) := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hm00`. Use `_ = D.R.m * aOne ch.G C b := by rw [aOne]; ring`. Establish `hexp : Real.exp K0 ^ (2 * D.R.m + 1) ≤ Real.exp (D.R.m * aOne ch.G C b)`. Rewrite using `[← Real.exp_nat_mul]`.

Conclude with `Real.exp_le_exp.2 key`. Use `⟨?_, fun Φ β hβ => ?_⟩` and prove the remaining obligations. Establish `h` using `(GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow ch.G ch.S.N).trans (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G (.top 0) (by simp [DefNode])) _ (Nat.cast_nonneg _) hmod)`. Use `h.trans (hMK.trans ((le_self_pow₀ (Real.one_le_exp hK00) (by omega)).trans hexp))` and prove the remaining obligations. Rewrite using `[GridChoice.Classes, Nat.card_prod, Nat.card_pi, Nat.card_pi]`.

Use `push_cast`. Establish `hT : ∏ j : Fin D.R.m, (Nat.card (FinCl (ch.G.V (.top j)) (ch.S.levTop A.μ0 Φ β j j.2)) : ℝ) ≤ M ^ D.R.m`. Combine the equalities or inequalities in the displayed calculation. Establish `hR : ∏ i : Fin (D.R.m + 1), (Nat.card (FinCl (ch.G.V (.grid i D.R.m)) (ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2))) : ℝ) ≤ M ^ (D.R.m + 1)`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem infClassK : GlobalTheory.FunPr.Hypotheses₂ → InfClassK := by
  intro _
  obtain ⟨c1, hT1⟩ := GlobalTheory.T.principalCongruence_le_topLevel_classSum
  obtain ⟨c2, hR1⟩ := GlobalTheory.T.classSum_vertexLevels_contain_principalCongruence
  refine ⟨max c1 c2, fun CF hCF => ⟨144, fun ε C hC => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := hT1 CF ((le_max_left _ _).trans hCF) ε
  obtain ⟨x2, hx2⟩ := hR1 CF ((le_max_right _ _).trans hCF) ε
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hFO => ?_⟩
  have hTop := hx1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  have hRow := hx2 D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  obtain ⟨hNb, hfb, hN1, hf1, hm2, hrd1, hlrd, hb12⟩ := GlobalTheory.T.parameterSizeConditions_numericBounds large₂ hS.size
  set b := large₂.sc.b with hb
  set N := bigN D with hNdef
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hf0 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1

  set base := 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 with hbase
  have hbase1 : 1 ≤ base := by
    have : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 := one_le_pow₀ hf0
    have : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN0
    have : (1 : ℝ) ≤ D.host.rdE ^ 2 := one_le_pow₀ hrd1
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 := by nlinarith
    nlinarith
  have hlbase : Real.log base ≤ 8 * Real.log b := by
    have h12 : Real.log 12 ≤ Real.log b := Real.log_le_log (by norm_num) hb12
    have hlf : Real.log (D.R.f:ℝ) ≤ Real.log b := Real.log_le_log (by linarith) hfb
    have hlN : Real.log N ≤ Real.log b := Real.log_le_log (by linarith) hNb
    have e : Real.log base = Real.log 12 + 2 * Real.log (D.R.f:ℝ) + 4 * Real.log N + 2 * Real.log D.host.rdE := by
      rw [hbase, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast; ring
    rw [e]; nlinarith

  set M := hBd D N * Real.exp (2 * sig ch.G) ^ (N ^ 2) with hM
  have hM0 : 0 ≤ M := by rw [hM, hBd]; positivity
  have factor : ∀ (n : ℕ), n ≤ N → ∀ a : ℝ, 0 ≤ a → a ≤ Real.exp (2 * sig ch.G) → hBd D n * a ^ (n ^ 2) ≤ M := by
    intro n hn a ha0 ha
    have h1 : hBd D n ≤ hBd D N := hBd_mono hn hbase1 hrd0.le
    have h2 : a ^ (n ^ 2) ≤ Real.exp (2 * sig ch.G) ^ (N ^ 2) :=
      (pow_le_pow_left₀ ha0 ha _).trans (pow_le_pow_right₀ (Real.one_le_exp (by linarith)) (by gcongr))
    exact mul_le_mul h1 h2 (by positivity) (by rw [hBd]; positivity)
  have hmod := GlobalTheory.T.absNorm_gridModulus_le_exp_depthLogNormSum ch.G hS.hF
  have fin : ∀ (X : Node), DefNode D.R.m X → ∀ K : Subgroup (GL (Fin (ch.G.V X).rank) (Lev.EAf D)),
      congLev D.sp.cm (ch.G.V X).gram (ch.G.Λ X) ch.G.modul ≤ K → (Nat.card (FinCl (ch.G.V X) K) : ℝ) ≤ M := fun X hX K hK =>
    (GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence ch.G ch.S.N X hX _ (ch.G.pl.modul_ne_bot _) K hK).trans
      (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G X hX) _ (Nat.cast_nonneg _) hmod)

  set K0 := 48 * (D.R.f:ℝ) * (N : ℝ) ^ 2 * Real.log b + 2 * (N : ℝ) ^ 2 * sig ch.G with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hMK : M ≤ Real.exp K0 := by
    have e1 : hBd D N ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) := by
      rw [Real.exp_nat_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [← Real.log_le_iff_le_exp (by positivity)]
      exact hlbase
    have e2 : Real.exp (2 * sig ch.G) ^ (N ^ 2) = Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) := (Real.exp_nat_mul _ _).symm
    rw [hM, e2, hK0]
    calc _ ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) * Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf

  have hm0 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have key : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ D.R.m * aOne ch.G C b := by
    have hm00 : (0 : ℝ) ≤ D.R.m := by linarith
    have h3 : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ 3 * D.R.m * K0 :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hK00
    refine h3.trans ?_
    have hX : 0 ≤ (D.R.f : ℝ) * N * Real.log b := by positivity
    have t1 : 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b ≤ C * D.R.f * N * b * Real.log b :=
      calc 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b = 144 * ((D.R.f * N * Real.log b) * N) := by ring
        _ ≤ 144 * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ ≤ C * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ = C * D.R.f * N * b * Real.log b := by ring
    have hCm : (6 : ℝ) ≤ C * D.R.m := by
      have := mul_le_mul hC hm0 (by norm_num) (by linarith)
      linarith
    have t2 : 6 * ((N : ℝ) ^ 2 * sig ch.G) ≤ (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G) :=
      mul_le_mul_of_nonneg_right hCm (by positivity)
    calc 3 * (D.R.m : ℝ) * K0 = D.R.m * (144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b + 6 * ((N : ℝ) ^ 2 * sig ch.G)) := by
          rw [hK0]; ring
      _ ≤ D.R.m * (C * D.R.f * N * b * Real.log b + (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_left (add_le_add t1 t2) hm00
      _ = D.R.m * aOne ch.G C b := by rw [aOne]; ring
  have hexp : Real.exp K0 ^ (2 * D.R.m + 1) ≤ Real.exp (D.R.m * aOne ch.G C b) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 key
  refine ⟨?_, fun Φ β hβ => ?_⟩
  ·
    have h := (GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow ch.G ch.S.N).trans
      (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G (.top 0) (by simp [DefNode])) _ (Nat.cast_nonneg _) hmod)
    refine h.trans (hMK.trans ((le_self_pow₀ (Real.one_le_exp hK00) (by omega)).trans hexp))
  ·
    rw [GridChoice.Classes, Nat.card_prod, Nat.card_pi, Nat.card_pi]
    push_cast
    have hT : ∏ j : Fin D.R.m, (Nat.card (FinCl (ch.G.V (.top j)) (ch.S.levTop A.μ0 Φ β j j.2)) : ℝ) ≤ M ^ D.R.m := by
      calc _ ≤ ∏ _j : Fin D.R.m, M := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun j _ =>
            fin (.top j) (by simp [DefNode]) _
            (hTop Φ β hβ j)
        _ = _ := by simp
    have hR : ∏ i : Fin (D.R.m + 1), (Nat.card (FinCl (ch.G.V (.grid i D.R.m))
        (ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2))) : ℝ) ≤ M ^ (D.R.m + 1) := by
      calc _ ≤ ∏ _i : Fin (D.R.m + 1), M := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ =>
            fin (.grid i D.R.m) (by simp [DefNode]; omega) _
            (hRow i)
        _ = _ := by simp
    calc _ ≤ M ^ D.R.m * M ^ (D.R.m + 1) := mul_le_mul hT hR (by positivity) (by positivity)
      _ = M ^ (2 * D.R.m + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ Real.exp K0 ^ (2 * D.R.m + 1) := pow_le_pow_left₀ hM0 hMK _
      _ ≤ _ := hexp

end GlobalTheory.ClassCount

end
