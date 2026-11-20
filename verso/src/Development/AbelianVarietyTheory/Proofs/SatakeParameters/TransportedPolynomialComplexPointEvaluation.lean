import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open MvPolynomial

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`. Consider the case `mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]`.
-/
theorem transpC_eval_aeval {σ κ : Type} (x : κ → ℂ) (g : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    eval x (aeval g Q) = eval (fun i => eval x (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

/- English proof (translation)
Proceed by induction on `R using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]`. Consider the case `mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_X, eval_X, eval_X, map_mul]`.
-/
theorem transpC_map_eval {σ Kc : Type} [CommRing Kc] (ι : ℂ →+* Kc) (x : σ → ℂ) (R : MvPolynomial σ ℂ) :
    eval (fun i => ι (x i)) (map ι R) = ι (eval x R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_X, eval_X, eval_X, map_mul]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C c => simp [MvPolynomial.algebraMap_apply, hφ]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`. Consider the case `mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]`.
-/
theorem transpC_hom_aeval {σ ι' κ : Type} (φ : MvPolynomial ι' (MvPolynomial κ ℂ) →+* ℂ) (hφ : ∀ c, φ (C (C c)) = c)
    (g : σ → MvPolynomial ι' (MvPolynomial κ ℂ)) (Q : MvPolynomial σ ℂ) :
    φ (aeval g Q) = eval (fun i => φ (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.algebraMap_apply, hφ]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

/- English proof (translation)
Establish `hB : IsBor (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ))` using `fun τ => ⟨fun r c hcr => by simp [Matrix.one_apply_ne hcr.ne'], fun r => by simp [hs τ]⟩`. Establish `h1 : colSub (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) Q = _` using `hQ _ hB`. Establish `h2` using `congrArg (eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)) h1`. Simplify using `only [colSub, transpC_eval_aeval, smul_eval] at h2`. Establish `h3 : (∏ τ, ∏ r, (s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) r r ^ ν τ r) = ∏ τ, ∏ r, s τ ^ ν τ r` using `by simp`.

Rewrite `h2` using `[h3]`. Unfold `GL3Theta.evFr`. Rewrite using `[← h2]`. Use `congrArg (fun x => eval x Q) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Simplify using `[Matrix.smul_apply, Matrix.one_apply, mul_comm]`.
-/
theorem evFr_scalar_of_wtPol (D : D7) {N : ℕ} (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (s : D.what₂.Tau → ℂ) (hs : ∀ τ, s τ ≠ 0) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D Q (fun τ => s τ • y τ) = (∏ τ, ∏ r, s τ ^ ν τ r) * GL3Theta.evFr D Q y := by
  have hB : IsBor (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun τ =>
    ⟨fun r c hcr => by simp [Matrix.one_apply_ne hcr.ne'], fun r => by simp [hs τ]⟩
  have h1 : colSub (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) Q = _ := hQ _ hB
  have h2 := congrArg (eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)) h1
  simp only [colSub, transpC_eval_aeval, smul_eval] at h2
  have h3 : (∏ τ, ∏ r, (s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) r r ^ ν τ r) = ∏ τ, ∏ r, s τ ^ ν τ r := by simp
  rw [h3] at h2
  unfold GL3Theta.evFr
  rw [← h2]
  refine congrArg (fun x => eval x Q) ?_
  funext k
  simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]

/- English proof (translation)
Unfold `polDY`. Rewrite using `[transpC_hom_aeval _ (fun c => by simp)]`. Unfold `GL3Theta.evFr`. Use `congrArg (fun x => MvPolynomial.eval x Q) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Establish `hk : ((k.2.2 : Fin N) : ℕ) < N'` using `lt_of_lt_of_le k.2.2.2 hle`. Simplify using `[dfr, Matrix.mul_apply, Finset.mul_sum, hk]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, mul_comm (f' k.1 b _)]`. Both sides reduce to the same expression.
-/
theorem transpC_polDY_eval (D : D7) {N N' : ℕ} (hle : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (d : D.what₂.Tau → Matrix (Fin N) (Fin N') ℂ) (f' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D N' => f' k.1 k.2.1 k.2.2)) (fun k : GL3Theta.Idx D N N' => d k.1 k.2.2 k.2.1)
        (polDY D s Q (N' := N')) =
      GL3Theta.evFr D Q (fun τ => s τ • (d τ * f' τ).submatrix id (Fin.castLE hle)) := by
  unfold polDY
  rw [transpC_hom_aeval _ (fun c => by simp)]
  unfold GL3Theta.evFr
  refine congrArg (fun x => MvPolynomial.eval x Q) ?_
  funext k
  have hk : ((k.2.2 : Fin N) : ℕ) < N' := lt_of_lt_of_le k.2.2.2 hle
  simp [dfr, Matrix.mul_apply, Finset.mul_sum, hk]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, mul_comm (f' k.1 b _)]
  rfl

/- English proof (translation)
Introduce `p _ X D pos Kc _ _ ι j hN ν hν Q hQ s hs d f' hf`. Establish `h'` using `rkT X D hN`. Take `⟨-, hsz, -, hle, -⟩` from `GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν`. Establish `hco` using `(GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero D (rk_le X D hN) s ν Q hQ).1`. Establish `hreal : ∀ α, Realises X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N'` using `D.R.N (j + 1)))) (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) := by`.

Introduce `α`. Take `⟨R, hR⟩` from `GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j h' (extNu _ ν) hle _ (hco α)`. Conclude with `selOf_mem (relPhi X D pos (j + 1) h' (wT X D pos j)) _ (Submodule.mem_map.2 ⟨(_, R), hR, rfl⟩)`. Set `F : Fr1 D (D.R.N (j + 1))` to `⟨f', fun τ => isUnit_iff_ne_zero.2 (hf τ)⟩`. Establish `hval : ∀ α, (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) * valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N'` using `D.R.N (j + 1))))) f' = (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' := by`.

Introduce `α`. Use `hreal α F` as an intermediate fact. Rewrite `this` using `[ev1_eq_prod_det_pow_mul_valZ]`. Conclude with `this`. Establish `hD : evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N'` using `D.R.N (j + 1)))) = ι (∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by`.

Unfold `trDY`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Unfold `evD`. Rewrite using `[MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`.

Unfold `phi0`. Rewrite using `[dif_pos h', map_mul, map_prod]`. Use `congr 1`. Unfold `valZ`. Conclude with `transpC_map_eval ι _ _`.

Unfold `Finsupp.prod`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[eIdx, map_pow]`. Establish `hP : ∑ α ∈ (polDY D s Q (N'` using `D.R.N (j + 1))).support, GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k = (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f') := by`. Set `φ : MvPolynomial (GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1))) (MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ) →+* ℂ` to `MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (j + 1)) => f' k.1 k.2.1 k.2.2)) (fun k => d k.1 k.2.2 k.2.1)`.

Establish `e1 : φ (polDY D s Q (N'` using `D.R.N (j + 1))) = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k := by`. Rewrite using `[MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]`. Both sides reduce to the same expression. Establish `e2 : φ (polDY D s Q (N'` using `D.R.N (j + 1))) = GL3Theta.evFr D Q (fun τ => s τ • dfr X D hN d f' τ) := transpC_polDY_eval D (rk_le X D hN) s Q d f'`. Establish `e3 : ∀ τ, ∏ r, s τ ^ ν τ r = s τ ^ szT X D pos j τ`.

Introduce `τ`. Rewrite using `[hsz τ, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast]`. Rewrite using `[← e1, e2, evFr_scalar_of_wtPol D ν Q hQ s hs]`. Simplify using `only [e3]`. Rewrite using `[hD, ← map_mul]`.

Use `congr 1`. Rewrite using `[Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← hval α]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [← Finset.mul_sum, hP, mul_assoc]`.
-/
theorem evD_trDY_polDY : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ s hs d f' hf
  classical
  have h' := rkT X D hN
  obtain ⟨-, hsz, -, hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hco := (GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero D (rk_le X D hN) s ν Q hQ).1
  have hreal : ∀ α, Realises X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))
      (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) := by
    intro α
    obtain ⟨R, hR⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j h' (extNu _ ν) hle _ (hco α)
    exact selOf_mem (relPhi X D pos (j + 1) h' (wT X D pos j)) _ (Submodule.mem_map.2 ⟨(_, R), hR, rfl⟩)
  let F : Fr1 D (D.R.N (j + 1)) := ⟨f', fun τ => isUnit_iff_ne_zero.2 (hf τ)⟩
  have hval : ∀ α, (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) *
      valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) f' =
      (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' := by
    intro α
    have := hreal α F
    rw [ev1_eq_prod_det_pow_mul_valZ] at this
    exact this
  have hD : evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) =
      ι (∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) f' *
          ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
    unfold trDY
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    unfold evD
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    unfold phi0
    rw [dif_pos h', map_mul, map_prod]
    congr 1
    · unfold valZ
      exact transpC_map_eval ι _ _
    · unfold Finsupp.prod
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [eIdx, map_pow]
  have hP : ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k =
      (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f') := by
    let φ : MvPolynomial (GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1))) (MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ) →+* ℂ :=
      MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (j + 1)) => f' k.1 k.2.1 k.2.2))
        (fun k => d k.1 k.2.2 k.2.1)
    have e1 : φ (polDY D s Q (N' := D.R.N (j + 1))) = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k := by
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
      rfl
    have e2 : φ (polDY D s Q (N' := D.R.N (j + 1))) = GL3Theta.evFr D Q (fun τ => s τ • dfr X D hN d f' τ) :=
      transpC_polDY_eval D (rk_le X D hN) s Q d f'
    have e3 : ∀ τ, ∏ r, s τ ^ ν τ r = s τ ^ szT X D pos j τ := by
      intro τ
      rw [hsz τ, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast]
    rw [← e1, e2, evFr_scalar_of_wtPol D ν Q hQ s hs]
    simp only [e3]
  rw [hD, ← map_mul]
  congr 1
  rw [Finset.sum_mul]
  calc _ = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) *
        (GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← mul_assoc, ← hval α]
        ring
    _ = _ := by rw [← Finset.mul_sum, hP, mul_assoc]

end GlobalTheory.TwV.DelA

end
