import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PhaseReal

variable {D : D7}

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j
  rfl

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i`.
-/
theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram :=
  Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a x => rfl`. Consider the case `add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]`.
-/
theorem infPart_cA (z : AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

/- English proof (translation)
Simplify using `only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`.
-/
theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `hz : (y * (adj D C' * V.gram))ᴴ = V.gram * C' * adj D y`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, gram_ct, adj_eq, adj_eq, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `hu : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D)`. Rewrite using `[Matrix.map_mul]`. Both sides reduce to the same expression.

Establish `hu' : ((isoPart V W C' (y.map (incA D))).map (cA D))ᵀ = (V.gram * C' * adj D y).map (incA D)`. Rewrite using `[hu, ← hz]`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]`. Conclude with `GlobalTheory.DualPairCheck.cA_incA _`.

Establish `e1 : (V.gram⁻¹).map (incA D) * (V.gram * C' * adj D y).map (incA D) * W.gram.map (incA D) = C'.map (incA D) * (adj D y * W.gram).map (incA D)`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]`. Use `congr 1`. Rewrite using `[Matrix.mul_assoc V.gram, Matrix.nonsing_inv_mul_cancel_left _ _ (Formalism.L2.Theta.gram_det_ne V).isUnit, Matrix.mul_assoc]`. Establish `e2 : (adj D C * V.gram).map (incA D) * C'.map (incA D) = 1`.

Rewrite using `[← Matrix.map_mul, hC]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `e3 : isoPart V W C κ = κ * (adj D C * V.gram).map (incA D)` using `rfl`. Rewrite using `[hO_eq_trace, hu', e1, e3, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one]`.
-/
theorem hO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    hO V W (isoPart V W C κ) (isoPart V W C' (y.map (incA D))) =
      Matrix.trace ((adj D y * W.gram).map (incA D) * κ) := by
  have hz : (y * (adj D C' * V.gram))ᴴ = V.gram * C' * adj D y := by
    rw [conjTranspose_mul, conjTranspose_mul, gram_ct, adj_eq, adj_eq, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hu : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D) := by
    rw [Matrix.map_mul]
    rfl
  have hu' : ((isoPart V W C' (y.map (incA D))).map (cA D))ᵀ = (V.gram * C' * adj D y).map (incA D) := by
    rw [hu, ← hz]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.cA_incA _
  have e1 : (V.gram⁻¹).map (incA D) * (V.gram * C' * adj D y).map (incA D) * W.gram.map (incA D) =
      C'.map (incA D) * (adj D y * W.gram).map (incA D) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_assoc V.gram, Matrix.nonsing_inv_mul_cancel_left _ _ (Formalism.L2.Theta.gram_det_ne V).isUnit,
      Matrix.mul_assoc]
  have e2 : (adj D C * V.gram).map (incA D) * C'.map (incA D) = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e3 : isoPart V W C κ = κ * (adj D C * V.gram).map (incA D) := rfl
  rw [hO_eq_trace, hu', e1, e3, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, e2,
    Matrix.mul_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [pairQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`.
-/
theorem pairQ_map (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (pairQ W y).map (incA D) = incA D D.host.xi0 • (adj D y * W.gram).map (incA D) := by
  ext i j
  simp only [pairQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

/- English proof (translation)
Unfold `symplO`. Rewrite using `[← GlobalTheory.FinTranslate.hO_herm, hO_iso V W C C' hC, pairQ_map, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imagi …`.
-/
theorem symplO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    symplO V W (isoPart V W C' (y.map (incA D))) (isoPart V W C κ) =
      -Algebra.trace (AF D.host.F) (AE D) (Matrix.trace ((pairQ W y).map (incA D) * κ)) := by
  unfold symplO
  rw [← GlobalTheory.FinTranslate.hO_herm, hO_iso V W C C' hC, pairQ_map, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

/- English proof (translation)
Establish `h : ∀ i j, finPart D (κ i j) = 0` using `fun i j => congrFun (congrFun hκ i) j`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]`.
-/
theorem finPart_trace {m n : ℕ} (P : Matrix (Fin n) (Fin m) (AE D)) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) : finPart D (Matrix.trace (P * κ)) = 0 := by
  have h : ∀ i j, finPart D (κ i j) = 0 := fun i j => congrFun (congrFun hκ i) j
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Establish `h3 : GlobalTheory.FinTranslate.eInf D * Algebra.trace (AF D.host.F) (AE D) t = Algebra.trace (AF D.host.F) (AE D) t` using `by conv_rhs => rw [← GlobalTheory.FinTranslate.smul_eq_self_of_fin h, map_smul, smul_eq_mul]`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `congrArg Prod.snd h3` as an intermediate fact. Conclude with `this.symm.trans (zero_mul _)`.
-/
theorem trace_real {t : AE D} (h : finPart D t = 0) :
    Algebra.trace (AF D.host.F) (AE D) t =
      pairA D.host.F (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t)) 0 := by
  have h3 : GlobalTheory.FinTranslate.eInf D * Algebra.trace (AF D.host.F) (AE D) t =
      Algebra.trace (AF D.host.F) (AE D) t := by
    conv_rhs => rw [← GlobalTheory.FinTranslate.smul_eq_self_of_fin h, map_smul, smul_eq_mul]
  refine Prod.ext rfl ?_
  have := congrArg Prod.snd h3
  exact this.symm.trans (zero_mul _)

/- English proof (translation)
Establish `hcm` using `Formalism.MainNotions.UnusedSlot34.isCMExt_D D`. Establish `hA : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t) = t + cA D t` using `GlobalTheory.SelfDualLatticeCompare.trace_tensor (AF D.host.F) hcm t`. Establish `hB` using `congrArg (infPart D) hA`. Rewrite `hB` using `[map_add, infPart_cA]`. Establish `hC : infPart D (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t)) = fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`.

Rewrite using `[← hC, hB, map_add, GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ ρ), Complex.add_conj]`.
-/
theorem theta_trace (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : AE D) :
    θ ρ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) := by
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hA : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t) = t + cA D t :=
    GlobalTheory.SelfDualLatticeCompare.trace_tensor (AF D.host.F) hcm t
  have hB := congrArg (infPart D) hA
  rw [map_add, infPart_cA] at hB
  have hC : infPart D (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t)) =
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [← hC, hB, map_add, GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ ρ), Complex.add_conj]

/- English proof (translation)
Establish `h : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e` using `fun e => (hθ ρ).1 e`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt, h]`.
-/
theorem theta_pair (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) D.host.E) (κ : Mx D m n) :
    θ ρ (infPart D (Matrix.trace (P.map (incA D) * κ))) =
      Matrix.trace (P.map (tauE D ρ) * compAt θ ρ κ) := by
  have h : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hθ ρ).1 e
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt, h]

end GlobalTheory.PhaseReal

/- English proof (translation)
Introduce `D V W r C C' hC ψ hψ θ hθ y κ hκ`. Unfold `phase`. Rewrite using `[GlobalTheory.PhaseReal.symplO_iso V W C C' hC]`. Use `set t := Matrix.trace ((pairQ W y).map (incA D) * κ) with ht`. Establish `hfin : finPart D t = 0` using `GlobalTheory.PhaseReal.finPart_trace _ κ hκ`.

Establish `hT` using `GlobalTheory.PhaseReal.trace_real hfin`. Use `set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef`. Establish `h1 : ψ (-T) = psiInf D.host.F ψ (-(fstA D.host.F T))`. Unfold `psiInf`. Use `congr 1`.

Rewrite using `[hT]`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Conclude with `neg_zero`. Establish `h2` using `hψ.2.2 θ hθ (-(fstA D.host.F T))`. Establish `h3 : ∀ ρ, θ ρ ((-(fstA D.host.F T)) ⊗ₜ[D.host.F] (1 : D.host.E)) = -((2 * (Matrix.trace ((pairQ W y).map (tauE D ρ) * compAt θ ρ κ)).re : ℝ) : ℂ)`.

Introduce `ρ`. Rewrite using `[TensorProduct.neg_tmul, map_neg, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, ht, GlobalTheory.PhaseReal.theta_pair θ hθ ρ]`. Rewrite using `[h1, h2]`. Use `congr 1`. Simplify using `only [h3, Finset.sum_neg_distrib]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.PhaseReal.phase_eq : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  intro D V W r C C' hC ψ hψ θ hθ y κ hκ
  unfold phase
  rw [GlobalTheory.PhaseReal.symplO_iso V W C C' hC]
  set t := Matrix.trace ((pairQ W y).map (incA D) * κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ (-T) = psiInf D.host.F ψ (-(fstA D.host.F T)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F T))
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F T)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace ((pairQ W y).map (tauE D ρ) * compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, ht,
      GlobalTheory.PhaseReal.theta_pair θ hθ ρ]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring
