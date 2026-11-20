import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def dpW (t : ℂ) : ℝ := (1 + ‖t‖ ^ 2) ^ 2

section Mul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Unfold `dpW`. Establish `h : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => (1 + ‖x.1 l‖ ^ 2) ^ 2)` using `((contDiff_const.add ((contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ ℂ l).comp contDiff_fst))).pow 2)`. Conclude with `Complex.ofRealCLM.contDiff.comp h`.
-/
theorem contDiff_dpW_coord (l : Fin r) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => ((dpW (x.1 l) : ℝ) : ℂ)) := by
  unfold dpW
  have h : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => (1 + ‖x.1 l‖ ^ 2) ^ 2) :=
    ((contDiff_const.add ((contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ ℂ l).comp contDiff_fst))).pow 2)
  exact Complex.ofRealCLM.contDiff.comp h

def dpMul (l : Fin r) : Module.End ℂ (RadSp k r z z' π π') :=
  Formalism.FourierDecayAlt.P5.mulOp (fun x => ((dpW (x.1 l) : ℝ) : ℂ)) (contDiff_dpW_coord l) (fun _ _ _ _ _ _ => rfl)

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P5.mulOp_isMulOp _ _ _`.
-/
theorem dpMul_isMulOp (l : Fin r) :
    Formalism.FourierDecayAlt.P5.multiplicationOperator (dpMul (z := z) (z' := z') (π := π) (π' := π') l) (fun c _ => ((dpW (c l) : ℝ) : ℂ)) :=
  Formalism.FourierDecayAlt.P5.mulOp_isMulOp _ _ _

/- English proof (translation)
Unfold `pairAt`. Repeatedly rewrite using `[dpMul_isMulOp l Ψ c, PBFV.hsInner_smul_right, Complex.conj_ofReal]`. Conclude with `integral_const_mul _ _`.
-/
theorem pairAt_dpMul_right (μ : Measure (Mt k r)) (l : Fin r) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ (dpMul l Ψ) c = ((dpW (c l) : ℝ) : ℂ) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp_rw [dpMul_isMulOp l Ψ c, PBFV.hsInner_smul_right, Complex.conj_ofReal]
  exact integral_const_mul _ _

/- English proof (translation)
Establish `hg : ∀ c' : Cf r l.succ, glue l.succ (Function.update c l t) c' l = t`. Introduce `c'`. Simplify using `[glue]`. Unfold `Dens form`. Repeatedly rewrite using `[pairAt_dpMul_right, hg, ← Finset.mul_sum, mul_left_comm _ ((dpW t : ℝ) : ℂ)]`.

Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_dpMul {S : Type} [Fintype S] [DecidableEq S] (μ : Measure (Mt k r)) (l : Fin r)
    (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    Dens μ l u (fun b => dpMul l (v b)) c t = ((dpW t : ℝ) : ℂ) * Dens μ l u v c t := by
  have hg : ∀ c' : Cf r l.succ, glue l.succ (Function.update c l t) c' l = t := by
    intro c'
    simp [glue]
  unfold Dens form
  simp_rw [pairAt_dpMul_right, hg, ← Finset.mul_sum, mul_left_comm _ ((dpW t : ℝ) : ℂ)]
  rw [integral_const_mul]
  ring

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Use `show (dpMul l (W Φ) : Fn k r (Wq →L[ℂ] Wp)) c g = (W (dpMul l Φ) : Fn k r (Wq →L[ℂ] Wp)) c g`. Rewrite using `[dpMul_isMulOp l, hW, hW, dpMul_isMulOp l, smul_comm]`.
-/
theorem dpMul_comm (l : Fin r) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ}
    (hW : Formalism.FourierDecayAlt.P5.multiplicationOperator W m) (Φ : RadSp k r z z' π π') : dpMul l (W Φ) = W (dpMul l Φ) := by
  apply Subtype.ext
  funext c g
  show (dpMul l (W Φ) : Fn k r (Wq →L[ℂ] Wp)) c g = (W (dpMul l Φ) : Fn k r (Wq →L[ℂ] Wp)) c g
  rw [dpMul_isMulOp l, hW, hW, dpMul_isMulOp l, smul_comm]

variable (k r z z' π π') in

def dpSub (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r) :
    Submodule ℂ (RadSp k r z z' π π') :=
  squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ ⊓ (squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ).comap (dpMul l)

/- English proof (translation)
Take `⟨hlc, hL⟩` from `hΦ`. Establish `hp : ∀ c, pairAt μ (Wv Φ) (Wv Φ) c = pairAt μ Φ Φ c`. Introduce `c`. Unfold `pairAt`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[h1 Φ c, B6.hsInner_smul_left, PBFV.hsInner_smul_right, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm, one_pow, Complex.ofReal_one, one_mul]`. Use `⟨?_, fun c => ?_⟩` and prove the remaining obligations. Introduce `c hc`. Take `⟨U, hU, hcU, K, hK, hKs, hv⟩` from `hlc c hc`.

Use `⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 Φ c' g, hv c' hc' g hg hgK, smul_zero]`. Use `hL c` as an intermediate fact. Unfold `LevelZeroSquareIntegrable at this ⊢`. Simplify `this` using `only [hp]`.
-/
private theorem isMulOp_unimodular_preserves_squareIntegrable (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {Wv : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ}
    (h1 : Formalism.FourierDecayAlt.P5.multiplicationOperator Wv m) (hm : ∀ c g, ‖m c g‖ = 1) {Φ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ) : Wv Φ ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ := by
  obtain ⟨hlc, hL⟩ := hΦ
  have hp : ∀ c, pairAt μ (Wv Φ) (Wv Φ) c = pairAt μ Φ Φ c := by
    intro c
    unfold pairAt
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [h1 Φ c, B6.hsInner_smul_left, PBFV.hsInner_smul_right, ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hm, one_pow, Complex.ofReal_one, one_mul]
  refine ⟨?_, fun c => ?_⟩
  · intro c hc
    obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
    refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
    rw [h1 Φ c' g, hv c' hc' g hg hgK, smul_zero]
  · have := hL c
    unfold LevelZeroSquareIntegrable at this ⊢
    simpa only [hp] using this

/- English proof (translation)
Use `⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨ha, hb⟩` from `hΦ`. Use `⟨isMulOp_unimodular_preserves_squareIntegrable μ hμ h1 hm ha, ?_⟩` and prove the remaining obligations. Use `show dpMul l (Wv Φ) ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ`. Rewrite using `[dpMul_comm l h1]`.

Conclude with `isMulOp_unimodular_preserves_squareIntegrable μ hμ h1 hm hb`. Take `⟨ha, hb⟩` from `hΦ`. Use `⟨isMulOp_unimodular_preserves_squareIntegrable μ hμ h2 hm' ha, ?_⟩` and prove the remaining obligations. Use `show dpMul l (Wv' Φ) ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ`. Rewrite using `[dpMul_comm l h2]`.

Conclude with `isMulOp_unimodular_preserves_squareIntegrable μ hμ h2 hm' hb`.
-/
theorem mkPair_mem_preservingAlgebra_of_isMulOp (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r)
    {Wv Wv' : Module.End ℂ (RadSp k r z z' π π')} {m m' : (Fin r → ℂ) → Mx k r → ℂ}
    (h1 : Formalism.FourierDecayAlt.P5.multiplicationOperator Wv m) (h2 : Formalism.FourierDecayAlt.P5.multiplicationOperator Wv' m') (hm : ∀ c g, ‖m c g‖ = 1)
    (hm' : ∀ c g, ‖m' c g‖ = 1) : mkP Wv Wv' ∈ presAlg (dpSub k r z z' π π' μ hμ l) := by
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨ha, hb⟩ := hΦ
    refine ⟨isMulOp_unimodular_preserves_squareIntegrable μ hμ h1 hm ha, ?_⟩
    show dpMul l (Wv Φ) ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ
    rw [dpMul_comm l h1]
    exact isMulOp_unimodular_preserves_squareIntegrable μ hμ h1 hm hb
  · obtain ⟨ha, hb⟩ := hΦ
    refine ⟨isMulOp_unimodular_preserves_squareIntegrable μ hμ h2 hm' ha, ?_⟩
    show dpMul l (Wv' Φ) ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ
    rw [dpMul_comm l h2]
    exact isMulOp_unimodular_preserves_squareIntegrable μ hμ h2 hm' hb

end Mul

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Use `set b := fvec k r z' 0`. Use `set v := fvec k r z 0`. Establish `hD : ∀ g : B.Mat k r, Dmin k r z z' g ⟨1, h1⟩ = herm (Hpk k r) (g *ᵥ b) v`. Introduce `g`. Simplify using `only [Dmin]`.

Rewrite using `[Matrix.det_unique]`. Both sides reduce to the same expression. Set `Lc : B.Mat k r →ₗ[ℝ] ℂ` to `{ toFun := fun g => star (herm (Hpk k r) (g *ᵥ b) v) map_add' := by`. Introduce `g g'`. Simplify using `[herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]`.

Use the proof step `map_smul' := by`. Introduce `c g`. Simplify using `only [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, RingHom.id_apply] }`. Establish `hc : JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => star (herm (Hpk k r) (g *ᵥ b) v))` using `JCx2.pd_good_lin (LinearMap.toContinuousLinearMap Lc)`. Establish `hsq` using `JCx2.pd_good_mul (d := 2) (by norm_num) (JCx2.pd_good_herm (Wp := Wp) (Wq := Wq) b v) hc`.

Establish `h2` using `JCx2.pd_good_add (JCx2.pd_good_const (Wp := Wp) (Wq := Wq) 2 1) hsq`. Establish `h4 : JCx2.pdGood Wp Wq 4 _` using `CutBP.pd_good_pow h2 2`. Establish `hn : ∀ w : ℂ, w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ)` using `fun w => by`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `JCx2.pd_good_congr (fun g _ => ?_) h4` and prove the remaining obligations.

Rewrite using `[hD g, hn]`. Simplify using `only [dpW]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pd_good_dpW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (h1 : 1 < r + 2) :
    JCx2.pdGood Wp Wq 4 (fun g : B.Mat k r => ((dpW (Dmin k r z z' g ⟨1, h1⟩) : ℝ) : ℂ)) := by
  set b := fvec k r z' 0
  set v := fvec k r z 0
  have hD : ∀ g : B.Mat k r, Dmin k r z z' g ⟨1, h1⟩ = herm (Hpk k r) (g *ᵥ b) v := by
    intro g
    simp only [Dmin]
    rw [Matrix.det_unique]
    rfl
  let Lc : B.Mat k r →ₗ[ℝ] ℂ :=
    { toFun := fun g => star (herm (Hpk k r) (g *ᵥ b) v)
      map_add' := by
        intro g g'
        simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := by
        intro c g
        simp only [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, star_mul',
          Complex.star_def, Complex.conj_ofReal, RingHom.id_apply] }
  have hc : JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => star (herm (Hpk k r) (g *ᵥ b) v)) :=
    JCx2.pd_good_lin (LinearMap.toContinuousLinearMap Lc)
  have hsq := JCx2.pd_good_mul (d := 2) (by norm_num) (JCx2.pd_good_herm (Wp := Wp) (Wq := Wq) b v) hc
  have h2 := JCx2.pd_good_add (JCx2.pd_good_const (Wp := Wp) (Wq := Wq) 2 1) hsq
  have h4 : JCx2.pdGood Wp Wq 4 _ := CutBP.pd_good_pow h2 2
  have hn : ∀ w : ℂ, w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine JCx2.pd_good_congr (fun g _ => ?_) h4
  rw [hD g, hn]
  simp only [dpW]
  push_cast
  ring

/- English proof (translation)
Take `⟨⟨hcc, ε, hε, hεF⟩, hcs⟩` from `hF`. Establish `hgood` using `pd_good_dpW (Wp := Wp) (Wq := Wq) P.k P.r z z' h1`. Establish `hsupp : ∀ g, ((dpW (Dmin P.k P.r z z' g ⟨1, h1⟩) : ℝ) : ℂ) • F g ≠ 0 → F g ≠ 0`. Introduce `g hne h0`. Apply `hne` to reduce the goal to its premises.

Simplify using `only [h0, smul_zero]`. Prove the components needed by the constructor for the conclusion. Prove the components needed by the constructor for the conclusion. Introduce `A' m'`. Take `⟨K, -, hK⟩` from `hgood.2 A' m'`.

Take `⟨b, hb⟩` from `hcc (A' + 4) m'`. Conclude with `⟨K * b, hK F b (by exact_mod_cast hb)⟩`. Conclude with `⟨ε, hε, fun g hg hne => hεF g hg (hsupp g hne)⟩`. Conclude with `HasCompactSupport.mono hcs (fun g hg => hsupp g hg)`.
-/
private theorem jfOKCpt_dpW_dmin_smul (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (h1 : 1 < P.r + 2)
    (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F) :
    JFOKCpt P z z' (fun g => ((dpW (Dmin P.k P.r z z' g ⟨1, h1⟩) : ℝ) : ℂ) • F g) := by
  obtain ⟨⟨hcc, ε, hε, hεF⟩, hcs⟩ := hF
  have hgood := pd_good_dpW (Wp := Wp) (Wq := Wq) P.k P.r z z' h1
  have hsupp : ∀ g, ((dpW (Dmin P.k P.r z z' g ⟨1, h1⟩) : ℝ) : ℂ) • F g ≠ 0 → F g ≠ 0 := by
    intro g hne h0
    apply hne
    simp only [h0, smul_zero]
  constructor
  · constructor
    · intro A' m'
      obtain ⟨K, -, hK⟩ := hgood.2 A' m'
      obtain ⟨b, hb⟩ := hcc (A' + 4) m'
      exact ⟨K * b, hK F b (by exact_mod_cast hb)⟩
    · exact ⟨ε, hε, fun g hg hne => hεF g hg (hsupp g hne)⟩
  · exact HasCompactSupport.mono hcs (fun g hg => hsupp g hg)

/- English proof (translation)
Establish `hr : 0 < P.r` using `Fin.pos l`. Establish `h1 : 1 < P.r + 2` using `by omega`. Establish `hl' : l = ⟨0, hr⟩` using `Fin.ext hl`. Establish `hF'` using `jfOKCpt_dpW_dmin_smul P z z' h1 F hF`. Establish `hinv : ∀ p : B.SS P.k P.r, D.inSS p → ∀ g : B.Mat P.k P.r, ((dpW (Dmin P.k P.r z z' (B.sgs p g) ⟨1, h1⟩) : ℝ) : ℂ) = ((dpW (Dmin P.k P.r z z' g ⟨1, h1⟩) : ℝ) : ℂ)`.

Introduce `p hp g`. Establish `h` using `BigCellZetaMinors.dmin_sgs D hp g ⟨1, h1⟩`. Rewrite `h` using `[hz, hz']`. Rewrite using `[h]`. Use `radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' _ hF' (dpMul l Φ) ?_` and prove the remaining obligations.

Introduce `x hx`. Rewrite using `[dpMul_isMulOp l Φ x.1 x.2, hΦ x hx]`. Simplify using `only [resG]`. Rewrite using `[PBFV.JF_mul_inv D _ hinv F, PBFV.first_minor_cell_eq_coord hP.2.1 hP.2.2.1 hr x.1 hx.2.1 h1, ← hl', smul_comm]`.
-/
theorem jf_dp (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) (l : Fin P.r)
    (hl : l.val = 0) : dpMul l Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  have hr : 0 < P.r := Fin.pos l
  have h1 : 1 < P.r + 2 := by omega
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have hF' := jfOKCpt_dpW_dmin_smul P z z' h1 F hF
  have hinv : ∀ p : B.SS P.k P.r, D.inSS p → ∀ g : B.Mat P.k P.r,
      ((dpW (Dmin P.k P.r z z' (B.sgs p g) ⟨1, h1⟩) : ℝ) : ℂ) = ((dpW (Dmin P.k P.r z z' g ⟨1, h1⟩) : ℝ) : ℂ) := by
    intro p hp g
    have h := BigCellZetaMinors.dmin_sgs D hp g ⟨1, h1⟩
    rw [hz, hz'] at h
    rw [h]
  refine radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' _ hF' (dpMul l Φ) ?_
  intro x hx
  rw [dpMul_isMulOp l Φ x.1 x.2, hΦ x hx]
  simp only [resG]
  rw [PBFV.JF_mul_inv D _ hinv F, PBFV.first_minor_cell_eq_coord hP.2.1 hP.2.2.1 hr x.1 hx.2.1 h1, ← hl', smul_comm]

/- English proof (translation)
Establish `hr : 0 < P.r` using `Fin.pos l`. Establish `hio : ∀ f ∈ presAlg (dpSub P.k P.r z z' π π' μ hμ l), (io f : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈ entSub (presAlg (dpSub P.k P.r z z' π π' μ hμ l))`. Introduce `f hf i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify `hf` using `[io]`. Simplify using `[io, Matrix.diagonal_apply_ne _ hij]`. Establish `key : ∀ i Φ, HerGenC S P z z' π π' L st l0 D i Φ → i = 0 → Φ ∈ dpSub P.k P.r z z' π π' μ hμ l`. Introduce `i Φ h`. Proceed by induction on `h with`.

Consider the case `jf F Φ hF hΦ`. Introduce `_`. Conclude with `⟨radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ, jf_dp P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ l hl⟩`. Consider the case `slice l' w a b Φ _ _ _`. Introduce `h0`.

Conclude with `absurd h0 (Fin.succ_ne_zero l')`. Consider the case `waveC l' w s Wv Wv' a b Φ _ h2 h3 _ ih`. Introduce `h0`. Establish `hΦ` using `ih h0`. Establish `hm : mkP Wv Wv' ∈ presAlg (dpSub P.k P.r z z' π π' μ hμ l)` using `mkPair_mem_preservingAlgebra_of_isMulOp μ hμ l h2 h3 (fun c g => norm_fsv s (c l')) (fun c g => norm_fsv (-s) (c l'))`.

Establish `hV : Vw (mkP Wv Wv') s w ∈ entSub (presAlg (dpSub P.k P.r z z' π π' μ hμ l))` using `Subalgebra.mul_mem _ (hio _ hm) (UUiw_mem s w)`. Conclude with `(hV a b).1 Φ hΦ`. Consider the case `_`. Introduce `h0`. Use `congrArg Fin.val h0` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Conclude with `Submodule.span_le.mpr (fun Φ hΦ => key 0 Φ hΦ rfl)`.
-/
theorem herKc0_le_dp (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.val = 0) :
    herKc S P z z' π π' L st l0 D 0 ≤ dpSub P.k P.r z z' π π' μ hμ l := by
  have hr : 0 < P.r := Fin.pos l
  have hio : ∀ f ∈ presAlg (dpSub P.k P.r z z' π π' μ hμ l),
      (io f : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈ entSub (presAlg (dpSub P.k P.r z z' π π' μ hμ l)) := by
    intro f hf i j
    by_cases hij : i = j
    · subst hij
      simpa [io] using hf
    · simp [io, Matrix.diagonal_apply_ne _ hij]
  have key : ∀ i Φ, HerGenC S P z z' π π' L st l0 D i Φ → i = 0 →
      Φ ∈ dpSub P.k P.r z z' π π' μ hμ l := by
    intro i Φ h
    induction h with
    | jf F Φ hF hΦ =>
      intro _
      exact ⟨radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ,
        jf_dp P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ l hl⟩
    | slice l' w a b Φ _ _ _ =>
      intro h0
      exact absurd h0 (Fin.succ_ne_zero l')
    | waveC l' w s Wv Wv' a b Φ _ h2 h3 _ ih =>
      intro h0
      have hΦ := ih h0
      have hm : mkP Wv Wv' ∈ presAlg (dpSub P.k P.r z z' π π' μ hμ l) :=
        mkPair_mem_preservingAlgebra_of_isMulOp μ hμ l h2 h3 (fun c g => norm_fsv s (c l')) (fun c g => norm_fsv (-s) (c l'))
      have hV : Vw (mkP Wv Wv') s w ∈ entSub (presAlg (dpSub P.k P.r z z' π π' μ hμ l)) :=
        Subalgebra.mul_mem _ (hio _ hm) (UUiw_mem s w)
      exact (hV a b).1 Φ hΦ
    | _ =>
      intro h0
      have := congrArg Fin.val h0
      simp at this
      omega
  exact Submodule.span_le.mpr (fun Φ hΦ => key 0 Φ hΦ rfl)

end Classes

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl0 hl0' hz hz' hπ hπ' w hw l hl x v hx hv c hc n`. Establish `hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ` using `hD.2.1`. Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩`. Establish `hr : 0 < P.r` using `Fin.pos l`. Establish `h0 : l.castSucc = (0 : Fin (P.r + 1))` using `Fin.ext (by simp [hl])`.

Rewrite `hx`, `hv`, the goal using `[h0]`. Establish `hle` using `herKc0_le_dp (S := S) P z z' π π' μ hμ L st l0 D hD.1 hz hz' hπ hπ' l hl`. Establish `hxd : ∀ b, x b ∈ dpSub P.k P.r z z' π π' μ hμ l` using `fun b => hle (hx b)`. Establish `hvd : ∀ b, v b ∈ dpSub P.k P.r z z' π π' μ hμ l` using `fun b => hle (hv b)`. Establish `hstar : ∀ a ∈ w, star a.pt = a.pt`.

Introduce `a ha`. Conclude with `Complex.conj_eq_iff_im.mpr (hw.2.1 a ha).1`. Establish `hRR` using `RRi_lc X μ L st l0 hD 0 w hstar`. Establish `hulc : ∀ a, act (RRi L st 0 w) x a ∈ lcSub P.k P.r z z' π π'`. Introduce `a`.

Conclude with `Submodule.sum_mem _ (fun b _ => (hRR a b).1 (x b) (hxd b).1.1)`. Establish `hul2 : ∀ a, LevelSquareIntegrable μ (0 : Fin (P.r + 1)) (act (RRi L st 0 w) x a) c` using `fun a => rRL2Lev0Pos Wp Wq S P z z' π π' X μ L st l0 D hD hl0 hl0' hz hz' hπ hπ' hr w hw x hx a c hc`. Establish `hvlc : ∀ a, dpMul l (v a) ∈ lcSub P.k P.r z z' π π'` using `fun a => (hvd a).2.1`. Establish `hvl2 : ∀ a, LevelSquareIntegrable μ (0 : Fin (P.r + 1)) (dpMul l (v a)) c` using `fun a => (hvd a).2.2 c`. Establish `hint` using `(dens_int μ hμ l (act (RRi L st 0 w) x) (fun b => dpMul l (v b)) hulc hvlc c (by rw [h0]; exact hul2) (by rw [h0]; exact hvl2)).1`.

Establish `heq : (fun t : ℂ => (1 + ‖t‖ ^ 2) ^ 2 • Dens μ l (act (RRi L st 0 w) x) v c t) = Dens μ l (act (RRi L st 0 w) x) (fun b => dpMul l (v b)) c`. Use function extensionality and compare the values at `t`. Rewrite using `[dens_dpMul, Complex.real_smul]`. Simplify using `only [dpW]`. Rewrite using `[heq]`.

Conclude with `hint`.
-/
theorem decay_pair_estimate : DecayPair1 := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl0 hl0' hz hz' hπ hπ' w hw l hl x v hx hv c hc n
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hr : 0 < P.r := Fin.pos l
  have h0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  rw [h0] at hx hv ⊢
  have hle := herKc0_le_dp (S := S) P z z' π π' μ hμ L st l0 D hD.1 hz hz' hπ hπ' l hl
  have hxd : ∀ b, x b ∈ dpSub P.k P.r z z' π π' μ hμ l := fun b => hle (hx b)
  have hvd : ∀ b, v b ∈ dpSub P.k P.r z z' π π' μ hμ l := fun b => hle (hv b)
  have hstar : ∀ a ∈ w, star a.pt = a.pt := by
    intro a ha
    exact Complex.conj_eq_iff_im.mpr (hw.2.1 a ha).1
  have hRR := RRi_lc X μ L st l0 hD 0 w hstar
  have hulc : ∀ a, act (RRi L st 0 w) x a ∈ lcSub P.k P.r z z' π π' := by
    intro a
    exact Submodule.sum_mem _ (fun b _ => (hRR a b).1 (x b) (hxd b).1.1)
  have hul2 : ∀ a, LevelSquareIntegrable μ (0 : Fin (P.r + 1)) (act (RRi L st 0 w) x a) c := fun a =>
    rRL2Lev0Pos Wp Wq S P z z' π π' X μ L st l0 D hD hl0 hl0' hz hz' hπ hπ' hr w hw x hx a c hc
  have hvlc : ∀ a, dpMul l (v a) ∈ lcSub P.k P.r z z' π π' := fun a => (hvd a).2.1
  have hvl2 : ∀ a, LevelSquareIntegrable μ (0 : Fin (P.r + 1)) (dpMul l (v a)) c := fun a => (hvd a).2.2 c
  have hint := (dens_int μ hμ l (act (RRi L st 0 w) x) (fun b => dpMul l (v b)) hulc hvlc c
    (by rw [h0]; exact hul2) (by rw [h0]; exact hvl2)).1
  have heq : (fun t : ℂ => (1 + ‖t‖ ^ 2) ^ 2 • Dens μ l (act (RRi L st 0 w) x) v c t) =
      Dens μ l (act (RRi L st 0 w) x) (fun b => dpMul l (v b)) c := by
    funext t
    rw [dens_dpMul, Complex.real_smul]
    simp only [dpW]
  rw [heq]
  exact hint

end Formalism.FourierDecayAlt.P.CutSE
