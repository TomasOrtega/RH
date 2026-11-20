import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.KerForm

open Classical

/- English proof (translation)
Establish `hs : frInv O i ∘ₗ frPoly O i = LinearMap.id` using `Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id) (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (Formalism.L2.Ker.frobenius_poly_injective D u C O i hi)))`. Conclude with `LinearMap.congr_fun hs Q`.
-/
theorem frInv_leftInv {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) {i : ℕ}
    (hi : i ≤ D.R.m) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : frInv O i (frPoly O i Q) = Q := by
  have hs : frInv O i ∘ₗ frPoly O i = LinearMap.id :=
    Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id)
      (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (Formalism.L2.Ker.frobenius_poly_injective D u C O i hi)))
  exact LinearMap.congr_fun hs Q

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[evC_sec]`. Use `show (∏ τ, ((D.chTw u μ).de i y τ) ^ ((D.chTw u μ).sSharp i τ)) * ((∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) * GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)) = _`. Use `show _ = GL3Theta.evFr D _ ((O u μ).frm i y)`. Unfold `srcPol GL3Theta.evFr`.

Rewrite using `[map_mul, map_mul, map_prod, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_pow, eval_detP, ← (O u μ).frm_de i hi.le y τ, ← zpow_add₀ ((D.chTw u μ).de_ne i y τ), ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (twLe D u μ i hi τ)), sub_eq_add_neg]`.
-/
theorem sharp_evC (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (v : ValQ O u μ i) :
    (D.chTw u μ).sharp i (evC O u μ i v) = frPoly (O u μ) i
      (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  funext y
  rw [evC_sec]
  show (∏ τ, ((D.chTw u μ).de i y τ) ^ ((D.chTw u μ).sSharp i τ)) * ((∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) *
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)) = _
  show _ = GL3Theta.evFr D _ ((O u μ).frm i y)
  unfold srcPol GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP, ← (O u μ).frm_de i hi.le y τ, ← zpow_add₀ ((D.chTw u μ).de_ne i y τ), ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.2 (twLe D u μ i hi τ)), sub_eq_add_neg]

/- English proof (translation)
Introduce `D O u μ i hi hU c c' v v' h`. Use `set Q := MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) with hQ`. Use `set Q' := MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) with hQ'`. Use `set ρ : ℂ := ((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) with hρ`. Establish `hunf : (D.chTw u μ).unf i c c' (frPoly (O u μ) i Q) = frPoly (O u μ) (i + 1) (jetMap (ι` using `D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) := by`.

Rewrite using `[hU c c' Q]`. Unfold `unfC`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, frInv_leftInv (O u μ) hi.le]`. Establish `hrho : (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c' = ρ`. Rewrite using `[((O u μ).c13 i hi).1 c, ((O u μ).c13 i hi).2 c']`.

Apply `Formalism.L2.Ker.frobenius_poly_injective D u (D.chTw u μ) (O u μ) (i + 1) hi` to reduce the goal to its premises. Use function extensionality and compare the values at `y'`. Establish `h1` using `congrFun h y'`. Rewrite `h1` using `[ColumnChain.Kmap, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, sharp_evC D O u μ i hi v, hunf, hrho]`. Rewrite `h1` using `[evC_sec]`.

Express the relevant statement in the definitionally equal form `(∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) * GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = ρ * ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ * frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (f …`. Establish `hne : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne (i + 1) y' τ)`. Establish `hinv : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) = (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹`. Rewrite using `[← Finset.prod_inv_distrib]`. Conclude with `Finset.prod_congr rfl fun τ _ => zpow_neg _ _`.

Rewrite `h1` using `[hinv]`. Establish `h2 : GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = ρ * frPoly (O u μ) (i + 1) (jetMap (ι` using `D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y' := by`. Use `inv_ne_zero hne` as an intermediate fact. Apply `mul_left_cancel₀ this` to reduce the goal to its premises. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree. Use `show GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = GL3Theta.evFr D _ ((O u μ).frm (i + 1) y')`. Rewrite using `[h2]`. Simplify using `[frPoly, GL3Theta.evFr]`.
-/
theorem complex_kform : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  intro D O u μ i hi hU c c' v v' h
  set Q := MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) with hQ
  set Q' := MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) with hQ'
  set ρ : ℂ := ((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) with hρ
  have hunf : (D.chTw u μ).unf i c c' (frPoly (O u μ) i Q) =
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) := by
    rw [hU c c' Q]
    unfold unfC
    rw [LinearMap.comp_apply, LinearMap.comp_apply, frInv_leftInv (O u μ) hi.le]
  have hrho : (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c' = ρ := by
    rw [((O u μ).c13 i hi).1 c, ((O u μ).c13 i hi).2 c']
  apply Formalism.L2.Ker.frobenius_poly_injective D u (D.chTw u μ) (O u μ) (i + 1) hi
  funext y'
  have h1 := congrFun h y'
  rw [ColumnChain.Kmap, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, sharp_evC D O u μ i hi v, hunf, hrho] at h1
  rw [evC_sec] at h1
  change (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) * GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
    ρ * ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y') at h1
  have hne : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne (i + 1) y' τ)
  have hinv : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) =
      (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun τ _ => zpow_neg _ _
  rw [hinv] at h1
  have h2 : GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
      ρ * frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y' := by
    have := inv_ne_zero hne
    apply mul_left_cancel₀ this
    rw [h1]; ring
  show GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = GL3Theta.evFr D _ ((O u μ).frm (i + 1) y')
  rw [h2]
  simp [frPoly, GL3Theta.evFr]

end GlobalTheory.Mem.KerForm

end
