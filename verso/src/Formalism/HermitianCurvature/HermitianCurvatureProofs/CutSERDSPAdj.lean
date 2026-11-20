import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSCoordAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSIpInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CsliceContDiffAt

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Split

def paWt (n : ℕ) (c : Fin n → ℂ) : ℝ := ∏ j, (‖c j‖ ^ 2)⁻¹

def paTh {β : Type*} {n : ℕ} (l : Fin (n + 1)) (p : (Fin n → ℂ) × (ℂ × β)) : (Fin (n + 1) → ℂ) × β :=
  (Fin.insertNth l p.2.1 p.1, p.2.2)

/- English proof (translation)
Unfold `paWt`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j _`. Conclude with `inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc j)))`.
-/
theorem paWt_ne_zero {n : ℕ} {c : Fin n → ℂ} (hc : ∀ i, c i ≠ 0) : paWt n c ≠ 0 := by
  unfold paWt
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc j)))

/- English proof (translation)
Use `set ρ : (Fin (n + 1) → ℂ) → NNReal := fun c => (∏ j, (‖c j‖ ^ 2)⁻¹ : ℝ).toNNReal with hρdef`. Establish `hρ : Measurable ρ` using `Measurable.real_toNNReal (by fun_prop)`. Establish `hd : dxc (n + 1) = (volume : Measure (Fin (n + 1) → ℂ)).withDensity (fun c => (ρ c : ENNReal))` using `rfl`. Establish `hprod : (dxc (n + 1)).prod μ = ((volume : Measure (Fin (n + 1) → ℂ)).prod μ).withDensity (fun q => (ρ q.1 : ENNReal))`. Rewrite using `[hd, prod_withDensity_left hρ.coe_nnreal_ennreal]`.

Establish `hρ1 : Measurable (fun q : (Fin (n + 1) → ℂ) × β => ρ q.1)` using `hρ.comp measurable_fst`. Set `E : (Fin n → ℂ) × (ℂ × β) ≃ᵐ (Fin (n + 1) → ℂ) × β` to `MeasurableEquiv.prodAssoc.symm.trans ((MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) l).symm).prodCongr (MeasurableEquiv.refl β))`. Establish `hEv : ∀ p, E p = paTh l p`. Introduce and unpack `⟨c, t, x⟩`. Both sides reduce to the same expression.

Establish `hpi` using `(measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) l).symm`. Establish `hE : MeasurePreserving E ((volume : Measure (Fin n → ℂ)).prod ((volume : Measure ℂ).prod μ)) ((volume : Measure (Fin (n + 1) → ℂ)).prod μ)` using `((hpi.comp Measure.measurePreserving_swap).prod (MeasurePreserving.id μ)).comp (measurePreserving_prodAssoc _ _ _).symm`. Establish `hval : ∀ p : (Fin n → ℂ) × (ℂ × β), ρ (E p).1 • f (E p) = ((paWt n p.1 : ℝ) : ℂ) * (f (paTh l p) / ((‖p.2.1‖ ^ 2 : ℝ) : ℂ))`. Introduce `p`. Rewrite using `[hEv]`.

Establish `hw : ((ρ (paTh l p).1 : NNReal) : ℝ) = (‖p.2.1‖ ^ 2)⁻¹ * paWt n p.1`. Rewrite using `[hρdef]`. Simplify using `only`. Rewrite using `[Real.coe_toNNReal _ (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (sq_nonneg _)), Fin.prod_univ_succAbove _ l]`. Simplify using `[paTh, paWt, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]`.

Rewrite using `[NNReal.smul_def, hw, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfun : (fun p : (Fin n → ℂ) × (ℂ × β) => ((paWt n p.1 : ℝ) : ℂ) * (f (paTh l p) / ((‖p.2.1‖ ^ 2 : ℝ) : ℂ))) = (fun q : (Fin (n + 1) → ℂ) × β => ρ q.1 • f q) ∘ E`. Use function extensionality and compare the values at `p`.

Conclude with `(hval p).symm`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hprod, integrable_withDensity_iff_integrable_smul hρ1, hfun, hE.integrable_comp_emb E.measurableEmbedding]`. Rewrite using `[hprod, integral_withDensity_eq_integral_smul hρ1, hfun]`. Conclude with `(hE.integral_comp' (fun q : (Fin (n + 1) → ℂ) × β => ρ q.1 • f q)).symm`.
-/
theorem pa_split {β : Type*} [MeasurableSpace β] (μ : Measure β) [SFinite μ] {n : ℕ} (l : Fin (n + 1))
    (f : (Fin (n + 1) → ℂ) × β → ℂ) :
    (Integrable f ((dxc (n + 1)).prod μ) ↔ Integrable (fun p : (Fin n → ℂ) × (ℂ × β) =>
      ((paWt n p.1 : ℝ) : ℂ) * (f (paTh l p) / ((‖p.2.1‖ ^ 2 : ℝ) : ℂ))) (volume.prod (volume.prod μ))) ∧
    ∫ q, f q ∂((dxc (n + 1)).prod μ) = ∫ p : (Fin n → ℂ) × (ℂ × β),
      ((paWt n p.1 : ℝ) : ℂ) * (f (paTh l p) / ((‖p.2.1‖ ^ 2 : ℝ) : ℂ)) ∂(volume.prod (volume.prod μ)) := by
  set ρ : (Fin (n + 1) → ℂ) → NNReal := fun c => (∏ j, (‖c j‖ ^ 2)⁻¹ : ℝ).toNNReal with hρdef
  have hρ : Measurable ρ := Measurable.real_toNNReal (by fun_prop)
  have hd : dxc (n + 1) = (volume : Measure (Fin (n + 1) → ℂ)).withDensity (fun c => (ρ c : ENNReal)) := rfl
  have hprod : (dxc (n + 1)).prod μ =
      ((volume : Measure (Fin (n + 1) → ℂ)).prod μ).withDensity (fun q => (ρ q.1 : ENNReal)) := by
    rw [hd, prod_withDensity_left hρ.coe_nnreal_ennreal]
  have hρ1 : Measurable (fun q : (Fin (n + 1) → ℂ) × β => ρ q.1) := hρ.comp measurable_fst
  let E : (Fin n → ℂ) × (ℂ × β) ≃ᵐ (Fin (n + 1) → ℂ) × β :=
    MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) l).symm).prodCongr
        (MeasurableEquiv.refl β))
  have hEv : ∀ p, E p = paTh l p := by
    rintro ⟨c, t, x⟩
    rfl
  have hpi := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) l).symm
  have hE : MeasurePreserving E ((volume : Measure (Fin n → ℂ)).prod ((volume : Measure ℂ).prod μ))
      ((volume : Measure (Fin (n + 1) → ℂ)).prod μ) :=
    ((hpi.comp Measure.measurePreserving_swap).prod (MeasurePreserving.id μ)).comp
      (measurePreserving_prodAssoc _ _ _).symm
  have hval : ∀ p : (Fin n → ℂ) × (ℂ × β), ρ (E p).1 • f (E p) =
      ((paWt n p.1 : ℝ) : ℂ) * (f (paTh l p) / ((‖p.2.1‖ ^ 2 : ℝ) : ℂ)) := by
    intro p
    rw [hEv]
    have hw : ((ρ (paTh l p).1 : NNReal) : ℝ) = (‖p.2.1‖ ^ 2)⁻¹ * paWt n p.1 := by
      rw [hρdef]
      simp only
      rw [Real.coe_toNNReal _ (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (sq_nonneg _)),
        Fin.prod_univ_succAbove _ l]
      simp [paTh, paWt, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [NNReal.smul_def, hw, Complex.real_smul]
    push_cast
    ring
  have hfun : (fun p : (Fin n → ℂ) × (ℂ × β) =>
      ((paWt n p.1 : ℝ) : ℂ) * (f (paTh l p) / ((‖p.2.1‖ ^ 2 : ℝ) : ℂ))) =
      (fun q : (Fin (n + 1) → ℂ) × β => ρ q.1 • f q) ∘ E := by
    funext p; exact (hval p).symm
  constructor
  · rw [hprod, integrable_withDensity_iff_integrable_smul hρ1, hfun,
      hE.integrable_comp_emb E.measurableEmbedding]
  · rw [hprod, integral_withDensity_eq_integral_smul hρ1, hfun]
    exact (hE.integral_comp' (fun q : (Fin (n + 1) → ℂ) × β => ρ q.1 • f q)).symm

end Split

section Core

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def paHs (U V : RadSp k r z z' π π') (q : (Fin r → ℂ) × Mt k r) : ℂ :=
  B.hsInner ((U : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2)) ((V : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ipF_eq_paHs (U V : RadSp k r z z' π π') : ipF U V = paHs V U := rfl

/- English proof (translation)
Rewrite using `[ipF_eq_paHs]`. Unfold `paHs`. Rewrite using `[Formalism.FourierDecayAlt.P5.HerA.hsInner_swap]`.
-/
theorem paHs_conj (U V : RadSp k r z z' π π') (q : (Fin r → ℂ) × Mt k r) :
    paHs U V q = conj (ipF U V q) := by
  rw [ipF_eq_paHs]; unfold paHs; rw [Formalism.FourierDecayAlt.P5.HerA.hsInner_swap]

/- English proof (translation)
Consider the cases of `r with`. Consider the case `zero => exact l.elim0`. Consider the case `succ n`. Establish `I0` using `(pa_split μ l (paHs Φ Ψ)).1.mp i0`. Establish `I1` using `(pa_split μ l (paHs (X.op l 0 Φ) Ψ)).1.mp i1`.

Establish `I2` using `(pa_split μ l (paHs Φ (X.op l 3 Ψ))).1.mp i2`. Rewrite using `[(pa_split μ l _).2, (pa_split μ l _).2, integral_prod _ I1, integral_prod _ I2, ← integral_neg]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [I0.prod_right_ae, I1.prod_right_ae, I2.prod_right_ae] with c h0 h1 h2`. Simplify using `only [integral_const_mul]`.

Rewrite using `[← mul_neg]`. Use `congr 1`. Distinguish the cases in `hc : ∀ j, c j ≠ 0`. Use `set c0 : Fin (n + 1) → ℂ := Fin.insertNth l 1 c with hc0def`. Establish `hc0 : c0 ∈ OmX (n + 1)`.

Introduce `j`. Use `Fin.succAboveCases l ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `[c0]`. Simplify using `[c0, Fin.insertNth_apply_succAbove, hc i]`. Establish `key : ∀ U V : RadSp k (n + 1) z z' π π', (fun q : ℂ × Mt k (n + 1) => paHs U V (paTh l (c, q)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) = fun q => B.hsInner ((U : Fn k (n + 1) (Wq →L[ℂ] Wp)) (Function.update c0 l q.1) (Matrix.of q.2)) ((V : Fn k (n + 1) (Wq →L[ℂ] Wp)) (Function.update c0 l q.1) …`.

Introduce `U V`. Use function extensionality and compare the values at `q`. Simplify using `[paHs, paTh, c0, Fin.update_insertNth]`. Establish `hw : IsUnit ((paWt n c : ℝ) : ℂ)` using `isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (paWt_ne_zero hc))`. Establish `g0` using `(integrable_const_mul_iff hw _).mp h0`.

Establish `g1` using `(integrable_const_mul_iff hw _).mp h1`. Establish `g2` using `(integrable_const_mul_iff hw _).mp h2`. Rewrite `g0`, `g1`, `g2` using `[key]`. Establish `hs` using `Formalism.FourierDecayAlt.P5.HerB.site_p_adj X μ Φ Ψ l c0 hc0 g0 g1 g2`. Unfold `pairAt at hs`.

Simplify using `only [← integral_div] at hs`. Rewrite using `[key, key, integral_prod _ g1, integral_prod _ g2]`. Conclude with `hs`. Use `push Not at hc`. Take `⟨j, hj⟩` from `hc`.

Establish `hz : ∀ U V : RadSp k (n + 1) z z' π π', (fun q : ℂ × Mt k (n + 1) => paHs U V (paTh l (c, q)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) = fun _ => 0`. Introduce `U V`. Use function extensionality and compare the values at `q`. Establish `hn : ((paTh l (c, q)).1, Matrix.of (paTh l (c, q)).2) ∉ DomR k (n + 1) z z'`. Introduce `h`.

Apply `h.1 (l.succAbove j)` to reduce the goal to its premises. Simplify using `[paTh, Fin.insertNth_apply_succAbove, hj]`. Simplify using `only [paHs]`. Rewrite using `[radSp_zero_off U hn, Formalism.FourierDecayAlt.P5.HerA.hsInner_zero_left, zero_div]`. Rewrite using `[hz, hz, integral_zero, neg_zero]`.
-/
theorem pa_core (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (Φ Ψ : RadSp k r z z' π π')
    (l : Fin r) (i0 : Integrable (paHs Φ Ψ) ((dxc r).prod μ)) (i1 : Integrable (paHs (X.op l 0 Φ) Ψ) ((dxc r).prod μ))
    (i2 : Integrable (paHs Φ (X.op l 3 Ψ)) ((dxc r).prod μ)) :
    ∫ q, paHs (X.op l 0 Φ) Ψ q ∂((dxc r).prod μ) = -∫ q, paHs Φ (X.op l 3 Ψ) q ∂((dxc r).prod μ) := by
  cases r with
  | zero => exact l.elim0
  | succ n =>
    have I0 := (pa_split μ l (paHs Φ Ψ)).1.mp i0
    have I1 := (pa_split μ l (paHs (X.op l 0 Φ) Ψ)).1.mp i1
    have I2 := (pa_split μ l (paHs Φ (X.op l 3 Ψ))).1.mp i2
    rw [(pa_split μ l _).2, (pa_split μ l _).2, integral_prod _ I1, integral_prod _ I2, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [I0.prod_right_ae, I1.prod_right_ae, I2.prod_right_ae] with c h0 h1 h2
    simp only [integral_const_mul]
    rw [← mul_neg]
    congr 1
    by_cases hc : ∀ j, c j ≠ 0
    · set c0 : Fin (n + 1) → ℂ := Fin.insertNth l 1 c with hc0def
      have hc0 : c0 ∈ OmX (n + 1) := by
        intro j
        refine Fin.succAboveCases l ?_ (fun i => ?_) j
        · simp [c0]
        · simp [c0, Fin.insertNth_apply_succAbove, hc i]
      have key : ∀ U V : RadSp k (n + 1) z z' π π', (fun q : ℂ × Mt k (n + 1) =>
          paHs U V (paTh l (c, q)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) = fun q =>
          B.hsInner ((U : Fn k (n + 1) (Wq →L[ℂ] Wp)) (Function.update c0 l q.1) (Matrix.of q.2))
            ((V : Fn k (n + 1) (Wq →L[ℂ] Wp)) (Function.update c0 l q.1) (Matrix.of q.2)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ) := by
        intro U V; funext q
        simp [paHs, paTh, c0, Fin.update_insertNth]
      have hw : IsUnit ((paWt n c : ℝ) : ℂ) := isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (paWt_ne_zero hc))
      have g0 := (integrable_const_mul_iff hw _).mp h0
      have g1 := (integrable_const_mul_iff hw _).mp h1
      have g2 := (integrable_const_mul_iff hw _).mp h2
      rw [key] at g0 g1 g2
      have hs := Formalism.FourierDecayAlt.P5.HerB.site_p_adj X μ Φ Ψ l c0 hc0 g0 g1 g2
      unfold pairAt at hs
      simp only [← integral_div] at hs
      rw [key, key, integral_prod _ g1, integral_prod _ g2]
      exact hs
    · push Not at hc
      obtain ⟨j, hj⟩ := hc
      have hz : ∀ U V : RadSp k (n + 1) z z' π π', (fun q : ℂ × Mt k (n + 1) =>
          paHs U V (paTh l (c, q)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) = fun _ => 0 := by
        intro U V; funext q
        have hn : ((paTh l (c, q)).1, Matrix.of (paTh l (c, q)).2) ∉ DomR k (n + 1) z z' := by
          intro h
          apply h.1 (l.succAbove j)
          simp [paTh, Fin.insertNth_apply_succAbove, hj]
        simp only [paHs]
        rw [radSp_zero_off U hn, Formalism.FourierDecayAlt.P5.HerA.hsInner_zero_left, zero_div]
      rw [hz, hz, integral_zero, neg_zero]

end Core

section Adj

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Take `⟨K, hK, hKD, h0⟩` from `h`. Use `⟨K, hK, hKD, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hopen : IsOpen {c : Fin r → ℂ | (c, x.2) ∉ K}` using `hK.isClosed.isOpen_compl.preimage (continuous_id.prodMk continuous_const)`. Establish `hev : (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' x.2) =ᶠ[𝓝 x.1] fun _ => 0` using `by filter_upwards [hopen.mem_nhds (show (x.1, x.2) ∉ K from hx)] with c' hc'`. Conclude with `h0 (c', x.2) hc'`.

Establish `hfd : fderiv ℝ (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' x.2) x.1 = 0`. Rewrite using `[hev.fderiv_eq]`. Conclude with `fderiv_const_apply _`. Establish `hf0 : (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0` using `h0 x hx`. Rewrite using `[X.op_apply]`.

Use `show opL l i (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' x.2) x.1 = 0`. Apply the tactic sequence `fin_cases i <;> simp [opL, pOp, pbOp, cOp, ciOp, cbOp, cbiOp, Formalism.QuantumDeterminants.wirt, Formalism.QuantumDeterminants.wirtBar, hfd, hf0]`.
-/
theorem rTest_op (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) {Ψ : RadSp k r z z' π π'} (h : RTest Ψ) :
    RTest (X.op l i Ψ) := by
  obtain ⟨K, hK, hKD, h0⟩ := h
  refine ⟨K, hK, hKD, fun x hx => ?_⟩
  have hopen : IsOpen {c : Fin r → ℂ | (c, x.2) ∉ K} :=
    hK.isClosed.isOpen_compl.preimage (continuous_id.prodMk continuous_const)
  have hev : (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' x.2) =ᶠ[𝓝 x.1] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds (show (x.1, x.2) ∉ K from hx)] with c' hc'
    exact h0 (c', x.2) hc'
  have hfd : fderiv ℝ (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' x.2) x.1 = 0 := by
    rw [hev.fderiv_eq]; exact fderiv_const_apply _
  have hf0 : (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := h0 x hx
  rw [X.op_apply]
  show opL l i (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' x.2) x.1 = 0
  fin_cases i <;> simp [opL, pOp, pbOp, cOp, ciOp, cbOp, cbiOp, Formalism.QuantumDeterminants.wirt, Formalism.QuantumDeterminants.wirtBar, hfd, hf0]

/- English proof (translation)
Simplify using `using rTest_smul (-1 : ℂ) h`.
-/
theorem rTest_neg {Ψ : RadSp k r z z' π π'} (h : RTest Ψ) : RTest (-Ψ) := by
  simpa using rTest_smul (-1 : ℂ) h

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `only [ipF, Submodule.coe_neg, Pi.neg_apply]`. Rewrite using `[show -(U : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2) = (-1 : ℂ) • (U : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2) by simp, rds_hsVec_smul, inner_smul_left]`. Simplify using the standard rewrite rules.
-/
theorem ipF_neg_left (U V : RadSp k r z z' π π') : ipF (-U) V = -ipF U V := by
  funext q
  simp only [ipF, Submodule.coe_neg, Pi.neg_apply]
  rw [show -(U : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2) = (-1 : ℂ) • (U : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2)
    by simp, rds_hsVec_smul, inner_smul_left]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `only [ipF, Submodule.coe_neg, Pi.neg_apply]`. Rewrite using `[show -(V : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2) = (-1 : ℂ) • (V : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2) by simp, rds_hsVec_smul, inner_smul_right]`. Simplify using the standard rewrite rules.
-/
theorem ipF_neg_right (U V : RadSp k r z z' π π') : ipF U (-V) = -ipF U V := by
  funext q
  simp only [ipF, Submodule.coe_neg, Pi.neg_apply]
  rw [show -(V : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2) = (-1 : ℂ) • (V : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2)
    by simp, rds_hsVec_smul, inner_smul_right]
  simp

/- English proof (translation)
Establish `h` using `(ipF_integrable hμ U V hV)`. Establish `e : paHs U V = fun q => (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) (ipF U V q)`. Use function extensionality and compare the values at `q`. Rewrite using `[paHs_conj]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(LinearIsometryEquiv.integrable_comp_iff _).mpr h`.
-/
theorem paHs_integrable {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (U V : RadSp k r z z' π π') (hV : RTest V) : Integrable (paHs U V) ((dxc r).prod μ) := by
  have h := (ipF_integrable hμ U V hV)
  have e : paHs U V = fun q => (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) (ipF U V q) := by
    funext q; rw [paHs_conj]; rfl
  rw [e]
  exact (LinearIsometryEquiv.integrable_comp_iff _).mpr h

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ` as an intermediate fact. Establish `hΨ3` using `rTest_op X l 3 hΨ`. Rewrite using `[radIp_eq_prod hμ _ _ hΨ, radIp_eq_prod hμ _ _ hΨ3]`. Establish `hc` using `pa_core X μ Φ Ψ l (paHs_integrable hμ _ _ hΨ) (paHs_integrable hμ _ _ hΨ) (paHs_integrable hμ _ _ hΨ3)`. Simplify using `only [paHs_conj, integral_conj] at hc`.

Establish `hc'` using `congrArg conj hc`. Simplify using `only [Complex.conj_conj, map_neg] at hc'`. Conclude with `hc'`.
-/
theorem pa_left (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (l : Fin r) (Φ Ψ : RadSp k r z z' π π') (hΨ : RTest Ψ) :
    radIp μ (X.op l 0 Φ) Ψ = -radIp μ Φ (X.op l 3 Ψ) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ
  have hΨ3 := rTest_op X l 3 hΨ
  rw [radIp_eq_prod hμ _ _ hΨ, radIp_eq_prod hμ _ _ hΨ3]
  have hc := pa_core X μ Φ Ψ l (paHs_integrable hμ _ _ hΨ) (paHs_integrable hμ _ _ hΨ)
    (paHs_integrable hμ _ _ hΨ3)
  simp only [paHs_conj, integral_conj] at hc
  have hc' := congrArg conj hc
  simp only [Complex.conj_conj, map_neg] at hc'
  exact hc'

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ` as an intermediate fact. Establish `hΨ0` using `rTest_op X l 0 hΨ`. Rewrite using `[radIp_eq_prod hμ _ _ hΨ0, radIp_eq_prod hμ _ _ hΨ]`. Simplify using `only [ipF_eq_paHs]`. Conclude with `pa_core X μ Ψ Φ l (ipF_integrable hμ Φ Ψ hΨ) (ipF_integrable hμ Φ _ hΨ0) (ipF_integrable hμ _ Ψ hΨ)`.
-/
theorem pa_right (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (l : Fin r) (Φ Ψ : RadSp k r z z' π π') (hΨ : RTest Ψ) :
    radIp μ Φ (X.op l 0 Ψ) = -radIp μ (X.op l 3 Φ) Ψ := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ
  have hΨ0 := rTest_op X l 0 hΨ
  rw [radIp_eq_prod hμ _ _ hΨ0, radIp_eq_prod hμ _ _ hΨ]
  simp only [ipF_eq_paHs]
  exact pa_core X μ Ψ Φ l (ipF_integrable hμ Φ Ψ hΨ) (ipF_integrable hμ Φ _ hΨ0) (ipF_integrable hμ _ Ψ hΨ)

/- English proof (translation)
Rewrite using `[radIp_eq_prod hμ _ _ hV, radIp_eq_prod hμ _ _ hV, ipF_neg_left, ← integral_neg]`. Both sides reduce to the same expression.
-/
theorem radIp_neg_left {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (U V : RadSp k r z z' π π') (hV : RTest V) : radIp μ (-U) V = -radIp μ U V := by
  rw [radIp_eq_prod hμ _ _ hV, radIp_eq_prod hμ _ _ hV, ipF_neg_left, ← integral_neg]
  rfl

/- English proof (translation)
Rewrite using `[radIp_eq_prod hμ _ _ (rTest_neg hV), radIp_eq_prod hμ _ _ hV, ipF_neg_right, ← integral_neg]`. Both sides reduce to the same expression.
-/
theorem radIp_neg_right {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (U V : RadSp k r z z' π π') (hV : RTest V) : radIp μ U (-V) = -radIp μ U V := by
  rw [radIp_eq_prod hμ _ _ (rTest_neg hV), radIp_eq_prod hμ _ _ hV, ipF_neg_right, ← integral_neg]
  rfl

/- English proof (translation)
Use `⟨fun Ψ h => rTest_op X l 0 h, fun Ψ h => ?_, fun Φ Ψ h => ?_, fun Φ Ψ h => ?_⟩` and prove the remaining obligations. Use `show RTest ((-X.op l 3) Ψ)`. Rewrite using `[LinearMap.neg_apply]`. Conclude with `rTest_neg (rTest_op X l 3 h)`. Use `show radIp μ (X.op l 0 Φ) Ψ = radIp μ Φ ((-X.op l 3) Ψ)`.

Rewrite using `[LinearMap.neg_apply, radIp_neg_right hμ _ _ (rTest_op X l 3 h)]`. Conclude with `pa_left X hμ l Φ Ψ h`. Use `show radIp μ ((-X.op l 3) Φ) Ψ = radIp μ Φ (X.op l 0 Ψ)`. Rewrite using `[LinearMap.neg_apply, radIp_neg_left hμ _ _ h, pa_right X hμ l Φ Ψ h]`.
-/
theorem rAdj_p (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (l : Fin r) : RAdj μ (mkP (X.op l 0) (-X.op l 3)) := by
  refine ⟨fun Ψ h => rTest_op X l 0 h, fun Ψ h => ?_, fun Φ Ψ h => ?_, fun Φ Ψ h => ?_⟩
  · show RTest ((-X.op l 3) Ψ)
    rw [LinearMap.neg_apply]; exact rTest_neg (rTest_op X l 3 h)
  · show radIp μ (X.op l 0 Φ) Ψ = radIp μ Φ ((-X.op l 3) Ψ)
    rw [LinearMap.neg_apply, radIp_neg_right hμ _ _ (rTest_op X l 3 h)]
    exact pa_left X hμ l Φ Ψ h
  · show radIp μ ((-X.op l 3) Φ) Ψ = radIp μ Φ (X.op l 0 Ψ)
    rw [LinearMap.neg_apply, radIp_neg_left hμ _ _ h, pa_right X hμ l Φ Ψ h]

/- English proof (translation)
Use `⟨fun Ψ h => rTest_op X l 3 h, fun Ψ h => ?_, fun Φ Ψ h => ?_, fun Φ Ψ h => ?_⟩` and prove the remaining obligations. Use `show RTest ((-X.op l 0) Ψ)`. Rewrite using `[LinearMap.neg_apply]`. Conclude with `rTest_neg (rTest_op X l 0 h)`. Use `show radIp μ (X.op l 3 Φ) Ψ = radIp μ Φ ((-X.op l 0) Ψ)`.

Rewrite using `[LinearMap.neg_apply, radIp_neg_right hμ _ _ (rTest_op X l 0 h), pa_right X hμ l Φ Ψ h, neg_neg]`. Use `show radIp μ ((-X.op l 0) Φ) Ψ = radIp μ Φ (X.op l 3 Ψ)`. Rewrite using `[LinearMap.neg_apply, radIp_neg_left hμ _ _ h, pa_left X hμ l Φ Ψ h, neg_neg]`.
-/
theorem rAdj_pb (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (l : Fin r) : RAdj μ (mkP (X.op l 3) (-X.op l 0)) := by
  refine ⟨fun Ψ h => rTest_op X l 3 h, fun Ψ h => ?_, fun Φ Ψ h => ?_, fun Φ Ψ h => ?_⟩
  · show RTest ((-X.op l 0) Ψ)
    rw [LinearMap.neg_apply]; exact rTest_neg (rTest_op X l 0 h)
  · show radIp μ (X.op l 3 Φ) Ψ = radIp μ Φ ((-X.op l 0) Ψ)
    rw [LinearMap.neg_apply, radIp_neg_right hμ _ _ (rTest_op X l 0 h), pa_right X hμ l Φ Ψ h, neg_neg]
  · show radIp μ ((-X.op l 0) Φ) Ψ = radIp μ Φ (X.op l 3 Ψ)
    rw [LinearMap.neg_apply, radIp_neg_left hμ _ _ h, pa_left X hμ l Φ Ψ h, neg_neg]

end Adj

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ l`. Take `⟨hp, hpb, -⟩` from `hD.2.2.1`. Rewrite using `[hp l, hpb l]`. Conclude with `⟨rAdj_p X hD.2.1 l, rAdj_pb X hD.2.1 l⟩`.
-/
theorem spectral_pairing_adjoint : RDSPAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ l
  obtain ⟨hp, hpb, -⟩ := hD.2.2.1
  rw [hp l, hpb l]
  exact ⟨rAdj_p X hD.2.1 l, rAdj_pb X hD.2.1 l⟩

end Formalism.FourierDecayAlt.P.CutSE
