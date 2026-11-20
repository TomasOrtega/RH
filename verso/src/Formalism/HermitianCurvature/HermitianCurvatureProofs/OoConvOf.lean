import Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleIntegrandMeasurable

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

/- English proof (translation)
Use `set H := Formalism.QuantumDeterminants.Hpk k r with hHdef`. Establish `hU : ∀ g ∈ Formalism.QuantumDeterminants.UH H, IsUnit g.det`. Introduce `g hg`. Establish `h1 : gᴴ * H * g = H` using `hg`. Establish `h2` using `congrArg Matrix.det h1`.

Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul]`. Establish `hH : IsUnit H.det` using `Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r`. Establish `h3 : (gᴴ).det * g.det = 1`. Apply `hH.mul_left_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Conclude with `IsUnit.of_mul_eq_one ((gᴴ).det) (by rw [mul_comm]; exact h3)`. Establish `hmem_mul : ∀ a ∈ Formalism.QuantumDeterminants.UH H, ∀ b ∈ Formalism.QuantumDeterminants.UH H, a * b ∈ Formalism.QuantumDeterminants.UH H`. Introduce `a ha b hb`. Establish `ha' : aᴴ * H * a = H` using `ha`. Establish `hb' : bᴴ * H * b = H` using `hb`.

Use `show (a * b)ᴴ * H * (a * b) = H`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmem_inv : ∀ a ∈ Formalism.QuantumDeterminants.UH H, a⁻¹ ∈ Formalism.QuantumDeterminants.UH H`. Introduce `a ha`.

Establish `hd` using `hU a ha`. Establish `ha' : aᴴ * H * a = H` using `ha`. Use `show (a⁻¹)ᴴ * H * a⁻¹ = H`. Combine the equalities or inequalities in the displayed calculation. Establish `hx : Q * γ⁻¹ * P⁻¹ ∈ Formalism.QuantumDeterminants.UH H` using `hmem_mul _ (hmem_mul _ hQ _ (hmem_inv _ hγ)) _ (hmem_inv _ hP)`.

Establish `hxinv : (Q * γ⁻¹ * P⁻¹)⁻¹ = P * γ * Q⁻¹`. Simplify using `only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hU _ hγ), Matrix.nonsing_inv_nonsing_inv _ (hU _ hP), mul_assoc]`. Rewrite using `[← ((hNI k r).2 _ hx).1, hxinv]`.
-/
theorem gN_Y_eq (hNI : NormInv) {P Q γ : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    B.gN (Q * γ⁻¹ * P⁻¹) = B.gN (P * γ * Q⁻¹) := by
  set H := Formalism.QuantumDeterminants.Hpk k r with hHdef
  have hU : ∀ g ∈ Formalism.QuantumDeterminants.UH H, IsUnit g.det := by
    intro g hg
    have h1 : gᴴ * H * g = H := hg
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH : IsUnit H.det := Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r
    have h3 : (gᴴ).det * g.det = 1 := by
      apply hH.mul_left_cancel
      calc H.det * ((gᴴ).det * g.det) = (gᴴ).det * H.det * g.det := by ring
        _ = H.det := h2
        _ = H.det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((gᴴ).det) (by rw [mul_comm]; exact h3)
  have hmem_mul : ∀ a ∈ Formalism.QuantumDeterminants.UH H, ∀ b ∈ Formalism.QuantumDeterminants.UH H, a * b ∈ Formalism.QuantumDeterminants.UH H := by
    intro a ha b hb
    have ha' : aᴴ * H * a = H := ha
    have hb' : bᴴ * H * b = H := hb
    show (a * b)ᴴ * H * (a * b) = H
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
      _ = H := by rw [ha', hb']
  have hmem_inv : ∀ a ∈ Formalism.QuantumDeterminants.UH H, a⁻¹ ∈ Formalism.QuantumDeterminants.UH H := by
    intro a ha
    have hd := hU a ha
    have ha' : aᴴ * H * a = H := ha
    show (a⁻¹)ᴴ * H * a⁻¹ = H
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hx : Q * γ⁻¹ * P⁻¹ ∈ Formalism.QuantumDeterminants.UH H :=
    hmem_mul _ (hmem_mul _ hQ _ (hmem_inv _ hγ)) _ (hmem_inv _ hP)
  have hxinv : (Q * γ⁻¹ * P⁻¹)⁻¹ = P * γ * Q⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hU _ hγ),
      Matrix.nonsing_inv_nonsing_inv _ (hU _ hP), mul_assoc]
  rw [← ((hNI k r).2 _ hx).1, hxinv]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe' γ hγ`. Establish `hS1'` using `hS1`. Take `⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩` from `hS1'`. Establish `hS2'` using `hS2`. Take `⟨-, -, -, -, -, -, hT', -, hπ', hW', -, -, hq'⟩` from `hS2'`.

Establish `: SigmaFinite D.μW` using `hW.1`. Establish `: SigmaFinite D.μN` using `hN.1`. Establish `: SigmaFinite D.μW'` using `hW'.1`. Establish `: SigmaFinite D.μG` using `hGm.1`. Establish `hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)`.

Rewrite using `[ae_iff]`. Simplify using `using hGm.2.2.1`. Establish `hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `hγ.1`. Take `⟨hγi, hγγ, hγγ'⟩` from `MatrixMultiplicationContinuity.uh_inv hγU`. Establish `hw0DD` using `cmHalfIntegralGenerator_mem_algebraicClosure hds w0`.

Establish `hP1` using `phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 l hbe w0 hw0DD`. Establish `hP2` using `phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 l' hbe' w0 hw0DD`. Establish `cont2' : ContinuousOn (fun g : Mx k r => l' (σ (γ⁻¹ * g) w0)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))` using `hP2.1.comp (continuous_const.matrix_mul continuous_id).continuousOn (fun g hg => DDSmoothness.uh_mul hγi hg)`. Establish `hop : ContinuousOn (fun g : Mx k r => (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))).smulRight (l (σ g w0))) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))`. Establish `ha : ContinuousOn (fun g : Mx k r => ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ (l' (σ (γ⁻¹ * g) w0)))) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))` using `(ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous.comp_continuousOn ((innerSL ℂ).continuous.comp_continuousOn cont2')`.

Conclude with `(ha.clm_apply hP1.1).congr fun g _ => rfl`. Establish `hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) D.μG`. Establish `hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}` using `hop.comp mt_cont.continuousOn (fun x hx => hx)`. Use `hc.aestronglyMeasurable (μ := D.μG) uh_mem_measurableSet` as an intermediate fact. Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) hGc]`. Then use the resulting hypothesis.

Use `⟨hmeas, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ x, ‖(innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))‖ₑ ∂D.μG < ⊤`. Simplify using `only [enorm_smulRight]`. Distinguish the cases in `hA : ∃ v ∈ DDsp σ w0, l v ≠ 0`. Use `swap`.

Use `push Not at hA`. Establish `e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0`. Rewrite using `[lintegral_congr_ae (g := fun _ => 0) ?_]`. Simplify using the standard rewrite rules. Use `filter_upwards [hGc] with x hx`.

Rewrite using `[hA _ (dd_stable hds hx w0 hw0DD)]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `ENNReal.zero_lt_top`. Distinguish the cases in `hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0`.

Use `swap`. Use `push Not at hA'`. Establish `e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0`. Rewrite using `[lintegral_congr_ae (g := fun _ => 0) ?_]`. Simplify using the standard rewrite rules.

Use `filter_upwards [hGc] with x hx`. Rewrite using `[hA' _ (dd_stable hds (DDSmoothness.uh_mul hγi hx) w0 hw0DD)]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `ENNReal.zero_lt_top`.

Take `⟨v, hv, hlv⟩` from `hA`. Take `⟨v', hv', hlv'⟩` from `hA'`. Take `⟨e1, he1, hee1⟩` from `coef_ext hds v w0`. Take `⟨e2, he2, hee2⟩` from `coef_ext hds v' w0`. Take `⟨C1, hC1⟩` from `hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv`.

Take `⟨C2, hC2⟩` from `hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD v' hv'`. Establish `hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h)` using `fun y hy => by rw [hee1 y hy]; exact hC1 y hy`. Establish `hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h)` using `fun y hy => by rw [hee2 y hy]; exact hC2 y hy`. Establish `h4` using `gap4 hG`. Establish `hAG` using `ag_nonneg k r`.

Establish `hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`. Establish `hb0 : 0 < aOf r h - AG k r - 1` using `by linarith`. Establish `hba : aOf r h - AG k r - 1 ≤ aOf r h` using `by linarith`. Establish `hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1` using `by ring`. Establish `hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0`.

Unfold `JF.TransportedAlt`. Establish `hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1)` using `by positivity`. Rewrite using `[Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤` using `(hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral`.

Establish `hLa` using `la_fin hNI D hThrb hb0.ne' hγ`. Establish `hpt : ∀ᵐ x ∂D.μG, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤ ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) * ((∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN)) * (∫⁻ q, ‖e2 (Matrix.of q.1 * Matr …` using `by filter_upwards [hGc] with x hx`. Establish `hgx : γ⁻¹ * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hγi hx`. Establish `b1` using `l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hx`. Establish `b2` using `l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hgx`.

Establish `i1 : ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) w0⟫_ℂ‖ₑ ∂(D.μW.prod D.μN) = ∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN)`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [prod_ae hW hN] with p hp`. Rewrite using `[hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hx)]`. Establish `i2 : ∫⁻ q, ‖⟪v', σ (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x)) w0⟫_ℂ‖ₑ ∂(D.μW'.prod D.μN) = ∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN)`.

Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [prod_ae hW' hN] with q hq`. Rewrite using `[hee2 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hq.1.1 hq.2.1) hgx)]`. Rewrite `b1` using `[i1]`. Rewrite `b2` using `[i2]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hinner : ∀ᵐ p ∂(D.μW.prod D.μN), ∀ᵐ q ∂(D.μW'.prod D.μN), ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ≤ (ENNReal.ofReal (|C1| * |C2|) * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) * ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1) …` using `by filter_upwards [prod_ae hW hN] with p hp filter_upwards [prod_ae hW' hN] with q hq`. Establish `hPU : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hp.1.1 hp.2.1`. Establish `hQU : Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)` using `DDSmoothness.uh_mul hq.1.1 hq.2.1`. Establish `hIB` using `inner_bound hNI D.haarG hGc he1 he2 hb1 hb2 hb0.le hba hPU hQU hγi`.

Establish `hY` using `gN_Y_eq hNI hPU hQU hγU`. Establish `e : Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ = Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹`. Rewrite using `[Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`. Unfold `Phi3`.

Rewrite `hIB` using `[hY, e]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmG` using `meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae (hpt.mono fun x hx => ?_)` and prove the remaining obligations.

Rewrite using `[← triple_lintegral_product he1 he2 γ⁻¹]`. Conclude with `hx`. Use `_ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) * ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by`. Rewrite using `[lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), triple_lintegral_swap he1 he2 γ⁻¹]`. Use `_ ≤ ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) * ∫⁻ p, ∫⁻ q, (ENNReal.ofReal (|C1| * |C2|) * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) * ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matri …`.

Conclude with `lintegral_mono_ae (hinner.mono fun p hp => lintegral_mono_ae hp)`. Use `_ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) * ((ENNReal.ofReal (|C1| * |C2|) * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) * ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * ( …`. Use `congr 1`. Establish `hc0 : ENNReal.ofReal (|C1| * |C2|) * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKg.ne`. Repeatedly rewrite using `[lintegral_const_mul' _ _ hc0]`.

Rewrite using `[show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable]`. Use `_ < ⊤ := by`. Use `ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) (ENNReal.mul_lt_top ?_ hLa)` and prove the remaining obligations. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKg`.
-/
theorem ooConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGG : GrowthG) (hDD : DecDD)
    (hBC : BeConv) : More.OOConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe' γ hγ
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have hS2' := hS2
  obtain ⟨-, -, -, -, -, -, hT', -, hπ', hW', -, -, hq'⟩ := hS2'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μW' := hW'.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hγ.1
  obtain ⟨hγi, hγγ, hγγ'⟩ := MatrixMultiplicationContinuity.uh_inv hγU
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hP1 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN
    D.μG νq hS1 l hbe w0 hw0DD
  have hP2 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN
    D.μG νq' hS2 l' hbe' w0 hw0DD
  have cont2' : ContinuousOn (fun g : Mx k r => l' (σ (γ⁻¹ * g) w0)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    hP2.1.comp (continuous_const.matrix_mul continuous_id).continuousOn (fun g hg => DDSmoothness.uh_mul hγi hg)
  have hop : ContinuousOn (fun g : Mx k r => (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))).smulRight (l (σ g w0)))
      (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have ha : ContinuousOn (fun g : Mx k r =>
        ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))))
        (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
      (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous.comp_continuousOn
        ((innerSL ℂ).continuous.comp_continuousOn cont2')
    exact (ha.clm_apply hP1.1).congr fun g _ => rfl
  have hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) D.μG := by
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r =>
        (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0)))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
      hop.comp mt_cont.continuousOn (fun x hx => hx)
    have := hc.aestronglyMeasurable (μ := D.μG) uh_mem_measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) hGc] at this
  refine ⟨hmeas, ?_⟩
  show ∫⁻ x, ‖(innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))‖ₑ ∂D.μG < ⊤
  simp only [enorm_smulRight]
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA _ (dd_stable hds hx w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  by_cases hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0
  swap
  · push Not at hA'
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA' _ (dd_stable hds (DDSmoothness.uh_mul hγi hx) w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨e2, he2, hee2⟩ := coef_ext hds v' w0
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD
    v' hv'
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee2 y hy]; exact hC2 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb0 : 0 < aOf r h - AG k r - 1 := by linarith
  have hba : aOf r h - AG k r - 1 ≤ aOf r h := by linarith
  have hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1 := by ring
  have hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
    linarith
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral
  have hLa := la_fin hNI D hThrb hb0.ne' hγ
  have hpt : ∀ᵐ x ∂D.μG, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤
      ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
        ((∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN)) *
          (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN))) := by
    filter_upwards [hGc] with x hx
    have hgx : γ⁻¹ * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hγi hx
    have b1 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hx
    have b2 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hgx
    have i1 : ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) w0⟫_ℂ‖ₑ ∂(D.μW.prod D.μN) =
        ∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW hN] with p hp
      rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hx)]
    have i2 : ∫⁻ q, ‖⟪v', σ (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x)) w0⟫_ℂ‖ₑ
        ∂(D.μW'.prod D.μN) =
        ∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW' hN] with q hq
      rw [hee2 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hq.1.1 hq.2.1) hgx)]
    rw [i1] at b1; rw [i2] at b2
    calc ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤ _ * _ := mul_le_mul' b2 b1
      _ = _ := by ring
  have hinner : ∀ᵐ p ∂(D.μW.prod D.μN), ∀ᵐ q ∂(D.μW'.prod D.μN),
      ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ≤
        (ENNReal.ofReal (|C1| * |C2|) *
          ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
        ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
          (-(aOf r h - AG k r - 1))‖ₑ := by
    filter_upwards [prod_ae hW hN] with p hp
    filter_upwards [prod_ae hW' hN] with q hq
    have hPU : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hQU : Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hq.1.1 hq.2.1
    have hIB := inner_bound hNI D.haarG hGc he1 he2 hb1 hb2 hb0.le hba hPU hQU hγi
    have hY := gN_Y_eq hNI hPU hQU hγU
    have e : Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ =
        Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹ := by
      rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    unfold Phi3
    rw [hY, e] at hIB
    calc _ ≤ _ := hIB
      _ = _ := by ring
  have hmG := meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)
  calc ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG
      ≤ ∫⁻ x, ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γ⁻¹ x p q ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) ∂D.μG := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        rw [← triple_lintegral_product he1 he2 γ⁻¹]; exact hx
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), triple_lintegral_swap he1 he2 γ⁻¹]
    _ ≤ ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, (ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
            ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        gcongr 1
        exact lintegral_mono_ae (hinner.mono fun p hp => lintegral_mono_ae hp)
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ((ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
          ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂D.μSS) := by
        congr 1
        have hc0 : ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKg.ne
        simp_rw [lintegral_const_mul' _ _ hc0]
        rw [show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) (ENNReal.mul_lt_top ?_ hLa)
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKg

end Formalism.FourierDecayAlt.P.S3dx4
