import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SD

/- English proof (translation)
Establish `hγ : ∀ a b, γ 0 a b = g a b` using `fun a b => by rw [h0]`. Establish `key : ∀ a b, HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j) (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) 0`. Introduce `a b`. Establish `h1 : HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j) (star (γ' a i) * H a b * γ 0 b j + star (γ 0 a i) * H a b * γ' b j) 0` using `(((h a i).star).mul_const (H a b)).mul (h b j)`. Rewrite `h1` using `[hγ a i, hγ b j]`.

Conclude with `h1`. Establish `hs` using `HasDerivAt.sum (u := Finset.univ) fun b _ => HasDerivAt.sum (u := Finset.univ) fun a _ => key a b`. Simplify using `only [Finset.sum_fn] at hs`. Establish `e1 : (fun t => ((γ t)ᴴ * H * γ t) i j) = fun t => ∑ b, ∑ a, star (γ t a i) * H a b * γ t b j`. Use function extensionality and compare the values at `t`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]`. Establish `e2 : (γ'ᴴ * H * g + gᴴ * H * γ') i j = ∑ b, ∑ a, (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j)`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.sum_add_distrib]`. Rewrite using `[e1, e2]`. Conclude with `hs`.
-/
theorem hasDeriv_form {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {γ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {g γ' : Matrix (Fin n) (Fin n) ℂ} (h0 : γ 0 = g) (h : ∀ a b, HasDerivAt (fun t => γ t a b) (γ' a b) 0)
    (i j : Fin n) :
    HasDerivAt (fun t => ((γ t)ᴴ * H * γ t) i j) ((γ'ᴴ * H * g + gᴴ * H * γ') i j) 0 := by
  have hγ : ∀ a b, γ 0 a b = g a b := fun a b => by rw [h0]
  have key : ∀ a b, HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
      (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) 0 := by
    intro a b
    have h1 : HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
        (star (γ' a i) * H a b * γ 0 b j + star (γ 0 a i) * H a b * γ' b j) 0 :=
      (((h a i).star).mul_const (H a b)).mul (h b j)
    rw [hγ a i, hγ b j] at h1
    exact h1
  have hs := HasDerivAt.sum (u := Finset.univ) fun b _ =>
    HasDerivAt.sum (u := Finset.univ) fun a _ => key a b
  simp only [Finset.sum_fn] at hs
  have e1 : (fun t => ((γ t)ᴴ * H * γ t) i j) =
      fun t => ∑ b, ∑ a, star (γ t a i) * H a b * γ t b j := by
    funext t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have e2 : (γ'ᴴ * H * g + gᴴ * H * γ') i j =
      ∑ b, ∑ a, (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      Finset.sum_add_distrib]
  rw [e1, e2]
  exact hs

variable {k r : ℕ}

/- English proof (translation)
Establish `hℓ : HasDerivAt (fun t : ℝ => ζ + t • v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ζ`. Establish `hγ : HasDerivAt (fun t : ℝ => μ (ζ + t • v)) (D v) 0`. Establish `hD' : HasFDerivAt μ D (ζ + (0 : ℝ) • v)` using `by simpa using hD`. Conclude with `hD'.comp_hasDerivAt (0 : ℝ) hℓ`.

Establish `hent : ∀ a b, HasDerivAt (fun t : ℝ => μ (ζ + t • v) a b) (D v a b) 0`. Introduce `a b`. Conclude with `hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ a) b`. Establish `hev : ∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) ∈ Q.Glev k r (Fin.last r)`. Establish `ht : Tendsto (fun t : ℝ => ζ + t • v) (𝓝 0) (𝓝 ζ)`.

Simplify using `using hℓ.continuousAt.tendsto`. Conclude with `ht.eventually hG`. Establish `hU : (μ ζ)ᴴ * Hpk k r * μ ζ = Hpk k r` using `hG.self_of_nhds.1`. Establish `hder : (D v)ᴴ * Hpk k r * μ ζ + (μ ζ)ᴴ * Hpk k r * D v = 0`. Use extensionality with `i j`.

Establish `h1` using `hasDeriv_form (Hpk k r) (γ := fun t : ℝ => μ (ζ + t • v)) (g := μ ζ) (γ' := D v) (by simp) hent i j`. Establish `h2 : HasDerivAt (fun t : ℝ => ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j) 0 0` using `(hasDerivAt_const (0 : ℝ) (Hpk k r i j)).congr_of_eventuallyEq (hev.mono fun t ht => by show ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j = Hpk k r i j`. Rewrite using `[show (μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v) = Hpk k r from ht.1])`. Conclude with `h1.unique h2`. Establish `hH : (Hpk k r).det ≠ 0`.

Establish `h1` using `congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_one]`. Introduce `h0`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1`.

Establish `hdet : IsUnit (μ ζ).det`. Establish `h2` using `congrArg Matrix.det hU`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul]`. Use `isUnit_iff_ne_zero.2 fun h0 => hH ?_` and prove the remaining obligations. Rewrite `h2` using `[h0, mul_zero]`.

Conclude with `h2.symm`. Establish `hgi : μ ζ * (μ ζ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Establish `e1 : ((μ ζ)⁻¹)ᴴ * Hpk k r = Hpk k r * μ ζ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r * μ ζ := by rw [hgi, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `e2 : Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Establish `hvec : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) *ᵥ w = w) → D v *ᵥ w = 0`.

Introduce `w hw`. Use function extensionality and compare the values at `q`. Establish `hd : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) ((D v *ᵥ w) q) 0`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `first`.

Consider the case `exact HasDerivAt.sum fun p _ => (hent q p).mul_const (w p)`. Consider the case `exact HasDerivAt.fun_sum fun p _ => (hent q p).mul_const (w p)`. Establish `hc : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) 0 0` using `(hasDerivAt_const (0 : ℝ) (w q)).congr_of_eventuallyEq (hw.mono fun t ht => by show (μ (ζ + t • v) *ᵥ w) q = w q`. Rewrite using `[ht])`. Conclude with `hd.unique hc`.

Unfold `Q.inLieLev`. Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2, ← Matrix.mul_assoc]`. Conclude with `hder`. Rewrite using `[← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).1), Matrix.mulVec_zero]`.

Rewrite using `[← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).2), Matrix.mulVec_zero]`.
-/
theorem lie_of_curve {μ : ℂ → Q.Mx k r} {ζ : ℂ} {D : ℂ →L[ℝ] Q.Mx k r} (hD : HasFDerivAt μ D ζ)
    (hG : ∀ᶠ w in 𝓝 ζ, μ w ∈ Q.Glev k r (Fin.last r)) (v : ℂ) :
    Q.inLieLev k r (Fin.last r) ((μ ζ)⁻¹ * D v) := by
  have hℓ : HasDerivAt (fun t : ℝ => ζ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ζ
  have hγ : HasDerivAt (fun t : ℝ => μ (ζ + t • v)) (D v) 0 := by
    have hD' : HasFDerivAt μ D (ζ + (0 : ℝ) • v) := by simpa using hD
    exact hD'.comp_hasDerivAt (0 : ℝ) hℓ
  have hent : ∀ a b, HasDerivAt (fun t : ℝ => μ (ζ + t • v) a b) (D v a b) 0 := by
    intro a b
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ a) b
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) ∈ Q.Glev k r (Fin.last r) := by
    have ht : Tendsto (fun t : ℝ => ζ + t • v) (𝓝 0) (𝓝 ζ) := by
      simpa using hℓ.continuousAt.tendsto
    exact ht.eventually hG
  have hU : (μ ζ)ᴴ * Hpk k r * μ ζ = Hpk k r := hG.self_of_nhds.1
  have hder : (D v)ᴴ * Hpk k r * μ ζ + (μ ζ)ᴴ * Hpk k r * D v = 0 := by
    ext i j
    have h1 := hasDeriv_form (Hpk k r) (γ := fun t : ℝ => μ (ζ + t • v)) (g := μ ζ) (γ' := D v)
      (by simp) hent i j
    have h2 : HasDerivAt (fun t : ℝ => ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (Hpk k r i j)).congr_of_eventuallyEq (hev.mono fun t ht => by
        show ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j = Hpk k r i j
        rw [show (μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v) = Hpk k r from ht.1])
    exact h1.unique h2
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hdet : IsUnit (μ ζ).det := by
    have h2 := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
    rw [h0, mul_zero] at h2
    exact h2.symm
  have hgi : μ ζ * (μ ζ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e1 : ((μ ζ)⁻¹)ᴴ * Hpk k r = Hpk k r * μ ζ := by
    calc ((μ ζ)⁻¹)ᴴ * Hpk k r = ((μ ζ)⁻¹)ᴴ * ((μ ζ)ᴴ * Hpk k r * μ ζ) := by rw [hU]
      _ = (μ ζ * (μ ζ)⁻¹)ᴴ * Hpk k r * μ ζ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * μ ζ := by rw [hgi, Matrix.conjTranspose_one, Matrix.one_mul]
  have e2 : Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r := by
    calc Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r * μ ζ * (μ ζ)⁻¹ := by rw [hU]
      _ = (μ ζ)ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have hvec : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) *ᵥ w = w) →
      D v *ᵥ w = 0 := by
    intro w hw
    funext q
    have hd : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) ((D v *ᵥ w) q) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      first
      | exact HasDerivAt.sum fun p _ => (hent q p).mul_const (w p)
      | exact HasDerivAt.fun_sum fun p _ => (hent q p).mul_const (w p)
    have hc : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (w q)).congr_of_eventuallyEq (hw.mono fun t ht => by
        show (μ (ζ + t • v) *ᵥ w) q = w q
        rw [ht])
    exact hd.unique hc
  unfold Q.inLieLev
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2,
      ← Matrix.mul_assoc]
    exact hder
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).1), Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).2), Matrix.mulVec_zero]

end SD

/- English proof (translation)
Introduce `k r z z' hk hz hz' hT hT' ζ hζ`. Establish `hsec` using `TheSec.theSection_isSection k r z z' hk hz hz' hT hT'`. Establish `hA : IsOpen {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w}` using `isOpen_lt continuous_const Complex.continuous_normSq`. Establish `hcd : ContDiffOn ℝ ∞ (mu0 k r z z') {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w}` using `NFRadRedA.muZ_contDiffOn hsec`. Establish `hdiff : DifferentiableAt ℝ (mu0 k r z z') ζ` using `(hcd.differentiableOn (by simp)).differentiableAt (hA.mem_nhds hζ)`.

Take `⟨D, hD⟩ : ∃ D : ℂ →L[ℝ] Q.Mx k r, HasFDerivAt (mu0 k r z z') D ζ` from `⟨_, hdiff.hasFDerivAt⟩`. Establish `hG : ∀ᶠ w in 𝓝 ζ, mu0 k r z z' w ∈ Q.Glev k r (Fin.last r)` using `by filter_upwards [hA.mem_nhds hζ] with w hw`. Conclude with `NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hw)`. Establish `hg : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r)` using `hG.self_of_nhds`. Establish `hX` using `SD.lie_of_curve hD hG`.

Establish `hrow : ∀ i, HasFDerivAt (fun w => mu0 k r z z' w i) ((ContinuousLinearMap.proj i).comp D) ζ` using `hasFDerivAt_pi'.1 hD`. Establish `hent : ∀ i j v, fderiv ℝ (fun w => mu0 k r z z' w i j) ζ v = D v i j`. Introduce `i j v`. Establish `h` using `(hasFDerivAt_pi'.1 (hrow i)) j`. Rewrite using `[h.fderiv]`.

Both sides reduce to the same expression. Establish `hs1 : D ((1 / 2 : ℝ) • (1 : ℂ)) = (1 / 2 : ℝ) • D 1` using `map_smul D _ _`. Establish `hs2 : D ((-(1 / 2) : ℝ) • Complex.I) = (-(1 / 2) : ℝ) • D Complex.I` using `map_smul D _ _`. Establish `hs3 : D ((1 / 2 : ℝ) • Complex.I) = (1 / 2 : ℝ) • D Complex.I` using `map_smul D _ _`. Establish `e1 : etaZ k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) + Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((-(1 / 2) : ℝ) • Complex.I))`.

Unfold `etaZ`. Rewrite using `[← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs2]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, NF.dZ, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : etaZb k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) + Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • Complex.I))`. Unfold `etaZb`. Rewrite using `[← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs3]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, NF.dZb, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨p1, p2⟩` from `Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((-(1 / 2) : ℝ) • Complex.I))`. Take `⟨q1, q2⟩` from `Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((1 / 2 : ℝ) • Complex.I))`. Rewrite `p1`, `p2` using `[← e1]`. Rewrite `q1`, `q2` using `[← e2]`. Establish `hmem : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z'`.

Use `⟨hg, ?_⟩` and prove the remaining obligations. Use `show 0 < Complex.normSq (Q.zetaL k r z z' (Fin.last r) (NF.muZ k r (TheSec.theSection k r z z') ζ)) - Tz k r z * Tz k r z'`. Rewrite using `[NFRadRedA.zeta_muZ hz hz' hsec hζ]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨⟨by rw [p1]; exact hX _, by rw [p2]; exact hX _⟩, ⟨by rw [q1]; exact hX _, by rw [q2]; exact hX _⟩, hmem, ?_⟩` and prove the remaining obligations.

Introduce `E _ _ F hF`. Take `⟨U, F', hU, hgU, hFc, he⟩` from `hF _ hmem`. Establish `hd : DifferentiableAt ℝ F' (mu0 k r z z' ζ)` using `(hFc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Establish `hR : ∀ v, RdV ((mu0 k r z z' ζ)⁻¹ * D v) F (mu0 k r z z' ζ) = fderiv ℝ F' (mu0 k r z z' ζ) (D v)`. Introduce `v`.

Establish `h` using `(Qx2.hasDeriv_ext hU hgU hg (hX v) hd he).deriv`. Rewrite `h` using `[← Matrix.mul_assoc, FrameEntries.mul_inv_uh hg.1, Matrix.one_mul]`. Conclude with `h`. Establish `hC : HasFDerivAt (fun w => F (mu0 k r z z' w)) ((fderiv ℝ F' (mu0 k r z z' ζ)).comp D) ζ`. Use `(hd.hasFDerivAt.comp ζ hD).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hG, hD.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with w h1 h2`. Conclude with `he _ h2 h1`. Prove the components needed by the constructor for the conclusion. Unfold `Rc dZV`. Rewrite using `[p1, p2, hR, hR, hC.fderiv, hs1, hs2]`.

Simplify using `only [ContinuousLinearMap.comp_apply, map_smul]`. Rewrite using `[← Complex.coe_smul, ← Complex.coe_smul]`. Use `push_cast`. Use `module`. Unfold `Rc dZbV`.

Rewrite using `[q1, q2, hR, hR, hC.fderiv, hs1, hs3]`. Simplify using `only [ContinuousLinearMap.comp_apply, map_smul]`. Rewrite using `[← Complex.coe_smul, ← Complex.coe_smul]`. Use `push_cast`. Use `module`.
-/
theorem section_derivative_holds : SecDeriv := by
  intro k r z z' hk hz hz' hT hT' ζ hζ
  have hsec := TheSec.theSection_isSection k r z z' hk hz hz' hT hT'
  have hA : IsOpen {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  have hcd : ContDiffOn ℝ ∞ (mu0 k r z z') {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    NFRadRedA.muZ_contDiffOn hsec
  have hdiff : DifferentiableAt ℝ (mu0 k r z z') ζ :=
    (hcd.differentiableOn (by simp)).differentiableAt (hA.mem_nhds hζ)
  obtain ⟨D, hD⟩ : ∃ D : ℂ →L[ℝ] Q.Mx k r, HasFDerivAt (mu0 k r z z') D ζ := ⟨_, hdiff.hasFDerivAt⟩
  have hG : ∀ᶠ w in 𝓝 ζ, mu0 k r z z' w ∈ Q.Glev k r (Fin.last r) := by
    filter_upwards [hA.mem_nhds hζ] with w hw
    exact NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hw)
  have hg : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) := hG.self_of_nhds
  have hX := SD.lie_of_curve hD hG
  have hrow : ∀ i, HasFDerivAt (fun w => mu0 k r z z' w i) ((ContinuousLinearMap.proj i).comp D) ζ :=
    hasFDerivAt_pi'.1 hD
  have hent : ∀ i j v, fderiv ℝ (fun w => mu0 k r z z' w i j) ζ v = D v i j := by
    intro i j v
    have h := (hasFDerivAt_pi'.1 (hrow i)) j
    rw [h.fderiv]
    rfl
  have hs1 : D ((1 / 2 : ℝ) • (1 : ℂ)) = (1 / 2 : ℝ) • D 1 := map_smul D _ _
  have hs2 : D ((-(1 / 2) : ℝ) • Complex.I) = (-(1 / 2) : ℝ) • D Complex.I := map_smul D _ _
  have hs3 : D ((1 / 2 : ℝ) • Complex.I) = (1 / 2 : ℝ) • D Complex.I := map_smul D _ _
  have e1 : etaZ k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((-(1 / 2) : ℝ) • Complex.I)) := by
    unfold etaZ
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs2]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZ, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have e2 : etaZb k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • Complex.I)) := by
    unfold etaZb
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs3]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZb, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  obtain ⟨p1, p2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((-(1 / 2) : ℝ) • Complex.I))
  obtain ⟨q1, q2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((1 / 2 : ℝ) • Complex.I))
  rw [← e1] at p1 p2
  rw [← e2] at q1 q2
  have hmem : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' := by
    refine ⟨hg, ?_⟩
    show 0 < Complex.normSq (Q.zetaL k r z z' (Fin.last r) (NF.muZ k r (TheSec.theSection k r z z') ζ)) -
      Tz k r z * Tz k r z'
    rw [NFRadRedA.zeta_muZ hz hz' hsec hζ]
    linarith
  refine ⟨⟨by rw [p1]; exact hX _, by rw [p2]; exact hX _⟩, ⟨by rw [q1]; exact hX _, by rw [q2]; exact hX _⟩, hmem, ?_⟩
  intro E _ _ F hF
  obtain ⟨U, F', hU, hgU, hFc, he⟩ := hF _ hmem
  have hd : DifferentiableAt ℝ F' (mu0 k r z z' ζ) :=
    (hFc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hR : ∀ v, RdV ((mu0 k r z z' ζ)⁻¹ * D v) F (mu0 k r z z' ζ) = fderiv ℝ F' (mu0 k r z z' ζ) (D v) := by
    intro v
    have h := (Qx2.hasDeriv_ext hU hgU hg (hX v) hd he).deriv
    rw [← Matrix.mul_assoc, FrameEntries.mul_inv_uh hg.1, Matrix.one_mul] at h
    exact h
  have hC : HasFDerivAt (fun w => F (mu0 k r z z' w)) ((fderiv ℝ F' (mu0 k r z z' ζ)).comp D) ζ := by
    refine (hd.hasFDerivAt.comp ζ hD).congr_of_eventuallyEq ?_
    filter_upwards [hG, hD.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with w h1 h2
    exact he _ h2 h1
  constructor
  · unfold Rc dZV
    rw [p1, p2, hR, hR, hC.fderiv, hs1, hs2]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  · unfold Rc dZbV
    rw [q1, q2, hR, hR, hC.fderiv, hs1, hs3]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
