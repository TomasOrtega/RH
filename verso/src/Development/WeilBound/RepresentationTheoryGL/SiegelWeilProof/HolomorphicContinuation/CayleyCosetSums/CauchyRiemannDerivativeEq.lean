import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetNeZeroOfInG

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.SiegelWeilFormula

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toC (L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ) (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := by
    have hv : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hv, L.map_add, L.map_smul, L.map_smul, hL, RingHom.id_apply, smul_eq_mul]
    simp only [Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  cont := L.cont

/- English proof (translation)
Establish `key : ∀ E : M2 n, (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • E))) = fun t : ℝ => Φ (x * II.cE E t)`. Introduce `E`. Use function extensionality and compare the values at `t`. Simplify using `only [II.cE, Complex.coe_smul]`. Express the relevant statement in the definitionally equal form `deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z1 A))) 0 + Complex.I * deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z2 A))) 0 = _`.

Rewrite using `[key, key, h1.deriv, h2.deriv]`.
-/
theorem cauchy_riemann_derivative_eq (A : M2 n) (Φ : M2 n → ℂ) (x : M2 n) (d1 d2 : ℂ)
    (h1 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z1 A) t)) d1 0)
    (h2 : HasDerivAt (fun t : ℝ => Φ (x * II.cE (Z2 A) t)) d2 0) : rC A Φ x = d1 + Complex.I * d2 := by
  have key : ∀ E : M2 n, (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • E))) = fun t : ℝ => Φ (x * II.cE E t) := by
    intro E; funext t; simp only [II.cE, Complex.coe_smul]
  change deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z1 A))) 0 +
    Complex.I * deriv (fun t : ℝ => Φ (x * NormedSpace.exp ((t : ℂ) • Z2 A))) 0 = _
  rw [key, key, h1.deriv, h2.deriv]

/- English proof (translation)
Introduce `n m e φ Φ Ω hΩ hGΩ hΦ hΦφ hlaw hrC`. Establish `hF0 : ∀ y : GR n, F0 m 0 e y ≠ 0`. Introduce `y`. Rewrite using `[ha.1]`. Unfold `holomorphicScalarSection`.

Conclude with `mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_inG y.2)) (zpow_ne_zero _ (AbsSt.detU1 n y).1)`. Use `set H : Matrix (Fin n) (Fin n) ℂ → ℂ := fun Z => if h : ∃ y : GR n, zOfE (mR y) = Z then φ h.choose / F0 m 0 e h.choose else 0 with hHdef`. Establish `hH : ∀ y : GR n, φ y = F0 m 0 e y * H (zOfE (mR y))`. Introduce `y`. Establish `hex : ∃ y' : GR n, zOfE (mR y') = zOfE (mR y)` using `⟨y, rfl⟩`.

Simplify using `only [hHdef, dif_pos hex]`. Establish `hz : zOfE (mR hex.choose) = zOfE (mR y)` using `hex.choose_spec`. Establish `hk` using `hfib n hex.choose y hz`. Establish `hkK : (hex.choose⁻¹ * y) ∈ AbsSt.KR n` using `hk`. Establish `e1 : y = hex.choose * (hex.choose⁻¹ * y)` using `by group`.

Establish `h1 : φ y = φ hex.choose * F0 m 0 e (hex.choose⁻¹ * y)` using `by conv_lhs => rw [e1]`. Conclude with `hlaw _ _ hk`. Establish `h2 : F0 m 0 e y = F0 m 0 e hex.choose * F0 m 0 e (hex.choose⁻¹ * y)` using `by conv_lhs => rw [e1]`. Conclude with `((AbsSt.mult n m 0 e).1 _ _ hkK).1`. Rewrite using `[h1, h2]`.

Clear denominators, using `[hF0 hex.choose]` for the nonvanishing conditions. Use `⟨fun Z => H (Matrix.of Z), ?_, fun y => ?_⟩` and prove the remaining obligations. Use `swap`. Simplify using `only [↓reduceIte]`. Conclude with `hH y`.

Introduce `Z0' hZ0`. Use `set Z0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of Z0' with hZ0def`. Take `⟨s, hs, hsd⟩` from `hsec n Z0 hZ0`. Take `⟨hxG, hxd, hxz⟩` from `hs.self_of_nhds`. Use `set x0 := s Z0 with hx0`.

Use `set y0 := toGR x0 hxG with hy0`. Establish `hu1 : (u1 x0).det ≠ 0` using `(AbsSt.detU1 n y0).1`. Take `⟨hzd, hFd, hlow, hsig, hW⟩` from `ha.2 n x0 hxd hu1`. Establish `hFx0 : holomorphicScalarSection m e x0 ≠ 0`. Use `hF0 y0` as an intermediate fact.

Rewrite `this` using `[ha.1]`. Then use the resulting hypothesis. Establish `heq : H =ᶠ[𝓝 Z0] fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹` using `by filter_upwards [hs] with Z hZ`. Take `⟨hG, -, hzZ⟩` from `hZ`. Establish `h1` using `hH (toGR (s Z) hG)`. Rewrite `h1` using `[mR_toGR, hzZ, ← hΦφ (toGR (s Z) hG), mR_toGR]`.

Establish `h2 : F0 m 0 e (toGR (s Z) hG) = holomorphicScalarSection m e (s Z)` using `by rw [ha.1, mR_toGR]`. Establish `h4 : holomorphicScalarSection m e (s Z) ≠ 0` using `by rw [← h2]; exact hF0 _`. Rewrite using `[← div_eq_mul_inv, eq_div_iff h4, mul_comm, ← h2, ← h1]`. Establish `hΦd : DifferentiableAt ℝ Φ x0` using `(hΦ.contDiffAt (hΩ.mem_nhds (hGΩ hxG))).differentiableAt (by simp)`. Establish `hsd' : DifferentiableAt ℝ s Z0` using `hsd.differentiableAt one_ne_zero`.

Establish `hFr : DifferentiableAt ℝ (holomorphicScalarSection m e) x0` using `(hFd m e).restrictScalars ℝ`. Establish `hzr : DifferentiableAt ℝ zOfE x0` using `hzd.restrictScalars ℝ`. Establish `hR : DifferentiableAt ℝ (fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹) Z0` using `(hΦd.comp Z0 hsd').mul ((hFr.comp Z0 hsd').inv hFx0)`. Establish `hHd : DifferentiableAt ℝ H Z0` using `hR.congr_of_eventuallyEq heq`. Use `set L := fderiv ℝ H Z0 with hLdef`.

Establish `hHd' : DifferentiableAt ℝ H (zOfE x0)` using `by rw [hxz]; exact hHd`. Establish `key : ∀ Q : Matrix (Fin n) (Fin n) ℂ, L (Complex.I • (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) = Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))`. Introduce `Q`. Use `set g : M2 n → ℂ := fun x => holomorphicScalarSection m e x * H (zOfE x) with hg`. Establish `hcurve : ∀ E : M2 n, sig E = E → ∀ t : ℝ, Φ (x0 * II.cE E t) = g (x0 * II.cE E t)`.

Introduce `E hE t`. Establish `hp : InG (x0 * II.cE E t)` using `inG_mul hxG (inG_cE hE t)`. Use `hH (toGR _ hp)` as an intermediate fact. Rewrite `this` using `[mR_toGR, ha.1, mR_toGR]`. Rewrite `this` using `[← hΦφ (toGR _ hp), mR_toGR]`.

Conclude with `this`. Establish `hr : rC (lowQ Q) Φ x0 = 0` using `hrC y0 Q`. Establish `hder : ∀ E : M2 n, sig E = E → HasDerivAt (fun t : ℝ => Φ (x0 * II.cE E t)) (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E) * H Z0 + holomorphicScalarSection m e x0 * L (fderiv ℂ zOfE x0 (x0 * E))) 0`. Introduce `E hE`. Establish `hc : HasDerivAt (fun t : ℝ => x0 * II.cE E t) (x0 * E) 0` using `(II.mulL x0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 E)`.

Establish `hc0 : x0 * II.cE E 0 = x0` using `by rw [II.cE_zero, Matrix.mul_one]`. Establish `hFc : HasDerivAt (fun t : ℝ => holomorphicScalarSection m e (x0 * II.cE E t)) (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E)) 0`. Establish `h : HasFDerivAt (holomorphicScalarSection m e) ((fderiv ℂ (holomorphicScalarSection m e) x0).restrictScalars ℝ) (x0 * II.cE E 0)`. Rewrite using `[hc0]`. Conclude with `(hFd m e).hasFDerivAt.restrictScalars ℝ`.

Conclude with `h.comp_hasDerivAt (0 : ℝ) hc`. Establish `hzc : HasDerivAt (fun t : ℝ => zOfE (x0 * II.cE E t)) (fderiv ℂ zOfE x0 (x0 * E)) 0`. Establish `h : HasFDerivAt zOfE ((fderiv ℂ zOfE x0).restrictScalars ℝ) (x0 * II.cE E 0)`. Rewrite using `[hc0]`. Conclude with `hzd.hasFDerivAt.restrictScalars ℝ`.

Conclude with `h.comp_hasDerivAt (0 : ℝ) hc`. Establish `hHc : HasDerivAt (fun t : ℝ => H (zOfE (x0 * II.cE E t))) (L (fderiv ℂ zOfE x0 (x0 * E))) 0`. Establish `h : HasFDerivAt H L (zOfE (x0 * II.cE E 0))`. Rewrite using `[hc0, hxz]`. Conclude with `hHd.hasFDerivAt`.

Conclude with `h.comp_hasDerivAt (0 : ℝ) hzc`. Establish `hprod` using `hFc.mul hHc`. Rewrite `hprod` using `[hc0, hxz]`. Use `hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Conclude with `hcurve E hE t`.

Rewrite `hr` using `[cauchy_riemann_derivative_eq (lowQ Q) Φ x0 _ _ (hder _ (conj_real_part_fixed _)) (hder _ (conj_imaginary_part_fixed _))]`. Establish `hsum : ∀ (D : M2 n →L[ℂ] Matrix (Fin n) (Fin n) ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I • D (x0 * Z2 (lowQ Q)) = D (x0 * lowQ Q)`. Introduce `D`. Rewrite using `[← D.map_smul, ← D.map_add, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]`. Establish `hsum' : ∀ (D : M2 n →L[ℂ] ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I * D (x0 * Z2 (lowQ Q)) = D (x0 * lowQ Q)`.

Introduce `D`. Rewrite using `[← smul_eq_mul Complex.I (D _), ← D.map_smul, ← D.map_add, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]`. Establish `hsumF : fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z1 (lowQ Q)) + Complex.I * fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z2 (lowQ Q)) = 0` using `(hsum' _).trans ((hlow Q).2 m e)`. Establish `hsumZ` using `hsum (fderiv ℂ zOfE x0)`. Rewrite `hsumZ` using `[(hlow Q).1]`.

Establish `hv1 : fderiv ℂ zOfE x0 (x0 * Z1 (lowQ Q)) = -(Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))` using `eq_neg_of_add_eq_zero_left hsumZ`. Rewrite `hr` using `[hv1, map_neg]`. Establish `hr2 : holomorphicScalarSection m e x0 * (-L (Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) + Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) = 0`. Rewrite using `[← hr]`. Take the linear combination `(-(H Z0)) * hsumF`.

Break down `mul_eq_zero.1 hr2 with h | h` into its components or cases. Conclude with `absurd h hFx0`. Take the linear combination `-h`. Establish `hsurj : ∀ v : Matrix (Fin n) (Fin n) ℂ, ∃ Q, fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)) = v`. Introduce `v`.

Establish `hWu : IsUnit (WM x0).det` using `isUnit_iff_ne_zero.2 (hW hxG)`. Establish `hUu : IsUnit (u1 x0).det` using `isUnit_iff_ne_zero.2 hu1`. Use `⟨((-(2 * Complex.I)) • ((WM x0)⁻¹ * v * u1 x0))ᴴ, ?_⟩` and prove the remaining obligations. Rewrite using `[Z2, Matrix.mul_smul, map_smul, Matrix.mul_sub, map_sub, (hlow _).1, hsig, Matrix.conjTranspose_conjTranspose, zero_sub]`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul]`.

Establish `: WM x0 * ((WM x0)⁻¹ * v * u1 x0) * (u1 x0)⁻¹ = v`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]`. Rewrite using `[this]`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Establish `hLC : ∀ v, L (Complex.I • v) = Complex.I * L v`. Introduce `v`. Take `⟨Q, hQ⟩` from `hsurj v`. Use `key Q` as an intermediate fact.

Rewrite `this` using `[hQ]`. Conclude with `this`. Establish `hC : HasFDerivAt H (toC L hLC) Z0` using `hasFDerivAt_of_restrictScalars ℝ hHd.hasFDerivAt (by ext; rfl)`. Establish `hC' : DifferentiableAt ℂ H Z0` using `hC.differentiableAt`. Conclude with `(hC'.comp Z0' (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv.differentiableAt).differentiableWithinAt`.
-/
theorem crLem_of (hsec : LocSec) (hfib : Fib) (ha : CauchyRiemannFacts) : CRLem := by
  intro n m e φ Φ Ω hΩ hGΩ hΦ hΦφ hlaw hrC
  classical
  have hF0 : ∀ y : GR n, F0 m 0 e y ≠ 0 := by
    intro y
    rw [ha.1]
    unfold holomorphicScalarSection
    exact mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_inG y.2)) (zpow_ne_zero _ (AbsSt.detU1 n y).1)
  set H : Matrix (Fin n) (Fin n) ℂ → ℂ := fun Z =>
    if h : ∃ y : GR n, zOfE (mR y) = Z then φ h.choose / F0 m 0 e h.choose else 0 with hHdef
  have hH : ∀ y : GR n, φ y = F0 m 0 e y * H (zOfE (mR y)) := by
    intro y
    have hex : ∃ y' : GR n, zOfE (mR y') = zOfE (mR y) := ⟨y, rfl⟩
    simp only [hHdef, dif_pos hex]
    have hz : zOfE (mR hex.choose) = zOfE (mR y) := hex.choose_spec
    have hk := hfib n hex.choose y hz
    have hkK : (hex.choose⁻¹ * y) ∈ AbsSt.KR n := hk
    have e1 : y = hex.choose * (hex.choose⁻¹ * y) := by group
    have h1 : φ y = φ hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact hlaw _ _ hk
    have h2 : F0 m 0 e y = F0 m 0 e hex.choose * F0 m 0 e (hex.choose⁻¹ * y) := by
      conv_lhs => rw [e1]
      exact ((AbsSt.mult n m 0 e).1 _ _ hkK).1
    rw [h1, h2]
    field_simp [hF0 hex.choose]
  refine ⟨fun Z => H (Matrix.of Z), ?_, fun y => ?_⟩
  swap
  · simp only [↓reduceIte]
    exact hH y
  intro Z0' hZ0
  set Z0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of Z0' with hZ0def
  obtain ⟨s, hs, hsd⟩ := hsec n Z0 hZ0
  obtain ⟨hxG, hxd, hxz⟩ := hs.self_of_nhds
  set x0 := s Z0 with hx0
  set y0 := toGR x0 hxG with hy0
  have hu1 : (u1 x0).det ≠ 0 := (AbsSt.detU1 n y0).1
  obtain ⟨hzd, hFd, hlow, hsig, hW⟩ := ha.2 n x0 hxd hu1
  have hFx0 : holomorphicScalarSection m e x0 ≠ 0 := by
    have := hF0 y0
    rwa [ha.1] at this
  have heq : H =ᶠ[𝓝 Z0] fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹ := by
    filter_upwards [hs] with Z hZ
    obtain ⟨hG, -, hzZ⟩ := hZ
    have h1 := hH (toGR (s Z) hG)
    rw [mR_toGR, hzZ, ← hΦφ (toGR (s Z) hG), mR_toGR] at h1
    have h2 : F0 m 0 e (toGR (s Z) hG) = holomorphicScalarSection m e (s Z) := by rw [ha.1, mR_toGR]
    have h4 : holomorphicScalarSection m e (s Z) ≠ 0 := by rw [← h2]; exact hF0 _
    rw [← div_eq_mul_inv, eq_div_iff h4, mul_comm, ← h2, ← h1]
  have hΦd : DifferentiableAt ℝ Φ x0 :=
    (hΦ.contDiffAt (hΩ.mem_nhds (hGΩ hxG))).differentiableAt (by simp)
  have hsd' : DifferentiableAt ℝ s Z0 := hsd.differentiableAt one_ne_zero
  have hFr : DifferentiableAt ℝ (holomorphicScalarSection m e) x0 := (hFd m e).restrictScalars ℝ
  have hzr : DifferentiableAt ℝ zOfE x0 := hzd.restrictScalars ℝ
  have hR : DifferentiableAt ℝ (fun Z => Φ (s Z) * (holomorphicScalarSection m e (s Z))⁻¹) Z0 :=
    (hΦd.comp Z0 hsd').mul ((hFr.comp Z0 hsd').inv hFx0)
  have hHd : DifferentiableAt ℝ H Z0 := hR.congr_of_eventuallyEq heq
  set L := fderiv ℝ H Z0 with hLdef
  have hHd' : DifferentiableAt ℝ H (zOfE x0) := by rw [hxz]; exact hHd

  have key : ∀ Q : Matrix (Fin n) (Fin n) ℂ,
      L (Complex.I • (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) =
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) := by
    intro Q
    set g : M2 n → ℂ := fun x => holomorphicScalarSection m e x * H (zOfE x) with hg
    have hcurve : ∀ E : M2 n, sig E = E → ∀ t : ℝ, Φ (x0 * II.cE E t) = g (x0 * II.cE E t) := by
      intro E hE t
      have hp : InG (x0 * II.cE E t) := inG_mul hxG (inG_cE hE t)
      have := hH (toGR _ hp)
      rw [mR_toGR, ha.1, mR_toGR] at this
      rw [← hΦφ (toGR _ hp), mR_toGR] at this
      exact this
    have hr : rC (lowQ Q) Φ x0 = 0 := hrC y0 Q
    have hder : ∀ E : M2 n, sig E = E → HasDerivAt (fun t : ℝ => Φ (x0 * II.cE E t))
        (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E) * H Z0 + holomorphicScalarSection m e x0 * L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
      intro E hE
      have hc : HasDerivAt (fun t : ℝ => x0 * II.cE E t) (x0 * E) 0 :=
        (II.mulL x0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 E)
      have hc0 : x0 * II.cE E 0 = x0 := by rw [II.cE_zero, Matrix.mul_one]
      have hFc : HasDerivAt (fun t : ℝ => holomorphicScalarSection m e (x0 * II.cE E t)) (fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * E)) 0 := by
        have h : HasFDerivAt (holomorphicScalarSection m e) ((fderiv ℂ (holomorphicScalarSection m e) x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact (hFd m e).hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hzc : HasDerivAt (fun t : ℝ => zOfE (x0 * II.cE E t)) (fderiv ℂ zOfE x0 (x0 * E)) 0 := by
        have h : HasFDerivAt zOfE ((fderiv ℂ zOfE x0).restrictScalars ℝ) (x0 * II.cE E 0) := by
          rw [hc0]; exact hzd.hasFDerivAt.restrictScalars ℝ
        exact h.comp_hasDerivAt (0 : ℝ) hc
      have hHc : HasDerivAt (fun t : ℝ => H (zOfE (x0 * II.cE E t))) (L (fderiv ℂ zOfE x0 (x0 * E))) 0 := by
        have h : HasFDerivAt H L (zOfE (x0 * II.cE E 0)) := by
          rw [hc0, hxz]; exact hHd.hasFDerivAt
        exact h.comp_hasDerivAt (0 : ℝ) hzc
      have hprod := hFc.mul hHc
      rw [hc0, hxz] at hprod
      refine hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      exact hcurve E hE t
    rw [cauchy_riemann_derivative_eq (lowQ Q) Φ x0 _ _ (hder _ (conj_real_part_fixed _)) (hder _ (conj_imaginary_part_fixed _))] at hr
    have hsum : ∀ (D : M2 n →L[ℂ] Matrix (Fin n) (Fin n) ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I • D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← D.map_smul, ← D.map_add, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsum' : ∀ (D : M2 n →L[ℂ] ℂ), D (x0 * Z1 (lowQ Q)) + Complex.I * D (x0 * Z2 (lowQ Q)) =
        D (x0 * lowQ Q) := by
      intro D
      rw [← smul_eq_mul Complex.I (D _), ← D.map_smul, ← D.map_add, ← Matrix.mul_smul, ← Matrix.mul_add, real_add_imaginary_part]
    have hsumF : fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z1 (lowQ Q)) + Complex.I * fderiv ℂ (holomorphicScalarSection m e) x0 (x0 * Z2 (lowQ Q)) =
        0 := (hsum' _).trans ((hlow Q).2 m e)
    have hsumZ := hsum (fderiv ℂ zOfE x0)
    rw [(hlow Q).1] at hsumZ
    have hv1 : fderiv ℂ zOfE x0 (x0 * Z1 (lowQ Q)) = -(Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) :=
      eq_neg_of_add_eq_zero_left hsumZ
    rw [hv1, map_neg] at hr
    have hr2 : holomorphicScalarSection m e x0 * (-L (Complex.I • fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q))) +
        Complex.I * L (fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)))) = 0 := by
      rw [← hr]
      linear_combination (-(H Z0)) * hsumF
    rcases mul_eq_zero.1 hr2 with h | h
    · exact absurd h hFx0
    · linear_combination -h

  have hsurj : ∀ v : Matrix (Fin n) (Fin n) ℂ, ∃ Q, fderiv ℂ zOfE x0 (x0 * Z2 (lowQ Q)) = v := by
    intro v
    have hWu : IsUnit (WM x0).det := isUnit_iff_ne_zero.2 (hW hxG)
    have hUu : IsUnit (u1 x0).det := isUnit_iff_ne_zero.2 hu1
    refine ⟨((-(2 * Complex.I)) • ((WM x0)⁻¹ * v * u1 x0))ᴴ, ?_⟩
    rw [Z2, Matrix.mul_smul, map_smul, Matrix.mul_sub, map_sub, (hlow _).1, hsig, Matrix.conjTranspose_conjTranspose,
      zero_sub]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul]
    have : WM x0 * ((WM x0)⁻¹ * v * u1 x0) * (u1 x0)⁻¹ = v := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hUu, Matrix.mul_one]
    rw [this]
    ext i j
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    field_simp
  have hLC : ∀ v, L (Complex.I • v) = Complex.I * L v := by
    intro v
    obtain ⟨Q, hQ⟩ := hsurj v
    have := key Q
    rw [hQ] at this
    exact this
  have hC : HasFDerivAt H (toC L hLC) Z0 :=
    hasFDerivAt_of_restrictScalars ℝ hHd.hasFDerivAt (by ext; rfl)
  have hC' : DifferentiableAt ℂ H Z0 := hC.differentiableAt
  exact (hC'.comp Z0' (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv.differentiableAt).differentiableWithinAt

end PositivityTheory.Rg.Sw.HSt.CR
