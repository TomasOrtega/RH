import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CubeIcoMeas
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta

open Complex Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.CanTh

noncomputable section

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

variable (τ) in

def realPt : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ fun i => (p (.inr i) : ℂ)
  map_add' p q := by
    funext i
    simp only [mulVec, dotProduct, Pi.add_apply, ofReal_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    funext i
    simp only [mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_mul,
      RingHom.id_apply, real_smul, mul_add, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realPt_apply (p : Fin g ⊕ Fin g → ℝ) :
    realPt τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ fun i => (p (.inr i) : ℂ) := rfl

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `p hp0`. Rewrite `hp0` using `[realPt_apply]`. Establish `him : ∀ i, ∑ j, (τ i j).im * p (.inr j) = 0`. Introduce `i`.

Use `congrArg (fun z => (z i).im) hp0` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct]`. Establish `hu : (fun i => p (.inr i)) = 0`. Assume the negation of the conclusion as `hne`. Establish `hpos` using `hp.dotProduct_mulVec_pos hne`.

Establish `hzero : (τ.map Complex.im) *ᵥ (fun i => p (.inr i)) = 0`. Use function extensionality and compare the values at `i`. Simplify `him i` using `[mulVec, dotProduct]`. Rewrite `hpos` using `[hzero]`. Simplify using `at hpos`.

Establish `hu' : ∀ j, p (.inr j) = 0` using `fun j => congrFun hu j`. Establish `hre : ∀ i, p (.inl i) = 0`. Introduce `i`. Use `congrArg (fun z => (z i).re) hp0` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, hu']`.

Use function extensionality and compare the values at `j`. Break down `j with i | i` into its components or cases. Conclude with `hre i`. Conclude with `hu' i`.
-/
theorem realPt_injective (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (realPt τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp0
  rw [realPt_apply] at hp0
  have him : ∀ i, ∑ j, (τ i j).im * p (.inr j) = 0 := by
    intro i
    have := congrArg (fun z => (z i).im) hp0
    simpa [mulVec, dotProduct] using this
  have hu : (fun i => p (.inr i)) = 0 := by
    by_contra hne
    have hpos := hp.dotProduct_mulVec_pos hne
    have hzero : (τ.map Complex.im) *ᵥ (fun i => p (.inr i)) = 0 := by
      funext i
      simpa [mulVec, dotProduct] using him i
    rw [hzero] at hpos
    simp at hpos
  have hu' : ∀ j, p (.inr j) = 0 := fun j => congrFun hu j
  have hre : ∀ i, p (.inl i) = 0 := by
    intro i
    have := congrArg (fun z => (z i).re) hp0
    simpa [mulVec, dotProduct, hu'] using this
  funext j
  rcases j with i | i
  · exact hre i
  · exact hu' i

/- English proof (translation)
Establish `hQ : realPt τ p ⬝ᵥ imInv τ *ᵥ realPt τ p = hermForm (imInv τ) (realPt τ p) (realPt τ p) + 2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ))`. Establish `h` using `dot_imInv_eq_hermForm_add hp (fun i => p (.inr i)) (fun i => p (.inl i)) (realPt τ p)`. Rewrite `h`, the goal using `[realPt_apply]`. Conclude with `h`. Establish `hIm : (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im = (fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i)`.

Rewrite using `[realPt_apply]`. Simplify using `[dotProduct, mulVec, Complex.mul_im, Finset.mul_sum, mul_comm, mul_left_comm]`. Establish `hre : ((π : ℂ) / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p) + 2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)))).re = π / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re - π * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im`. Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ A B C T : ℝ, 2 * A + B = C → Real.exp A ^ 2 * T * Real.exp B = T * Real.exp C`. Introduce `A B C T h`. Rewrite using `[← h, Real.exp_add, sq, ← Real.exp_add A A, two_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[canTh, hQ, norm_mul, mul_pow, Complex.norm_exp, hre, hIm]`.

Apply `key` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_canTh_realPt (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ)
    (p : Fin g ⊕ Fin g → ℝ) :
    ‖canTh τ a b (realPt τ p)‖ ^ 2 *
        Real.exp (-π * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re) =
      ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (realPt τ p)‖ ^ 2 *
        Real.exp (-2 * π * ((fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i))) := by
  have hQ : realPt τ p ⬝ᵥ imInv τ *ᵥ realPt τ p =
      hermForm (imInv τ) (realPt τ p) (realPt τ p) +
        2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)) := by
    have h := dot_imInv_eq_hermForm_add hp (fun i => p (.inr i)) (fun i => p (.inl i)) (realPt τ p)
    rw [realPt_apply] at h ⊢
    exact h
  have hIm : (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im =
      (fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i) := by
    rw [realPt_apply]
    simp [dotProduct, mulVec, Complex.mul_im, Finset.mul_sum, mul_comm, mul_left_comm]
  have hre : ((π : ℂ) / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p) +
      2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)))).re =
      π / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re -
        π * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im := by
    simp [Complex.mul_re]
    ring
  have key : ∀ A B C T : ℝ, 2 * A + B = C → Real.exp A ^ 2 * T * Real.exp B = T * Real.exp C := by
    intro A B C T h
    rw [← h, Real.exp_add, sq, ← Real.exp_add A A, two_mul]
    ring
  rw [canTh, hQ, norm_mul, mul_pow, Complex.norm_exp, hre, hIm]
  apply key
  ring

variable (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
  (φ : EuclideanSpace ℂ (Fin g) ≃ₗ[ℂ] (Fin g → ℂ))

def realCoord : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin g) :=
  ((realPt τ).linearEquivOfInjective (realPt_injective hs hp) (by
    simp [Module.finrank_pi_fintype, mul_two])).trans (φ.symm.restrictScalars ℝ)

/- English proof (translation)
Simplify using `[realCoord]`.
-/
theorem apply_realCoord (p : Fin g ⊕ Fin g → ℝ) : φ (realCoord hs hp φ p) = realPt τ p := by
  simp [realCoord]

def sumBasis : Module.Basis (Fin g ⊕ Fin g) ℝ (EuclideanSpace ℂ (Fin g)) :=
  (Pi.basisFun ℝ _).map (realCoord hs hp φ)

def perBasis : Module.Basis (Fin (2 * Fintype.card (Fin g))) ℝ (EuclideanSpace ℂ (Fin g)) :=
  (sumBasis hs hp φ).reindex (finSumFinEquiv.trans (finCongr (by simp [two_mul])))

/- English proof (translation)
Establish `hsum : ∀ m : Fin g ⊕ Fin g → ℤ, ∑ j, m j • sumBasis hs hp φ j = realCoord hs hp φ fun j => (m j : ℝ)`. Introduce `m`. Establish `hm : (fun j => (m j : ℝ)) = ∑ j, (m j : ℝ) • Pi.single j (1 : ℝ)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Simplify using `only [sumBasis, Module.Basis.map_apply, Pi.basisFun_apply]`. Rewrite using `[hm, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Int.cast_smul_eq_zsmul]`. Use `show y ∈ Submodule.span ℤ (Set.range (perBasis hs hp φ)) ↔ _`.

Rewrite using `[perBasis, Module.Basis.range_reindex, Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, by rw [← hc, hsum]⟩`. Introduce and unpack `⟨m, hm⟩`.

Conclude with `⟨m, by rw [hsum, hm]⟩`.
-/
theorem mem_lat_perBasis (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (perBasis hs hp φ) ↔
      ∃ m : Fin g ⊕ Fin g → ℤ, y = realCoord hs hp φ fun j => (m j : ℝ) := by
  have hsum : ∀ m : Fin g ⊕ Fin g → ℤ,
      ∑ j, m j • sumBasis hs hp φ j = realCoord hs hp φ fun j => (m j : ℝ) := by
    intro m
    have hm : (fun j => (m j : ℝ)) = ∑ j, (m j : ℝ) • Pi.single j (1 : ℝ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    simp only [sumBasis, Module.Basis.map_apply, Pi.basisFun_apply]
    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Int.cast_smul_eq_zsmul]
  show y ∈ Submodule.span ℤ (Set.range (perBasis hs hp φ)) ↔ _
  rw [perBasis, Module.Basis.range_reindex, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc, hsum]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hsum, hm]⟩

variable (hφ : ∀ v w, Hf v w = hermForm (imInv τ) (φ v) (φ w))

include hφ in

/- English proof (translation)
Rewrite using `[hφ, apply_realCoord, apply_realCoord, realPt_apply, realPt_apply, im_hermForm_imInv hs hp]`. Simplify using `[dotProduct]`.
-/
theorem im_Hf_realCoord (p q : Fin g ⊕ Fin g → ℝ) :
    (Hf (realCoord hs hp φ p) (realCoord hs hp φ q)).im =
      ∑ i, p (.inr i) * q (.inl i) - ∑ i, p (.inl i) * q (.inr i) := by
  rw [hφ, apply_realCoord, apply_realCoord, realPt_apply, realPt_apply, im_hermForm_imInv hs hp]
  simp [dotProduct]

/- English proof (translation)
Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[apply_realCoord, realPt_apply, h]`. Simplify using the standard rewrite rules.
-/
private theorem eq_realCoord_of_eq_int_add_tau_mulVec {y : EuclideanSpace ℂ (Fin g)} {m n : Fin g → ℤ}
    (h : φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    y = realCoord hs hp φ fun j => ((Sum.elim m n j : ℤ) : ℝ) := by
  apply φ.injective
  rw [apply_realCoord, realPt_apply, h]
  simp

def torus (a b : Fin g → ℝ) : GT (Fin g) where
  b := perBasis hs hp φ
  integral x y hx hy := by
    obtain ⟨m, rfl⟩ := (mem_lat_perBasis hs hp φ x).1 hx
    obtain ⟨n, rfl⟩ := (mem_lat_perBasis hs hp φ y).1 hy
    refine ⟨∑ i, m (.inr i) * n (.inl i) - ∑ i, m (.inl i) * n (.inr i), ?_⟩
    rw [im_Hf_realCoord hs hp φ hφ]
    push_cast
    rfl
  perfect f := by
    let e : Fin g ⊕ Fin g → lat (perBasis hs hp φ) := fun j =>
      ⟨_, (mem_lat_perBasis hs hp φ _).2 ⟨Pi.single j 1, rfl⟩⟩
    refine ⟨_, (mem_lat_perBasis hs hp φ _).2
      ⟨Sum.elim (fun i => -f (e (.inr i))) fun i => f (e (.inl i)), rfl⟩, fun y => ?_⟩
    obtain ⟨n, hn⟩ := (mem_lat_perBasis hs hp φ y).1 y.2
    have hy : y = ∑ j, n j • e j := by
      apply Subtype.ext
      simp only [hn, e, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul_of_tower,
        ← map_zsmul, ← map_sum]
      congr 1
      funext j
      simp [Pi.single_apply]
    rw [hn, im_Hf_realCoord hs hp φ hφ, hy, map_sum]
    simp [mul_comm]
  ka y := cexp (((π * ∑ i, (realCoord hs hp φ).symm y (.inl i) * (realCoord hs hp φ).symm y (.inr i) +
    2 * π * (∑ i, a i * (realCoord hs hp φ).symm y (.inl i) -
      ∑ i, b i * (realCoord hs hp φ).symm y (.inr i)) : ℝ) : ℂ) * I)
  ka_abs _ _ := norm_exp_ofReal_mul_I _

variable (a b : Fin g → ℝ)

/- English proof (translation)
Use `show y ∈ lat (perBasis hs hp φ) ↔ _`. Rewrite using `[mem_lat_perBasis]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Use `⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩` and prove the remaining obligations.

Rewrite using `[apply_realCoord, realPt_apply]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨m, n, h⟩`. Conclude with `⟨Sum.elim m n, eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h⟩`.
-/
theorem mem_lat_torus (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (torus hs hp φ hφ a b).b ↔
      ∃ m n : Fin g → ℤ, φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) := by
  show y ∈ lat (perBasis hs hp φ) ↔ _
  rw [mem_lat_perBasis]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    rw [apply_realCoord, realPt_apply]
    simp
  · rintro ⟨m, n, h⟩
    exact ⟨Sum.elim m n, eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h⟩

/- English proof (translation)
Rewrite using `[eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h]`. Simplify using `only [torus, LinearEquiv.symm_apply_apply, canMult, Sum.elim_inl, Sum.elim_inr]`. Use `congr 1`. Simplify using `only [dotProduct]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_ka {y : EuclideanSpace ℂ (Fin g)} {m n : Fin g → ℤ}
    (h : φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    (torus hs hp φ hφ a b).ka y = canMult a b m n := by
  rw [eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h]
  simp only [torus, LinearEquiv.symm_apply_apply, canMult, Sum.elim_inl, Sum.elim_inr]
  congr 1
  simp only [dotProduct]
  push_cast
  ring

/- English proof (translation)
Use `show _ ∧ _`. Use `⟨(differentiable_canTh hp a b).comp (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable, ?_⟩` and prove the remaining obligations. Introduce `γ hγ v`. Take `⟨m, n, h⟩` from `(mem_lat_torus hs hp φ hφ a b γ).1 hγ`. Use `beta_reduce`.

Rewrite using `[map_add, h, canTh_add_period hs hp a b m n rfl, torus_ka hs hp φ hφ a b h, hφ, hφ, h]`. Simplify using `only [Nat.cast_one, one_mul]`. Put the polynomial expressions in normal form.
-/
theorem canTh_mem_Sec : (fun v => canTh τ a b (φ v)) ∈ (torus hs hp φ hφ a b).Sec 1 := by
  show _ ∧ _
  refine ⟨(differentiable_canTh hp a b).comp
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable, ?_⟩
  intro γ hγ v
  obtain ⟨m, n, h⟩ := (mem_lat_torus hs hp φ hφ a b γ).1 hγ
  beta_reduce
  rw [map_add, h, canTh_add_period hs hp a b m n rfl, torus_ka hs hp φ hφ a b h, hφ, hφ, h]
  simp only [Nat.cast_one, one_mul]
  ring_nf

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`.
-/
private theorem norm_sq_eq_re_Hf (w : EuclideanSpace ℂ (Fin g)) : ‖w‖ ^ 2 = (Hf w w).re := by
  rw [EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Establish `hpt : ∀ x : Fin g ⊕ Fin g → ℝ, (torus hs hp φ hφ a b).ptN2 1 (fun v => canTh τ a b (φ v)) ((sumBasis hs hp φ).equivFun.symm x) = ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ((fun i => (x (.inl i) : ℂ)) + τ.mulVec (fun i => (x (.inr i) : ℂ)))‖ ^ 2 * Real.exp (-2 * Real. …`. Introduce `x`. Establish `hx : (sumBasis hs hp φ).equivFun.symm x = realCoord hs hp φ x`. Simplify using `[sumBasis, Module.Basis.map_equivFun]`. Simplify using `only [hx, GT.ptN2]`.

Rewrite using `[norm_sq_eq_re_Hf, hφ, apply_realCoord, Nat.cast_one, one_mul, norm_canTh_realPt hp, realPt_apply]`. Establish `hfd : ZSpan.fundamentalDomain (torus hs hp φ hφ a b).b = ZSpan.fundamentalDomain (sumBasis hs hp φ)` using `ZSpan.fundamentalDomain_reindex (b := sumBasis hs hp φ) _`. Rewrite using `[GT.l2, hfd, avg_fd_cube, cubeIco_eq]`. Repeatedly rewrite using `[hpt]`. Conclude with `GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hs hp`.
-/
theorem l2_canTh_eq_inv_sqrt_two_pow_mul_det_im : (torus hs hp φ hφ a b).l2 1 (fun v => canTh τ a b (φ v)) =
    (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  have hpt : ∀ x : Fin g ⊕ Fin g → ℝ,
      (torus hs hp φ hφ a b).ptN2 1 (fun v => canTh τ a b (φ v))
          ((sumBasis hs hp φ).equivFun.symm x) =
        ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))
            ((fun i => (x (.inl i) : ℂ)) + τ.mulVec (fun i => (x (.inr i) : ℂ)))‖ ^ 2 *
          Real.exp (-2 * Real.pi *
            ((fun i => x (.inr i)) ⬝ᵥ (τ.map Complex.im).mulVec (fun i => x (.inr i)))) := by
    intro x
    have hx : (sumBasis hs hp φ).equivFun.symm x = realCoord hs hp φ x := by
      simp [sumBasis, Module.Basis.map_equivFun]
    simp only [hx, GT.ptN2]
    rw [norm_sq_eq_re_Hf, hφ, apply_realCoord, Nat.cast_one, one_mul, norm_canTh_realPt hp,
      realPt_apply]
  have hfd : ZSpan.fundamentalDomain (torus hs hp φ hφ a b).b =
      ZSpan.fundamentalDomain (sumBasis hs hp φ) :=
    ZSpan.fundamentalDomain_reindex (b := sumBasis hs hp φ) _
  rw [GT.l2, hfd, avg_fd_cube, cubeIco_eq]
  simp_rw [hpt]
  exact GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hs hp

end

end GlobalTheory.CanTh
