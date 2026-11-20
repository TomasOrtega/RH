import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaFunctionCmLatticeIntegralSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaIteratedDerivZeroAlgebraicStatement

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open Formalism.L2.Th1.F (herm altE cmTheta)
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.MomN

def latOne (L : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  L.lattice.comap (LinearMap.proj 0 : (Fin 1 → ℂ) →ₗ[ℤ] ℂ)

def setupOne (d : ℕ) (L : PeriodPair) : JMB.Setup 1 := ⟨d, hOne L (Fin 1), latOne L⟩

/- English proof (translation)
Simplify using `[JMB.hf, hOne, herm, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_hOne (L : PeriodPair) (z w : Fin 1 → ℂ) : JMB.hf (hOne L (Fin 1)) z w = herm L (z 0) (w 0) := by
  simp [JMB.hf, hOne, herm, div_eq_mul_inv]
  ring

/- English proof (translation)
Simplify using `only [JMB.opU, Formalism.L2.Th1.F.opU, hf_hOne, Pi.add_apply]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opU_hOne (L : PeriodPair) (x : Fin 1 → ℂ) (F : ℂ → ℂ) (z : Fin 1 → ℂ) :
    JMB.opU (hOne L (Fin 1)) x (fun w => F (w 0)) z = Formalism.L2.Th1.F.opU L (x 0) F (z 0) := by
  simp only [JMB.opU, Formalism.L2.Th1.F.opU, hf_hOne, Pi.add_apply]
  congr 3
  ring

/- English proof (translation)
The claim follows from `Formalism.L2.Th1.F.areaPos_thm L`.
-/
theorem area_pos (L : PeriodPair) : 0 < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L

/- English proof (translation)
Simplify using `[herm, mul_comm]`.
-/
theorem herm_conj (L : PeriodPair) (x y : ℂ) : herm L y x = conj (herm L x y) := by
  simp [herm, mul_comm]

/- English proof (translation)
Simplify using `[JMB.w0, JMB.rtd, cmTheta]`.
-/
theorem rankOne_base_weight_eq_cmTheta (d : ℕ) : JMB.w0 d = cmTheta 1 d := by
  simp [JMB.w0, JMB.rtd, cmTheta]

/- English proof (translation)
Unfold `Formalism.L2.Th1.F.opU herm`. Use `fun_prop`.
-/
theorem opU_contDiff (L : PeriodPair) (s : ℂ) {F : ℂ → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s F) := by
  unfold Formalism.L2.Th1.F.opU herm
  fun_prop

/- English proof (translation)
Establish `h` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).iteratedFDeriv_comp_right hF (0 : Fin 1 → ℂ) (i := k) (by exact_mod_cast le_top)`. Establish `e : (fun z : Fin 1 → ℂ => F (z 0)) = F ∘ (ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : Fin 1 => ℂ) 0) := rfl`. Rewrite using `[e, h, iteratedDeriv_eq_iteratedFDeriv]`. Establish `e2 : (fun j => v j 0) = fun j => (v j 0) • (1 : ℂ)` using `by funext j; simp`. Simplify using `only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def]`.

Use `(iteratedFDeriv ℂ k F ((0 : Fin 1 → ℂ) 0)).map_smul_univ (fun j => v j 0) (fun _ => (1 : ℂ))` as an intermediate fact. Simplify `this` using `[smul_eq_mul]`.
-/
theorem jet_one {F : ℂ → ℂ} (hF : ContDiff ℂ ⊤ F) (k : ℕ) (v : Fin k → Fin 1 → ℂ) :
    iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => F (z 0)) 0 v = (∏ j, v j 0) * iteratedDeriv k F 0 := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).iteratedFDeriv_comp_right hF
    (0 : Fin 1 → ℂ) (i := k) (by exact_mod_cast le_top)
  have e : (fun z : Fin 1 → ℂ => F (z 0)) = F ∘ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) := rfl
  rw [e, h, iteratedDeriv_eq_iteratedFDeriv]
  have e2 : (fun j => v j 0) = fun j => (v j 0) • (1 : ℂ) := by funext j; simp
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def]
  have := (iteratedFDeriv ℂ k F ((0 : Fin 1 → ℂ) 0)).map_smul_univ (fun j => v j 0) (fun _ => (1 : ℂ))
  simpa [smul_eq_mul] using this

section Lat

variable (d : ℕ) (L : PeriodPair) (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst

/- English proof (translation)
Take `⟨k, hk⟩` from `Formalism.L2.Th1.F.altEInt L x y hx hy`. Take `⟨m, hm⟩` from `Formalism.L2.Th1.F.altEInt L _ y (hst x hx) hy`. Establish `hs : Real.sqrt d * Real.sqrt d = d` using `Real.mul_self_sqrt (Nat.cast_nonneg d)`. Establish `e : herm L (cmTheta 1 d * x) y = cmTheta 1 d * herm L x y` using `by unfold herm; ring`. Simplify using `only [altE] at hk hm`.

Rewrite `hm` using `[e, Complex.mul_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk]`. Use `⟨m - k, k, ?_⟩` and prove the remaining obligations. Rewrite using `[rankOne_base_weight_eq_cmTheta]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem beta_mem {x y : ℂ} (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) :
    ((Real.sqrt d / 2 : ℝ) : ℂ) * herm L x y ∈ JMB.OK d := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L x y hx hy
  obtain ⟨m, hm⟩ := Formalism.L2.Th1.F.altEInt L _ y (hst x hx) hy
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have e : herm L (cmTheta 1 d * x) y = cmTheta 1 d * herm L x y := by unfold herm; ring
  simp only [altE] at hk hm
  rw [e, Complex.mul_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk] at hm
  refine ⟨m - k, k, ?_⟩
  rw [rankOne_base_weight_eq_cmTheta]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re,
      Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im]
    push_cast
    linarith
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_im,
      Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk]
    push_cast
    ring

/- English proof (translation)
Use `⟨hp, h16, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h : hOne L (Fin 1) = Matrix.diagonal fun _ => (((Formalism.L2.Th1.F.area L : ℝ) : ℂ))⁻¹`. Use extensionality with `i j`. Simplify using `[hOne, Matrix.one_apply, Matrix.diagonal_apply]`. Use `show (hOne L (Fin 1)).PosDef`.

Rewrite using `[h, Matrix.posDef_diagonal_iff]`. Introduce `_`. Use `area_pos L` as an intermediate fact. Rewrite using `[← Complex.ofReal_inv]`. Conclude with `inv_pos.2 this` after adjusting the coercions.

Establish `hi : Function.Injective (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice))`. Introduce `a b hab`. Use extensionality with `i`. Establish `: i = 0` using `Subsingleton.elim _ _`. Substitute `this` using the available equality.

Conclude with `congrArg (fun w : L.lattice => (w : ℂ)) hab`. Establish `hc : Continuous (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice))` using `Continuous.subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _`. Conclude with `DiscreteTopology.of_continuous_injective hc hi`. Establish `htop : Submodule.span ℝ (L.lattice : Set ℂ) = ⊤` using `IsZLattice.span_top`. Set `c : ℂ →ₗ[ℝ] (Fin 1 → ℂ)` to `LinearMap.pi fun _ => LinearMap.id`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `hv : v = c (v 0)`. Use function extensionality and compare the values at `i`. Establish `: i = 0` using `Subsingleton.elim _ _`.

Substitute `this` using the available equality. Both sides reduce to the same expression. Establish `h0 : v 0 ∈ Submodule.span ℝ (L.lattice : Set ℂ)` using `by rw [htop]; trivial`. Establish `hmap : (Submodule.span ℝ (L.lattice : Set ℂ)).map c ≤ Submodule.span ℝ ((setupOne d L).La : Set (Fin 1 → ℂ))`. Rewrite using `[Submodule.map_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `Submodule.subset_span hw`. Rewrite using `[hv]`. Conclude with `hmap (Submodule.mem_map_of_mem h0)`. Introduce `x hx show (JMB.w0 d • x) 0 ∈ L.lattice`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, rankOne_base_weight_eq_cmTheta]`. Conclude with `hst _ hx`. Introduce `x hx y hy show ((Real.sqrt d / 2 : ℝ) : ℂ) * JMB.hf (hOne L (Fin 1)) x y ∈ JMB.OK d`. Rewrite using `[hf_hOne]`. Conclude with `beta_mem d L hst hx hy`.

Introduce `y hy`. Establish `key : ∀ w ∈ L.lattice, ∃ m : ℤ, altE L (y 0) w = (m : ℝ)`. Introduce `w hw`. Take `⟨k, hk⟩` from `hy (fun _ => w) hw`. Use `⟨-k, ?_⟩` and prove the remaining obligations.

Establish `e : JMB.hf (setupOne d L).Hm (fun _ => w) y = herm L w (y 0)` using `hf_hOne L _ _`. Rewrite `hk` using `[e]`. Simplify using `only [altE]`. Rewrite using `[herm_conj L w (y 0), Complex.conj_im, hk]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Formalism.L2.Th1.H.mem_lattice_of_dual L _ (key _ L.ω₁_mem_lattice) (key _ L.ω₂_mem_lattice)`.
-/
theorem setupOne_ok (hp : d.Prime) (h16 : d % 16 = 7) : (setupOne d L).Ok := by
  refine ⟨hp, h16, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : hOne L (Fin 1) = Matrix.diagonal fun _ => (((Formalism.L2.Th1.F.area L : ℝ) : ℂ))⁻¹ := by
      ext i j
      simp [hOne, Matrix.one_apply, Matrix.diagonal_apply]
    show (hOne L (Fin 1)).PosDef
    rw [h, Matrix.posDef_diagonal_iff]
    intro _
    have := area_pos L
    rw [← Complex.ofReal_inv]
    exact_mod_cast inv_pos.2 this
  · have hi : Function.Injective (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice)) := by
      intro a b hab
      ext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      exact congrArg (fun w : L.lattice => (w : ℂ)) hab
    have hc : Continuous (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice)) :=
      Continuous.subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _
    exact DiscreteTopology.of_continuous_injective hc hi
  · have htop : Submodule.span ℝ (L.lattice : Set ℂ) = ⊤ := IsZLattice.span_top
    let c : ℂ →ₗ[ℝ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.id
    rw [eq_top_iff]
    intro v _
    have hv : v = c (v 0) := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
    have h0 : v 0 ∈ Submodule.span ℝ (L.lattice : Set ℂ) := by rw [htop]; trivial
    have hmap : (Submodule.span ℝ (L.lattice : Set ℂ)).map c ≤ Submodule.span ℝ ((setupOne d L).La : Set (Fin 1 → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      exact Submodule.subset_span hw
    rw [hv]
    exact hmap (Submodule.mem_map_of_mem h0)
  · intro x hx
    show (JMB.w0 d • x) 0 ∈ L.lattice
    rw [Pi.smul_apply, smul_eq_mul, rankOne_base_weight_eq_cmTheta]
    exact hst _ hx
  · intro x hx y hy
    show ((Real.sqrt d / 2 : ℝ) : ℂ) * JMB.hf (hOne L (Fin 1)) x y ∈ JMB.OK d
    rw [hf_hOne]
    exact beta_mem d L hst hx hy
  · intro y hy
    have key : ∀ w ∈ L.lattice, ∃ m : ℤ, altE L (y 0) w = (m : ℝ) := by
      intro w hw
      obtain ⟨k, hk⟩ := hy (fun _ => w) hw
      refine ⟨-k, ?_⟩
      have e : JMB.hf (setupOne d L).Hm (fun _ => w) y = herm L w (y 0) := hf_hOne L _ _
      rw [e] at hk
      simp only [altE]
      rw [herm_conj L w (y 0), Complex.conj_im, hk]
      push_cast; ring
    exact Formalism.L2.Th1.H.mem_lattice_of_dual L _ (key _ L.ω₁_mem_lattice) (key _ L.ω₂_mem_lattice)

end Lat

/- English proof (translation)
Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `IsAlgebraic.algHom D.host.φ₀.toRatAlgHom (Algebra.IsAlgebraic.isAlgebraic x)`.
-/
theorem mem_Qbar_phi (D : D7) (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact IsAlgebraic.algHom D.host.φ₀.toRatAlgHom (Algebra.IsAlgebraic.isAlgebraic x)

section Main

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

/- English proof (translation)
The claim follows from `(Formalism.L2.Th1.F.th0Basic B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B)).1.contDiff`.
-/
theorem contDiff_base_even_theta_kernel : ContDiff ℂ ⊤ B.th0 :=
  (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B)).1.contDiff

def eOne (_B : Base D cc δ) : (Fin 1 → ℂ) → ℂ := fun z => _B.th0 (z 0)

/- English proof (translation)
Use `⟨(contDiff_base_even_theta_kernel B).comp (by fun_prop), fun x hx => ?_⟩` and prove the remaining obligations. Establish `h8 : D.host.d % 8 = 7` using `by have := D.host.hyp.2.2.2.1; omega`. Establish `hc` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (GlobalTheory.FourthRootStd.hst B) (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.hθ B) (GlobalTheory.FourthRootStd.hθ' B) h8 (x 0) hx`. Use function extensionality and compare the values at `z`. Establish `hfix` using `Formalism.L2.Th1.H.th0Char_mul_opU_th0_half_period_eq B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B) (x 0) hx (z 0)`.

Rewrite `hfix` using `[← hc]`. Establish `hU : JMB.opU (setupOne D.host.d B.L).Hm x (eOne B) z = Formalism.L2.Th1.F.opU B.L (x 0) B.th0 (z 0)` using `opU_hOne B.L x B.th0 z`. Establish `hb : (JMB.beta (setupOne D.host.d B.L).d (setupOne D.host.d B.L).Hm x x).re = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (x 0)`. Establish `: JMB.hf (setupOne D.host.d B.L).Hm x x = herm B.L (x 0) (x 0)` using `hf_hOne B.L x x`. Rewrite using `[JMB.beta, this, Complex.re_ofReal_mul]`.

Both sides reduce to the same expression. Simplify using `only [JMB.opW]`. Rewrite using `[hU, hb]`. Conclude with `hfix`.
-/
theorem eOne_theta : (setupOne D.host.d B.L).IsTheta (eOne B) := by
  refine ⟨(contDiff_base_even_theta_kernel B).comp (by fun_prop), fun x hx => ?_⟩
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  have hc := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (GlobalTheory.FourthRootStd.hst B) (GlobalTheory.FourthRootStd.omega_mem B)
    (GlobalTheory.FourthRootStd.hθ B) (GlobalTheory.FourthRootStd.hθ' B) h8 (x 0) hx
  funext z
  have hfix := Formalism.L2.Th1.H.th0Char_mul_opU_th0_half_period_eq B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B) (x 0) hx (z 0)
  rw [← hc] at hfix
  have hU : JMB.opU (setupOne D.host.d B.L).Hm x (eOne B) z = Formalism.L2.Th1.F.opU B.L (x 0) B.th0 (z 0) :=
    opU_hOne B.L x B.th0 z
  have hb : (JMB.beta (setupOne D.host.d B.L).d (setupOne D.host.d B.L).Hm x x).re = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (x 0) := by
    have : JMB.hf (setupOne D.host.d B.L).Hm x x = herm B.L (x 0) (x 0) := hf_hOne B.L x x
    rw [JMB.beta, this, Complex.re_ofReal_mul]
    rfl
  simp only [JMB.opW]
  rw [hU, hb]
  exact hfix

/- English proof (translation)
Introduce `k ys hy`. Establish `hcc : cc ≠ ⊥` using `hc.1`. Establish `hdir : ∀ j, δ₀⁻¹ * ys j 0 ∈ Qbar`. Introduce `j`. Take `⟨s, hs, hmem⟩` from `hy j`.

Establish `h1 : (s : ℂ) * ys j 0 ∈ lamOf D cc δ`. Use `(GlobalTheory.FourthRootStd.mem_iff B _).1 hmem` as an intermediate fact. Simplify using `using this`. Take `⟨x, -, hx⟩` from `((GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D).2.2.2.2 cc δ hcc).2 _ |>.1 h1`. Establish `hs0 : (s : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`.

Establish `e : δ₀⁻¹ * ys j 0 = (δ / δ₀) * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹`. Establish `: ys j 0 = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_comm]`. Conclude with `hx`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem h0 (mem_Qbar_phi D _)) (inv_mem (natCast_mem _ s))`. Establish `hj` using `jet_one (contDiff_base_even_theta_kernel B) k (fun j => δ₀⁻¹ • ys j)`.

Use `show iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => B.th0 (z 0)) 0 (fun j => δ₀⁻¹ • ys j) ∈ Qbar`. Rewrite using `[hj]`. Use `mul_mem (prod_mem fun j _ => ?_) (GlobalTheory.T.iteratedDeriv_th0_zero_mem_Qbar D cc δ B hc hδ k)` and prove the remaining obligations. Simplify using `using hdir j`.
-/
theorem eOne_algJets (hc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {δ₀ : ℂ} (h0 : δ / δ₀ ∈ Qbar) :
    (setupOne D.host.d B.L).AlgJets δ₀ (eOne B) := by
  intro k ys hy
  have hcc : cc ≠ ⊥ := hc.1
  have hdir : ∀ j, δ₀⁻¹ * ys j 0 ∈ Qbar := by
    intro j
    obtain ⟨s, hs, hmem⟩ := hy j
    have h1 : (s : ℂ) * ys j 0 ∈ lamOf D cc δ := by
      have := (GlobalTheory.FourthRootStd.mem_iff B _).1 hmem
      simpa using this
    obtain ⟨x, -, hx⟩ := ((GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D).2.2.2.2 cc δ hcc).2 _ |>.1 h1
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : δ₀⁻¹ * ys j 0 = (δ / δ₀) * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹ := by
      have : ys j 0 = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹ := by
        field_simp
        rw [mul_comm]; exact hx
      rw [this]; ring
    rw [e]
    exact mul_mem (mul_mem h0 (mem_Qbar_phi D _)) (inv_mem (natCast_mem _ s))
  have hj := jet_one (contDiff_base_even_theta_kernel B) k (fun j => δ₀⁻¹ • ys j)
  show iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => B.th0 (z 0)) 0 (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [hj]
  refine mul_mem (prod_mem fun j _ => ?_) (GlobalTheory.T.iteratedDeriv_th0_zero_mem_Qbar D cc δ B hc hδ k)
  simpa using hdir j

end Main

/- English proof (translation)
Introduce `D cc δ B hc hδ q _ hq2 hj hcop ι δ₀ θ Ω hPer s n hn hs`. Take `⟨hp, h16, -⟩` from `GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D`. Establish `hOk : (setupOne D.host.d B.L).Ok` using `setupOne_ok D.host.d B.L (GlobalTheory.FourthRootStd.hst B) hp h16`. Establish `hd0 : δ / δ₀ ∈ Qbar` using `(GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hc hδ hPer.2.1 q hq2 hcop).1`. Establish `hnpos : 0 < n`.

Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. Substitute `h` using the available equality. Establish `: q = 1` using `by simpa using hn`. Conclude with `absurd this (Fact.out : q.Prime).one_lt.ne'`. Conclude with `h`.

Establish `hprime : (setupOne D.host.d B.L).PrimeTo q (fun _ => s)` using `⟨n, hnpos, hn, hs⟩`. Set `p0 : (Fin 1 → ℂ) →L[ℂ] ℂ` to `ContinuousLinearMap.proj 0`. Set `c0 : ℂ →L[ℂ] (Fin 1 → ℂ)` to `ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ`. Establish `hLat : LatInt ι (Ω / ι δ₀) (setupOne D.host.d B.L).La.toAddSubgroup (eOne B)` using `GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 1 → ℂ) _ (lamOf D cc δ) _ p0 B.th0 (contDiff_base_even_theta_kernel B) (fun x hx => ⟨1, Nat.coprime_one_left q, by`. Rewrite using `[one_smul]`.

Conclude with `(GlobalTheory.FourthRootStd.mem_iff B _).1 hx⟩)`. Use the proof step `(GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime D cc δ B hc hδ q hq2 hj hcop ι δ₀ θ Ω hPer)`. Establish `hres` using `GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality q ι δ₀ θ Ω 1 (setupOne D.host.d B.L) (eOne B) (fun _ => s) hPer hOk (Or.inr ⟨hq2, hj⟩) (eOne_theta B) (eOne_algJets B hc hδ hd0) hprime hLat`. Establish `hU : JMB.opU (setupOne D.host.d B.L).Hm (fun _ => s) (eOne B) = fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0)`. Use function extensionality and compare the values at `z`.

Conclude with `opU_hOne B.L _ B.th0 z`. Rewrite `hres` using `[hU]`. Establish `hcd : ContDiff ℂ ⊤ (fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0))` using `(opU_contDiff B.L s (contDiff_base_even_theta_kernel B)).comp (by fun_prop)`. Conclude with `GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (Fin 1 → ℂ) ℂ _ _ (lamOf D cc δ) c0 _ hcd (fun x hx => ⟨1, Nat.coprime_one_left q, by`. Rewrite using `[one_smul]`.

Use `show x ∈ B.L.lattice`. Conclude with `(GlobalTheory.FourthRootStd.mem_iff B _).2 hx⟩) hres`.
-/
theorem latInt_opU_of_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q →
    ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (s : ℂ) (n : ℕ), Nat.Coprime n q →
    (n : ℂ) * s ∈ B.L.lattice → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) (Formalism.L2.Th1.F.opU B.L s B.th0) := by
  intro D cc δ B hc hδ q _ hq2 hj hcop ι δ₀ θ Ω hPer s n hn hs
  obtain ⟨hp, h16, -⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  have hOk : (setupOne D.host.d B.L).Ok := setupOne_ok D.host.d B.L (GlobalTheory.FourthRootStd.hst B) hp h16
  have hd0 : δ / δ₀ ∈ Qbar := (GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hc hδ hPer.2.1 q hq2 hcop).1
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : q = 1 := by simpa using hn
      exact absurd this (Fact.out : q.Prime).one_lt.ne'
    · exact h
  have hprime : (setupOne D.host.d B.L).PrimeTo q (fun _ => s) := ⟨n, hnpos, hn, hs⟩
  let p0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let c0 : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
  have hLat : LatInt ι (Ω / ι δ₀) (setupOne D.host.d B.L).La.toAddSubgroup (eOne B) :=
    GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 1 → ℂ) _ (lamOf D cc δ) _ p0 B.th0 (contDiff_base_even_theta_kernel B)
      (fun x hx => ⟨1, Nat.coprime_one_left q, by
        rw [one_smul]; exact (GlobalTheory.FourthRootStd.mem_iff B _).1 hx⟩)
      (GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime D cc δ B hc hδ q hq2 hj hcop ι δ₀ θ Ω hPer)
  have hres := GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality q ι δ₀ θ Ω 1 (setupOne D.host.d B.L) (eOne B) (fun _ => s) hPer hOk
    (Or.inr ⟨hq2, hj⟩) (eOne_theta B) (eOne_algJets B hc hδ hd0) hprime hLat
  have hU : JMB.opU (setupOne D.host.d B.L).Hm (fun _ => s) (eOne B)
      = fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0) := by
    funext z; exact opU_hOne B.L _ B.th0 z
  rw [hU] at hres
  have hcd : ContDiff ℂ ⊤ (fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0)) :=
    (opU_contDiff B.L s (contDiff_base_even_theta_kernel B)).comp (by fun_prop)
  exact GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (Fin 1 → ℂ) ℂ _ _ (lamOf D cc δ) c0 _ hcd
    (fun x hx => ⟨1, Nat.coprime_one_left q, by
      rw [one_smul]
      show x ∈ B.L.lattice
      exact (GlobalTheory.FourthRootStd.mem_iff B _).2 hx⟩) hres

end GlobalTheory.MomN
