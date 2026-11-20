import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussiansStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiagStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDefStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ β hβ T hadd h0 hunit A hAc hAadd hA0 hint hcont J₀ hJ₀ f₀ hf₀`. Distinguish the cases in `hz : f₀ = 0`. Substitute `hz` using the available equality. Establish `hT0 : ∀ t, T t 0 = 0` using `fun t => map_zero _`. Use `⟨?_, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, fun x => ?_⟩` and prove the remaining obligations.

Simplify using `only [hT0, SchwartzMap.zero_apply]`. Conclude with `contDiff_const`. Simplify using `only [hT0, SchwartzMap.zero_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, add_zero]`. Conclude with `hasDerivAt_const _ _`. Establish `hAsm` using `GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear A hAc hAadd hA0`.

Establish `hinv : ∀ t w, A t (A (-t) w) = w`. Introduce `t w`. Use `congrArg (fun L => L w) (hAadd t (-t))` as an intermediate fact. Simplify using `only [add_neg_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this`. Conclude with `this.symm`.

Establish `hinv' : ∀ t w, A (-t) (A t w) = w`. Introduce `t w`. Use `congrArg (fun L => L w) (hAadd (-t) t)` as an intermediate fact. Simplify using `only [neg_add_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this`. Conclude with `this.symm`.

Use `set J : ℝ → (V × V) →ₗ[ℝ] (V × V) := fun t => (A t).comp (J₀.comp (A (-t))) with hJdef`. Establish `hJapp : ∀ t w, J t w = A t (J₀ (A (-t) w))` using `fun t w => rfl`. Establish `hJsm : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w`. Introduce `w`. Establish `e : (fun t => J t w) = fun t => (LinearMap.toContinuousLinearMap (A t)) ((LinearMap.toContinuousLinearMap J₀) ((LinearMap.toContinuousLinearMap (A (-t))) w))`.

Use function extensionality and compare the values at `t`. Simplify using `[hJapp]`. Rewrite using `[e]`. Conclude with `hAsm.clm_apply ((LinearMap.toContinuousLinearMap J₀).contDiff.comp ((hAsm.comp contDiff_neg).clm_apply contDiff_const))`. Establish `hJsq : ∀ t w, J t (J t w) = -w`.

Introduce `t w`. Simplify using `only [hJapp, hinv', hJ₀, map_neg, hinv]`. Establish `hFock : ∀ t w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑(T t f₀) x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑(T t f₀) x`. Introduce `t w x`. Use `set u := A (-t) w`.

Take `⟨g1, hg1⟩` from `GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β (J₀ u) f₀`. Take `⟨g2, hg2⟩` from `GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β u f₀`. Establish `hg12 : g1 = Complex.I • g2`. Use extensionality with `y`. Rewrite using `[SchwartzMap.smul_apply, hg1, hg2, hf₀, smul_eq_mul]`.

Establish `hI : ∀ w₁ : V × V, ∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w₁).1 (s • w₁).2 ⇑f → ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (s • A t w₁).1 (s • A t w₁).2 ⇑(T t f)`. Introduce `w₁ s f g h`. Use `hint t (s • w₁).1 (s • w₁).2 f g h` as an intermediate fact. Rewrite `this` using `[Prod.mk.eta, map_smul]`. Then use the resulting hypothesis. Apply the tactic sequence `have h1 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) (J₀ u) (A t (J₀ u)) (hI _) f₀ g1 hg1 x`.

Apply the tactic sequence `have h2 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) u (A t u) (hI _) f₀ g2 hg2 x`. Establish `hu : A t u = w` using `hinv t w`. Rewrite `h2` using `[hu]`. Rewrite using `[hJapp, ← h1, ← h2, hg12, map_smul, SchwartzMap.smul_apply, smul_eq_mul]`. Establish `hne : ∀ t, T t f₀ ≠ 0`.

Introduce `t h`. Apply `hz` to reduce the goal to its premises. Use `hadd (-t) t f₀` as an intermediate fact. Rewrite `this` using `[neg_add_cancel, h0, h, map_zero]`. Conclude with `this`.

Take `⟨M, hMs, hMj, hMdec, hMuniq, n, qs, qs', cs, hMder⟩` from `GlobalTheory.T.fockVacua_smooth_family_complexGaussians β hβ J hJsm hJsq (fun t => ⟨T t f₀, hne t, hFock t⟩)`. Use `set cc : ℝ → ℂ := fun t => T t f₀ 0 with hccdef`. Establish `hrep : ∀ t x, T t f₀ x = cc t * Complex.exp (M t x x)` using `fun t x => hMuniq t (T t f₀) (hFock t) x`. Take `⟨hK, hKne⟩` from `GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag μ M hMs hMdec`. Use `set K : ℝ → ℝ → ℂ := fun u v => ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M v x x)) ∂μ with hKdef`.

Establish `hexp : ∀ u v, ∫ x, T u f₀ x * starRingEnd ℂ (T v f₀ x) ∂μ = cc u * starRingEnd ℂ (cc v) * K u v`. Introduce `u v`. Repeatedly rewrite using `[hrep, map_mul]`. Rewrite using `[hKdef, ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Establish `hpol` using `fun s => GlobalTheory.T.schwartz_isometry_inner_product_eq μ (T s) (hunit s)`. Establish `eq1 : ∀ s t, cc (s + t) * starRingEnd ℂ (cc s) * K (s + t) s = cc t * starRingEnd ℂ (cc 0) * K t 0`. Introduce `s t`.

Use `hpol s (T t f₀) (T 0 f₀)` as an intermediate fact. Rewrite `this` using `[← hadd, ← hadd, add_zero]`. Rewrite using `[← hexp, ← hexp, this]`. Establish `eq2 : ∀ s, cc s * starRingEnd ℂ (cc s) * K s s = cc 0 * starRingEnd ℂ (cc 0) * K 0 0`. Introduce `s`.

Use `hpol s f₀ f₀` as an intermediate fact. Rewrite using `[← hexp, ← hexp, this, h0]`. Establish `hc0 : cc 0 ≠ 0`. Introduce `h`. Apply `hz` to reduce the goal to its premises.

Use extensionality with `x`. Rewrite using `[← h0 f₀, hrep, h, zero_mul, SchwartzMap.zero_apply]`. Establish `hcs : ∀ s, cc s ≠ 0`. Introduce `s h`. Use `eq2 s` as an intermediate fact.

Rewrite `this` using `[h, zero_mul, zero_mul]`. Conclude with `mul_ne_zero (mul_ne_zero hc0 ((map_ne_zero _).2 hc0)) (hKne 0) this.symm`. Establish `hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2` using `hK.continuous`. Use `set U : Set (ℝ × ℝ) := {p | K (p.1 + p.2) p.1 ≠ 0} with hUdef`. Establish `hUo : IsOpen U` using `isOpen_ne_fun (hKc.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)) continuous_const`.

Establish `hU0 : ∀ s, (s, 0) ∈ U` using `by intro s; simp only [hUdef, Set.mem_setOf_eq, add_zero]; exact hKne s`. Use `set E : ℝ → ℝ → ℂ := fun s t => K s s * K t 0 / (cc 0 * K 0 0 * K (s + t) s) with hEdef`. Establish `hEsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U`. Establish `k1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.1 p.1)` using `hK.comp (contDiff_fst.prodMk contDiff_fst)`. Establish `k2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.2 0)` using `hK.comp (contDiff_snd.prodMk contDiff_const)`.

Establish `k3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K (p.1 + p.2) p.1)` using `hK.comp ((contDiff_fst.add contDiff_snd).prodMk contDiff_fst)`. Establish `hinvd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (cc 0 * K 0 0 * K (p.1 + p.2) p.1)⁻¹) U` using `((contDiff_const.mul k3).contDiffOn).inv (fun p hp => mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)`. Use `(k1.mul k2).contDiffOn.mul hinvd` as an intermediate fact. Simplify `this` using `only [hEdef, div_eq_mul_inv]`. Establish `hfe : ∀ p ∈ U, cc (p.1 + p.2) = cc p.1 * cc p.2 * E p.1 p.2`.

Introduce and unpack `⟨s, t⟩ hp`. Simplify using `only [hUdef, Set.mem_setOf_eq] at hp`. Simplify using `only [hEdef]`. Establish `hd : starRingEnd ℂ (cc 0) ≠ 0` using `(map_ne_zero _).2 hc0`. Rewrite using `[mul_div_assoc', eq_div_iff (mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)]`.

Apply `mul_left_cancel₀ hd` to reduce the goal to its premises. Take the linear combination `(-(cc (s + t) * K (s + t) s)) * eq2 s + (cc s * K s s) * eq1 s t`. Establish `hccc : Continuous cc`. Use `hcont f₀ 0` as an intermediate fact. Conclude with `this`.

Establish `hcsm` using `GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect cc E U hccc hc0 hUo hU0 hEsm hfe`. Establish `hfun : (fun p : ℝ × V => T p.1 f₀ p.2) = fun p => cc p.1 * Complex.exp (M p.1 p.2 p.2)`. Use function extensionality and compare the values at `p`. Conclude with `hrep p.1 p.2`. Use `⟨?_, n, qs, qs', cs, deriv cc 0 / cc 0, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hfun]`. Conclude with `(hcsm.comp contDiff_fst).mul hMj.cexp`. Establish `hft : (fun t => T t f₀ x) = fun t => cc t * Complex.exp (M t x x)` using `by funext t; exact hrep t x`. Rewrite using `[hft]`. Establish `hdc : HasDerivAt cc (deriv cc 0) 0` using `((hcsm.differentiable (by simp)) 0).hasDerivAt`.

Use `(hdc.mul (hMder x).cexp).congr_deriv ?_` and prove the remaining obligations. Establish `hf0x : f₀ x = cc 0 * Complex.exp (M 0 x x)` using `by rw [← hrep 0 x, h0]`. Rewrite using `[hf0x, ← Finset.sum_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.WeilVacuum.smooth_flow : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  intro V _ _ _ _ _ μ _ β hβ T hadd h0 hunit A hAc hAadd hA0 hint hcont J₀ hJ₀ f₀ hf₀
  by_cases hz : f₀ = 0
  · subst hz
    have hT0 : ∀ t, T t 0 = 0 := fun t => map_zero _
    refine ⟨?_, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, fun x => ?_⟩
    · simp only [hT0, SchwartzMap.zero_apply]; exact contDiff_const
    · simp only [hT0, SchwartzMap.zero_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, add_zero]
      exact hasDerivAt_const _ _
  have hAsm := GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear A hAc hAadd hA0
  have hinv : ∀ t w, A t (A (-t) w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd t (-t))
    simp only [add_neg_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  have hinv' : ∀ t w, A (-t) (A t w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd (-t) t)
    simp only [neg_add_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  set J : ℝ → (V × V) →ₗ[ℝ] (V × V) := fun t => (A t).comp (J₀.comp (A (-t))) with hJdef
  have hJapp : ∀ t w, J t w = A t (J₀ (A (-t) w)) := fun t w => rfl
  have hJsm : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w := by
    intro w
    have e : (fun t => J t w) = fun t => (LinearMap.toContinuousLinearMap (A t))
        ((LinearMap.toContinuousLinearMap J₀) ((LinearMap.toContinuousLinearMap (A (-t))) w)) := by
      funext t; simp [hJapp]
    rw [e]
    exact hAsm.clm_apply ((LinearMap.toContinuousLinearMap J₀).contDiff.comp
      ((hAsm.comp contDiff_neg).clm_apply contDiff_const))
  have hJsq : ∀ t w, J t (J t w) = -w := by
    intro t w; simp only [hJapp, hinv', hJ₀, map_neg, hinv]
  have hFock : ∀ t w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑(T t f₀) x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑(T t f₀) x := by
    intro t w x
    set u := A (-t) w
    obtain ⟨g1, hg1⟩ := GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β (J₀ u) f₀
    obtain ⟨g2, hg2⟩ := GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β u f₀
    have hg12 : g1 = Complex.I • g2 := by
      ext y; rw [SchwartzMap.smul_apply, hg1, hg2, hf₀, smul_eq_mul]
    have hI : ∀ w₁ : V × V, ∀ (s : ℝ) (f g : SchwartzMap V ℂ),
        ⇑g = GlobalTheory.GaussLine.heisFun β (s • w₁).1 (s • w₁).2 ⇑f →
        ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (s • A t w₁).1 (s • A t w₁).2 ⇑(T t f) := by
      intro w₁ s f g h
      have := hint t (s • w₁).1 (s • w₁).2 f g h
      rwa [Prod.mk.eta, map_smul] at this
    have h1 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) (J₀ u) (A t (J₀ u)) (hI _) f₀ g1 hg1 x
    have h2 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) u (A t u) (hI _) f₀ g2 hg2 x
    have hu : A t u = w := hinv t w
    rw [hu] at h2
    rw [hJapp, ← h1, ← h2, hg12, map_smul, SchwartzMap.smul_apply, smul_eq_mul]
  have hne : ∀ t, T t f₀ ≠ 0 := by
    intro t h
    apply hz
    have := hadd (-t) t f₀
    rw [neg_add_cancel, h0, h, map_zero] at this
    exact this
  obtain ⟨M, hMs, hMj, hMdec, hMuniq, n, qs, qs', cs, hMder⟩ :=
    GlobalTheory.T.fockVacua_smooth_family_complexGaussians β hβ J hJsm hJsq (fun t => ⟨T t f₀, hne t, hFock t⟩)
  set cc : ℝ → ℂ := fun t => T t f₀ 0 with hccdef
  have hrep : ∀ t x, T t f₀ x = cc t * Complex.exp (M t x x) := fun t x => hMuniq t (T t f₀) (hFock t) x
  obtain ⟨hK, hKne⟩ := GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag μ M hMs hMdec
  set K : ℝ → ℝ → ℂ := fun u v => ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M v x x)) ∂μ with hKdef
  have hexp : ∀ u v, ∫ x, T u f₀ x * starRingEnd ℂ (T v f₀ x) ∂μ = cc u * starRingEnd ℂ (cc v) * K u v := by
    intro u v
    simp_rw [hrep, map_mul]
    rw [hKdef, ← integral_const_mul]
    congr 1; funext x; ring
  have hpol := fun s => GlobalTheory.T.schwartz_isometry_inner_product_eq μ (T s) (hunit s)
  have eq1 : ∀ s t, cc (s + t) * starRingEnd ℂ (cc s) * K (s + t) s = cc t * starRingEnd ℂ (cc 0) * K t 0 := by
    intro s t
    have := hpol s (T t f₀) (T 0 f₀)
    rw [← hadd, ← hadd, add_zero] at this
    rw [← hexp, ← hexp, this]
  have eq2 : ∀ s, cc s * starRingEnd ℂ (cc s) * K s s = cc 0 * starRingEnd ℂ (cc 0) * K 0 0 := by
    intro s
    have := hpol s f₀ f₀
    rw [← hexp, ← hexp, this, h0]
  have hc0 : cc 0 ≠ 0 := by
    intro h; apply hz; ext x
    rw [← h0 f₀, hrep, h, zero_mul, SchwartzMap.zero_apply]
  have hcs : ∀ s, cc s ≠ 0 := by
    intro s h
    have := eq2 s
    rw [h, zero_mul, zero_mul] at this
    exact mul_ne_zero (mul_ne_zero hc0 ((map_ne_zero _).2 hc0)) (hKne 0) this.symm
  have hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2 := hK.continuous
  set U : Set (ℝ × ℝ) := {p | K (p.1 + p.2) p.1 ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun (hKc.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)) continuous_const
  have hU0 : ∀ s, (s, 0) ∈ U := by intro s; simp only [hUdef, Set.mem_setOf_eq, add_zero]; exact hKne s
  set E : ℝ → ℝ → ℂ := fun s t => K s s * K t 0 / (cc 0 * K 0 0 * K (s + t) s) with hEdef
  have hEsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U := by
    have k1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.1 p.1) := hK.comp (contDiff_fst.prodMk contDiff_fst)
    have k2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.2 0) := hK.comp (contDiff_snd.prodMk contDiff_const)
    have k3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K (p.1 + p.2) p.1) :=
      hK.comp ((contDiff_fst.add contDiff_snd).prodMk contDiff_fst)
    have hinvd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (cc 0 * K 0 0 * K (p.1 + p.2) p.1)⁻¹) U :=
      ((contDiff_const.mul k3).contDiffOn).inv (fun p hp => mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)
    have := (k1.mul k2).contDiffOn.mul hinvd
    simpa only [hEdef, div_eq_mul_inv] using this
  have hfe : ∀ p ∈ U, cc (p.1 + p.2) = cc p.1 * cc p.2 * E p.1 p.2 := by
    rintro ⟨s, t⟩ hp
    simp only [hUdef, Set.mem_setOf_eq] at hp
    simp only [hEdef]
    have hd : starRingEnd ℂ (cc 0) ≠ 0 := (map_ne_zero _).2 hc0
    rw [mul_div_assoc', eq_div_iff (mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)]
    apply mul_left_cancel₀ hd
    linear_combination (-(cc (s + t) * K (s + t) s)) * eq2 s + (cc s * K s s) * eq1 s t
  have hccc : Continuous cc := by
    have := hcont f₀ 0
    exact this
  have hcsm := GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect cc E U hccc hc0 hUo hU0 hEsm hfe
  have hfun : (fun p : ℝ × V => T p.1 f₀ p.2) = fun p => cc p.1 * Complex.exp (M p.1 p.2 p.2) := by
    funext p; exact hrep p.1 p.2
  refine ⟨?_, n, qs, qs', cs, deriv cc 0 / cc 0, fun x => ?_⟩
  · rw [hfun]; exact (hcsm.comp contDiff_fst).mul hMj.cexp
  · have hft : (fun t => T t f₀ x) = fun t => cc t * Complex.exp (M t x x) := by funext t; exact hrep t x
    rw [hft]
    have hdc : HasDerivAt cc (deriv cc 0) 0 := ((hcsm.differentiable (by simp)) 0).hasDerivAt
    refine (hdc.mul (hMder x).cexp).congr_deriv ?_
    have hf0x : f₀ x = cc 0 * Complex.exp (M 0 x x) := by rw [← hrep 0 x, h0]
    rw [hf0x, ← Finset.sum_mul]
    field_simp
    ring

end
