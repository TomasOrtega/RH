import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.UnipLog

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
Use `hU.is_const_of_fderiv_eq_zero hc hf (fun z hz => ?_) hx hy` and prove the remaining obligations. Establish `hd : HasFDerivAt f (fderiv ℂ f z) z` using `(hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt`. Establish `h1 : HasFDerivAt (fun w => (f w).re) (Complex.reCLM.comp ((fderiv ℂ f z).restrictScalars ℝ)) z` using `Complex.reCLM.hasFDerivAt.comp z (hd.restrictScalars ℝ)`. Establish `h2 : HasFDerivAt (fun w => (f w).re) (0 : Frame Ψ N →L[ℝ] ℝ) z`. Establish `: (fun w => (f w).re) =ᶠ[𝓝 z] fun _ => (0 : ℝ)` using `by filter_upwards [hU.mem_nhds hz] with w hw using hre w hw`.

Conclude with `(hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq this`. Establish `h3` using `h1.unique h2`. Use `show fderiv ℂ f z = 0`. Use extensionality with `v`. Establish `hv : (fderiv ℂ f z v).re = 0`.

Use `congrArg (fun L : Frame Ψ N →L[ℝ] ℝ => L v) h3` as an intermediate fact. Simplify using `using this`. Establish `hiv : (fderiv ℂ f z (Complex.I • v)).re = 0`. Use `congrArg (fun L : Frame Ψ N →L[ℝ] ℝ => L (Complex.I • v)) h3` as an intermediate fact. Simplify using `using this`.

Rewrite `hiv` using `[map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im]`. Apply the tactic sequence `apply Complex.ext <;> simp only [ContinuousLinearMap.zero_apply, Complex.zero_re, Complex.zero_im]`. Conclude with `hv`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_of_re_eq_zero {Ψ : Finset (E →+* ℂ)} {U : Set (Frame Ψ N)} (hU : IsOpen U)
    (hc : IsPreconnected U) {f : Frame Ψ N → ℂ} (hf : DifferentiableOn ℂ f U)
    (hre : ∀ x ∈ U, (f x).re = 0) {x y : Frame Ψ N} (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  refine hU.is_const_of_fderiv_eq_zero hc hf (fun z hz => ?_) hx hy
  have hd : HasFDerivAt f (fderiv ℂ f z) z := (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have h1 : HasFDerivAt (fun w => (f w).re)
      (Complex.reCLM.comp ((fderiv ℂ f z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hd.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun w => (f w).re) (0 : Frame Ψ N →L[ℝ] ℝ) z := by
    have : (fun w => (f w).re) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hz] with w hw using hre w hw
    exact (hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq this
  have h3 := h1.unique h2
  show fderiv ℂ f z = 0
  ext v
  have hv : (fderiv ℂ f z v).re = 0 := by
    have := congrArg (fun L : Frame Ψ N →L[ℝ] ℝ => L v) h3
    simpa using this
  have hiv : (fderiv ℂ f z (Complex.I • v)).re = 0 := by
    have := congrArg (fun L : Frame Ψ N →L[ℝ] ℝ => L (Complex.I • v)) h3
    simpa using this
  rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at hiv
  apply Complex.ext <;> simp only [ContinuousLinearMap.zero_apply, Complex.zero_re, Complex.zero_im]
  · exact hv
  · linarith

/- English proof (translation)
Introduce `E _ _ _ N X R hdeg hR hR0 hRb hRγ`. Take `⟨L, hL, hLexp, hLb⟩` from `GlobalTheory.T.exists_invariant_logarithm E N X R hR hR0 hRb`. Use `⟨L, hL, hLexp, hLb, ?_⟩` and prove the remaining obligations. Break down `X.dom.eq_empty_or_nonempty with hemp | ⟨x0, hx0⟩` into its components or cases. Introduce `γ _ _ x hx`.

Rewrite `hx` using `[hemp]`. Conclude with `absurd hx (by simp)`. Establish `hopen : IsOpen X.dom` using `ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X`. Establish `hconn : IsPreconnected X.dom` using `(ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected (E := E) N X).isPreconnected`. Establish `hmem : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, lact γ x ∈ X.dom` using `fun γ hγ x hx => GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) hx`.

Establish `hdiff : ∀ γ ∈ X.Γ, DifferentiableOn ℂ (fun x => L (lact γ x) - L x) X.dom`. Introduce `γ hγ`. Use `DifferentiableOn.sub ?_ hL` and prove the remaining obligations. Conclude with `hL.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiable_lact γ).differentiableOn (fun x hx => hmem γ hγ x hx)`. Establish `hre : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, (L (lact γ x) - L x).re = 0`.

Introduce `γ hγ x hx`. Establish `h1` using `hRγ γ hγ x hx`. Rewrite `h1` using `[← hLexp _ (hmem γ hγ x hx), ← hLexp x hx, Complex.norm_exp, Complex.norm_exp]`. Establish `h2` using `Real.exp_injective h1`. Rewrite using `[Complex.sub_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hconst : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, L (lact γ x) - L x = L (lact γ x0) - L x0` using `fun γ hγ x hx => eq_of_re_eq_zero hopen hconn (hdiff γ hγ) (hre γ hγ) hx hx0`. Set `c : X.Γ → ℝ` to `fun γ => (L (lact γ x0) - L x0).im`. Establish `hc : ∀ γ γ' : X.Γ, c (γ * γ') = c γ + c γ'`. Introduce `γ γ'`.

Establish `e1 : L (lact (γ * γ' : X.Γ) x0) - L x0 = (L (lact γ (lact γ' x0)) - L (lact γ' x0)) + (L (lact γ' x0) - L x0)`. Rewrite using `[Subgroup.coe_mul, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e1` using `[hconst γ γ.2 _ (hmem γ' γ'.2 x0 hx0)]`. Simplify using `only [c]`.

Rewrite using `[e1, Complex.add_im]`. Set `φ : X.Γ →* Multiplicative ℝ` to `MonoidHom.mk' (fun γ => Multiplicative.ofAdd (c γ)) (fun γ γ' => by`. Rewrite using `[hc, ofAdd_add])`. Introduce `γ hγ hunip x hx`. Establish `hφ : φ ⟨γ, hγ⟩ = 1` using `GlobalTheory.T.character_trivial_on_unipotent E N X hdeg φ ⟨γ, hγ⟩ hunip`.

Establish `hc0 : c ⟨γ, hγ⟩ = 0`. Establish `: Multiplicative.ofAdd (c ⟨γ, hγ⟩) = 1` using `hφ`. Conclude with `ofAdd_eq_one.1 this`. Establish `h1 : L (lact γ x) - L x = 0`. Rewrite using `[hconst γ hγ x hx]`.

Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[hre γ hγ x0 hx0]`. Both sides reduce to the same expression. Conclude with `hc0`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (R : Frame X.Ψ N → ℂ), 1 < Module.finrank ℚ E / 2 → DifferentiableOn ℂ R X.dom → (∀ x ∈ X.dom, R x ≠ 0) → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, R (rmul x b) = R x) → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ‖R (lact γ x)‖ = ‖R x‖) → ∃ L : Frame X.Ψ N → ℂ, DifferentiableOn ℂ L X.dom ∧ (∀ x ∈ X.dom, Complex.exp (L x) = R x) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, L (rmul x b) = L x) ∧ ∀ γ ∈ X.Γ, ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → ∀ x ∈ X.dom, L (lact γ x) = L x := by
  intro E _ _ _ N X R hdeg hR hR0 hRb hRγ
  obtain ⟨L, hL, hLexp, hLb⟩ := GlobalTheory.T.exists_invariant_logarithm E N X R hR hR0 hRb
  refine ⟨L, hL, hLexp, hLb, ?_⟩
  rcases X.dom.eq_empty_or_nonempty with hemp | ⟨x0, hx0⟩
  · intro γ _ _ x hx
    rw [hemp] at hx
    exact absurd hx (by simp)
  have hopen : IsOpen X.dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X
  have hconn : IsPreconnected X.dom :=
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected (E := E) N X).isPreconnected
  have hmem : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, lact γ x ∈ X.dom :=
    fun γ hγ x hx => GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) hx

  have hdiff : ∀ γ ∈ X.Γ, DifferentiableOn ℂ (fun x => L (lact γ x) - L x) X.dom := by
    intro γ hγ
    refine DifferentiableOn.sub ?_ hL
    exact hL.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiable_lact γ).differentiableOn
      (fun x hx => hmem γ hγ x hx)
  have hre : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, (L (lact γ x) - L x).re = 0 := by
    intro γ hγ x hx
    have h1 := hRγ γ hγ x hx
    rw [← hLexp _ (hmem γ hγ x hx), ← hLexp x hx, Complex.norm_exp, Complex.norm_exp] at h1
    have h2 := Real.exp_injective h1
    rw [Complex.sub_re]
    linarith

  have hconst : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, L (lact γ x) - L x = L (lact γ x0) - L x0 :=
    fun γ hγ x hx => eq_of_re_eq_zero hopen hconn (hdiff γ hγ) (hre γ hγ) hx hx0

  let c : X.Γ → ℝ := fun γ => (L (lact γ x0) - L x0).im
  have hc : ∀ γ γ' : X.Γ, c (γ * γ') = c γ + c γ' := by
    intro γ γ'
    have e1 : L (lact (γ * γ' : X.Γ) x0) - L x0 =
        (L (lact γ (lact γ' x0)) - L (lact γ' x0)) + (L (lact γ' x0) - L x0) := by
      rw [Subgroup.coe_mul, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]; ring
    rw [hconst γ γ.2 _ (hmem γ' γ'.2 x0 hx0)] at e1
    simp only [c]
    rw [e1, Complex.add_im]
  let φ : X.Γ →* Multiplicative ℝ :=
    MonoidHom.mk' (fun γ => Multiplicative.ofAdd (c γ)) (fun γ γ' => by
      rw [hc, ofAdd_add])
  intro γ hγ hunip x hx
  have hφ : φ ⟨γ, hγ⟩ = 1 := GlobalTheory.T.character_trivial_on_unipotent E N X hdeg φ ⟨γ, hγ⟩ hunip
  have hc0 : c ⟨γ, hγ⟩ = 0 := by
    have : Multiplicative.ofAdd (c ⟨γ, hγ⟩) = 1 := hφ
    exact ofAdd_eq_one.1 this
  have h1 : L (lact γ x) - L x = 0 := by
    rw [hconst γ hγ x hx]
    apply Complex.ext
    · rw [hre γ hγ x0 hx0]; rfl
    · exact hc0
  exact sub_eq_zero.1 h1

end GlobalTheory.UnipLog
