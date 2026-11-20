import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConst

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `B.hsVec`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem tc_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

/- English proof (translation)
Establish `h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0` using `fun i => by`. Use `congrArg (fun w => w i) h` as an intermediate fact. Simplify `this` using `[B.hsVec]`. Establish `hl : A.toLinearMap = (0 : Wq →ₗ[ℂ] Wp)` using `(stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => by simpa using h' i`. Use extensionality with `v`.

Conclude with `LinearMap.congr_fun hl v`.
-/
theorem tc_hsVec_eq_zero {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => by
    have := congrArg (fun w => w i) h
    simpa [B.hsVec] using this
  have hl : A.toLinearMap = (0 : Wq →ₗ[ℂ] Wp) :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => by simpa using h' i
  ext v
  exact LinearMap.congr_fun hl v

end hs

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[h i, h' i]`.
-/
theorem tc_up_unique {P : M.Par} {l : ℕ} {π ρ ρ' : M.Ty P} (h : M.Up P l π ρ) (h' : M.Up P l π ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

/- English proof (translation)
Introduce `hPR hMC hLN hPF`. Introduce `Wp Wq _ _ _ _ _ _ P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw'`. Establish `main : ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf → (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) = c • (Pr ρ (SSn.nu0 P.k P.r Bs.z B …`. Introduce `π ρ hup`. Take `⟨n, q, hq⟩` from `hPR Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup`.

Take `⟨c₁, c₂, hc⟩` from `hMC Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup`. Establish `hGG : ∀ ζ ∈ Gauge.GC.Ann P, (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) ≠ 0`. Introduce `ζ hζ`. Establish `: (0 : ℝ) < Complex.normSq ζ - P.TT`. Use `hζ` as an intermediate fact.

Simplify using `only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `pow_ne_zero _ (by exact_mod_cast this.ne')`. Distinguish the cases in `hc2 : c₂ = 0`. Use `⟨0, fun ζ hζ Xf hXf hfix => ?_⟩` and prove the remaining obligations.

Establish `hB0` using `(hc ζ hζ Xf hXf hfix).2`. Rewrite `hB0` using `[hc2, zero_mul, sq_eq_zero_iff, norm_eq_zero]`. Establish `hB0'` using `tc_hsVec_eq_zero hB0`. Establish `h1` using `hq ζ hζ Xf hXf hfix`. Rewrite `h1` using `[hB0', smul_zero]`.

Rewrite using `[zero_smul]`. Conclude with `(smul_eq_zero.1 h1).resolve_left (hGG ζ hζ)`. Establish `hTT : 0 ≤ P.TT`. Use `hAct.1.1` as an intermediate fact. Conclude with `mul_nonneg this.T_pos.le this.T'_pos.le`.

Establish `hmod : ∀ x : ℝ, P.TT < x → Complex.normSq (q.eval (x : ℂ)) = (c₁ / c₂) * (x - P.TT) ^ (2 * n)`. Introduce `x hx`. Establish `hx0 : 0 ≤ x` using `le_trans hTT hx.le`. Use `set ζ : ℂ := ((Real.sqrt x : ℝ) : ℂ) with hζdef`. Establish `hnz : Complex.normSq ζ = x`.

Rewrite using `[hζdef, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hx0]`. Establish `hζ : ζ ∈ Gauge.GC.Ann P` using `by show P.TT < Complex.normSq ζ`. Rewrite using `[hnz]`. Conclude with `hx`. Take `⟨Xf, hXf, hfix, hne⟩` from `hLN Wp Wq P Bs hAct.1 hk Pr hPr π ζ hζ`.

Take `⟨hS1, hB1⟩` from `hc ζ hζ Xf hXf hfix`. Establish `h1` using `congrArg (fun w => ‖B.hsVec w‖ ^ 2) (hq ζ hζ Xf hXf hfix)`. Simplify using `only [tc_hsVec_smul, norm_smul, mul_pow] at h1`. Rewrite `h1` using `[hS1, hB1, hnz]`. Establish `hX : 0 < ‖B.hsVec Xf‖ ^ 2`.

Establish `: B.hsVec Xf ≠ 0` using `fun h0 => hne (tc_hsVec_eq_zero h0)`. Check the signs of the components of the expression. Establish `hnq : ‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 = Complex.normSq (q.eval (x : ℂ))`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Establish `hng : ‖((x - P.TT : ℝ) : ℂ) ^ n‖ ^ 2 = (x - P.TT) ^ (2 * n)`.

Rewrite using `[norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x - P.TT), ← pow_mul, mul_comm]`. Rewrite `h1` using `[hng]`. Establish `h2 : (‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 * c₂ - (x - P.TT) ^ (2 * n) * c₁) * ‖B.hsVec Xf‖ ^ 2 = 0`. Take the linear combination `(-1 : ℝ) * h1`. Establish `h3` using `sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX.ne')`.

Rewrite using `[← hnq, div_mul_eq_mul_div, eq_div_iff hc2]`. Combine the linear relations using `[h3]`. Take `⟨c, hcq⟩` from `hPF q n P.TT (c₁ / c₂) hmod`. Use `⟨c, fun ζ hζ Xf hXf hfix => ?_⟩` and prove the remaining obligations. Establish `h1` using `hq ζ hζ Xf hXf hfix`.

Rewrite `h1` using `[hcq]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X] at h1`. Establish `he : ((Complex.normSq ζ : ℝ) : ℂ) - (P.TT : ℂ) = (((Complex.normSq ζ - P.TT : ℝ)) : ℂ)` using `by push_cast; ring`. Rewrite `h1` using `[he, mul_comm, mul_smul]`. Conclude with `smul_right_injective _ (hGG ζ hζ) h1`.

Use `⟨fun π => if h : ∃ ρ, M.Up P l π ρ then (main π h.choose h.choose_spec).choose else 0, ?_⟩` and prove the remaining obligations. Introduce `ζ hζ π ρ hup Xf hXf hfix`. Establish `hex : ∃ ρ, M.Up P l π ρ` using `⟨ρ, hup⟩`. Establish `hρ : hex.choose = ρ` using `tc_up_unique hex.choose_spec hup`. Simplify using `only [dif_pos hex]`.

Use `(main π hex.choose hex.choose_spec).choose_spec ζ hζ Xf hXf hfix` as an intermediate fact. Substitute `hρ` using the available equality. Conclude with `this`.
-/
theorem theta_constancy_assembly : ThConstOfCut := by
  intro hPR hMC hLN hPF
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw'
  have main : ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) := by
    intro π ρ hup
    obtain ⟨n, q, hq⟩ := hPR Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    obtain ⟨c₁, c₂, hc⟩ := hMC Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    have hGG : ∀ ζ ∈ Gauge.GC.Ann P, (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) ≠ 0 := by
      intro ζ hζ
      have : (0 : ℝ) < Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      exact pow_ne_zero _ (by exact_mod_cast this.ne')
    by_cases hc2 : c₂ = 0
    · refine ⟨0, fun ζ hζ Xf hXf hfix => ?_⟩
      have hB0 := (hc ζ hζ Xf hXf hfix).2
      rw [hc2, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hB0
      have hB0' := tc_hsVec_eq_zero hB0
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hB0', smul_zero] at h1
      rw [zero_smul]
      exact (smul_eq_zero.1 h1).resolve_left (hGG ζ hζ)
    ·
      have hTT : 0 ≤ P.TT := by
        have := hAct.1.1
        exact mul_nonneg this.T_pos.le this.T'_pos.le
      have hmod : ∀ x : ℝ, P.TT < x → Complex.normSq (q.eval (x : ℂ)) = (c₁ / c₂) * (x - P.TT) ^ (2 * n) := by
        intro x hx
        have hx0 : 0 ≤ x := le_trans hTT hx.le
        set ζ : ℂ := ((Real.sqrt x : ℝ) : ℂ) with hζdef
        have hnz : Complex.normSq ζ = x := by
          rw [hζdef, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hx0]
        have hζ : ζ ∈ Gauge.GC.Ann P := by
          show P.TT < Complex.normSq ζ
          rw [hnz]; exact hx
        obtain ⟨Xf, hXf, hfix, hne⟩ := hLN Wp Wq P Bs hAct.1 hk Pr hPr π ζ hζ
        obtain ⟨hS1, hB1⟩ := hc ζ hζ Xf hXf hfix
        have h1 := congrArg (fun w => ‖B.hsVec w‖ ^ 2) (hq ζ hζ Xf hXf hfix)
        simp only [tc_hsVec_smul, norm_smul, mul_pow] at h1
        rw [hS1, hB1, hnz] at h1
        have hX : 0 < ‖B.hsVec Xf‖ ^ 2 := by
          have : B.hsVec Xf ≠ 0 := fun h0 => hne (tc_hsVec_eq_zero h0)
          positivity
        have hnq : ‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 = Complex.normSq (q.eval (x : ℂ)) := by
          rw [Complex.normSq_eq_norm_sq]
        have hng : ‖((x - P.TT : ℝ) : ℂ) ^ n‖ ^ 2 = (x - P.TT) ^ (2 * n) := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x - P.TT), ← pow_mul,
            mul_comm]
        rw [hng] at h1
        have h2 : (‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 * c₂ - (x - P.TT) ^ (2 * n) * c₁) * ‖B.hsVec Xf‖ ^ 2 = 0 := by
          linear_combination (-1 : ℝ) * h1
        have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX.ne')
        rw [← hnq, div_mul_eq_mul_div, eq_div_iff hc2]
        linarith [h3]
      obtain ⟨c, hcq⟩ := hPF q n P.TT (c₁ / c₂) hmod
      refine ⟨c, fun ζ hζ Xf hXf hfix => ?_⟩
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hcq] at h1
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X] at h1
      have he : ((Complex.normSq ζ : ℝ) : ℂ) - (P.TT : ℂ) = (((Complex.normSq ζ - P.TT : ℝ)) : ℂ) := by push_cast; ring
      rw [he, mul_comm, mul_smul] at h1
      exact smul_right_injective _ (hGG ζ hζ) h1
  classical
  refine ⟨fun π => if h : ∃ ρ, M.Up P l π ρ then (main π h.choose h.choose_spec).choose else 0, ?_⟩
  intro ζ hζ π ρ hup Xf hXf hfix
  have hex : ∃ ρ, M.Up P l π ρ := ⟨ρ, hup⟩
  have hρ : hex.choose = ρ := tc_up_unique hex.choose_spec hup
  simp only [dif_pos hex]
  have := (main π hex.choose hex.choose_spec).choose_spec ζ hζ Xf hXf hfix
  subst hρ
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
