import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def qOne (P : M.Par) (ζ : ℂ) (hζ : ζ ∈ Ann P) : MA.Qp P.r P.TT :=
  ⟨(fun _ => (1 : ℂ), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩

/- English proof (translation)
Establish `hpl` using `hyp.1`. Establish `hk2` using `hyp.2.1`. Set `F : M.Ty P → MA.SmQ P.r P.TT` to `fun τ => if τ = ρ then fnZ P (fun _ => (1 : ℂ)) else 0`. Take `⟨Φ, hΦ, hΦv⟩` from `SSTr.exists_tr P Bs hpl hk2 e0 he0 F`. Set `f : M.Ty P → ℂ` to `fun τ => if τ = ρ then 1 else 0`.

Establish `hfix : (d.κ f).1 Φ = Φ`. Apply `SSTr.trR_inj P Bs hpl hk2 e0 he0` to reduce the goal to its premises. Rewrite using `[hk0 f Φ, hΦ]`. Use function extensionality and compare the values at `τ`. Rewrite using `[actA_kap]`.

Distinguish the cases in `h : τ = ρ`. Simplify using `[f, h]`. Simplify using `[f, F, h]`. Establish `hz : trR P Bs e Φ σ = 0`. Establish `h` using `congrFun (hk f Φ) σ`.

Rewrite `h` using `[hfix, actA_kap]`. Rewrite using `[h]`. Simplify using `[f, hσ]`. Establish `hq` using `congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) hz`. Simplify using `only [ZeroMemClass.coe_zero, Pi.zero_apply] at hq`.

Rewrite `hq` using `[SSTr.trR_apply P Bs hpl hk2 e he Φ σ, rawR, hΦv]`. Establish `h1 : ((F ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ) = 1`. Simplify using `only [F, if_pos rfl, fnZ_eq_mk P (contDiffOn_const (c := (1 : ℂ)))]`. Establish `hsum : inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) = (((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ))`. Rewrite using `[SSTr.hsVec_sum, inner_sum, Finset.sum_eq_single ρ]`.

Rewrite using `[hsVec_smul, inner_smul_right, h1, mul_one]`. Introduce `τ _ hτ`. Simplify using `only [F, if_neg hτ, ZeroMemClass.coe_zero, Pi.zero_apply, mul_zero, zero_smul]`. Rewrite using `[← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hsVec_smul, zero_smul, inner_zero_right]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ ρ) h`. Establish `hw` using `SSTr.wR_pos P (ζ := ζ) hζ`. Express the relevant statement in the definitionally equal form `((wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) = 0 at hq`. Rewrite `hq` using `[hsum, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_mul]`. Conclude with `hq`.
-/
theorem kap_orth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ σ : M.Ty P) (hσ : σ ≠ ρ) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) = 0 := by
  have hpl := hyp.1
  have hk2 := hyp.2.1
  let F : M.Ty P → MA.SmQ P.r P.TT := fun τ => if τ = ρ then fnZ P (fun _ => (1 : ℂ)) else 0
  obtain ⟨Φ, hΦ, hΦv⟩ := SSTr.exists_tr P Bs hpl hk2 e0 he0 F
  let f : M.Ty P → ℂ := fun τ => if τ = ρ then 1 else 0
  have hfix : (d.κ f).1 Φ = Φ := by
    apply SSTr.trR_inj P Bs hpl hk2 e0 he0
    rw [hk0 f Φ, hΦ]
    funext τ
    rw [actA_kap]
    by_cases h : τ = ρ
    · simp [f, h]
    · simp [f, F, h]
  have hz : trR P Bs e Φ σ = 0 := by
    have h := congrFun (hk f Φ) σ
    rw [hfix, actA_kap] at h
    rw [h]
    simp [f, hσ]
  have hq := congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) hz
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at hq
  rw [SSTr.trR_apply P Bs hpl hk2 e he Φ σ, rawR, hΦv] at hq
  have h1 : ((F ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ) = 1 := by
    simp only [F, if_pos rfl, fnZ_eq_mk P (contDiffOn_const (c := (1 : ℂ)))]
  have hsum : inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) =
      (((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) := by
    rw [SSTr.hsVec_sum, inner_sum, Finset.sum_eq_single ρ]
    · rw [hsVec_smul, inner_smul_right, h1, mul_one]
    · intro τ _ hτ
      simp only [F, if_neg hτ, ZeroMemClass.coe_zero, Pi.zero_apply, mul_zero, zero_smul]
      rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hsVec_smul, zero_smul, inner_zero_right]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  have hw := SSTr.wR_pos P (ζ := ζ) hζ
  change ((wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) = 0 at hq
  rw [hsum, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_mul] at hq
  exact hq

def hsCLM : (Wq →L[ℂ] Wp) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  (LinearMap.toContinuousLinearMap (SSTr.hsL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsCLM_apply (A : Wq →L[ℂ] Wp) : hsCLM A = B.hsVec A := rfl

/- English proof (translation)
Take `⟨hfib0, -, -⟩` from `(he0.2 ζ hζ)`. Take `⟨-, -, hexp⟩` from `he.2 ζ hζ`. Use `conv_lhs => rw [hexp (e0 ρ ζ) (hfib0 ρ)]`. Rewrite using `[Finset.sum_eq_single ρ]`. Introduce `σ _ hσ`.

Rewrite using `[kap_orth P Bs X d hyp e e0 he hk he0 hk0 ρ σ hσ ζ hζ, zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ ρ) h`.
-/
theorem e0_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ : M.Ty P) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    e0 ρ ζ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e0 ρ ζ)) • e ρ ζ := by
  obtain ⟨hfib0, -, -⟩ := (he0.2 ζ hζ)
  obtain ⟨-, -, hexp⟩ := he.2 ζ hζ
  conv_lhs => rw [hexp (e0 ρ ζ) (hfib0 ρ)]
  rw [Finset.sum_eq_single ρ]
  · intro σ _ hσ
    rw [kap_orth P Bs X d hyp e e0 he hk he0 hk0 ρ σ hσ ζ hζ, zero_smul]
  · intro h; exact absurd (Finset.mem_univ ρ) h

end

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hyp e e0 he hk he0 hk0`. Use `⟨fun ρ ζ => inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)), fun ρ => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `(hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he0.1 ρ)`. Establish `h2` using `(hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he.1 ρ)`. Establish `h3` using `h1.inner ℂ h2`.

Simplify using `only [Function.comp_def, hsCLM_apply] at h3`. Conclude with `h3`. Introduce `ζ hζ`. Establish `hrel` using `e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ`. Establish `hn` using `((he.2 ζ hζ).2.1 ρ ρ)`.

Rewrite `hn` using `[if_pos rfl]`. Use `set c := inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)) with hc`. Establish `hn0` using `((he0.2 ζ hζ).2.1 ρ ρ)`. Rewrite `hn0` using `[if_pos rfl]`. Rewrite `hn` using `[hrel, hsVec_smul, inner_smul_left, inner_smul_right, hn0, mul_one]`.

Establish `h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1`. Rewrite using `[← hn, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]`. Establish `h3 : ‖c‖ ^ 2 = 1` using `by exact_mod_cast h2`. Establish `h4 : 0 ≤ ‖c‖` using `norm_nonneg c`. Use polynomial arithmetic with `[h3, h4]`.

Introduce `ρ ζ hζ`. Conclude with `e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ`.
-/
theorem phase_relation_holds : GTCPhaseRel := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e e0 he hk he0 hk0
  refine ⟨fun ρ ζ => inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)), fun ρ => ⟨?_, ?_⟩, ?_⟩
  · have h1 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he0.1 ρ)
    have h2 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he.1 ρ)
    have h3 := h1.inner ℂ h2
    simp only [Function.comp_def, hsCLM_apply] at h3
    exact h3
  · intro ζ hζ
    have hrel := e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ
    have hn := ((he.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn
    set c := inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)) with hc
    have hn0 := ((he0.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn0
    rw [hrel, hsVec_smul, inner_smul_left, inner_smul_right, hn0, mul_one] at hn
    have h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hn, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
    have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith [h3, h4]
  · intro ρ ζ hζ
    exact e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
