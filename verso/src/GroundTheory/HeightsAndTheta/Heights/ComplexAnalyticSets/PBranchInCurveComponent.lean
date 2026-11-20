import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInCurveComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Introduce `n I q c hdim`. Take `⟨J, hJ, hmaps⟩` from `h₁ n I 1 q c`. Establish `hJp : J.IsPrime` using `hJ.1.1`. Establish `hIJ : I ≤ J` using `hJ.1.2`. Establish `hq : q ∈ zeroSet J` using `c.map_zero ▸ hmaps (Metric.mem_ball_self c.radius_pos)`.

Use `⟨J, hJ, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds _ c.radius_pos) hmaps⟩` and prove the remaining obligations. Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J)` using `inferInstance`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ)`. Use `(ringKrullDim_quotient_le J).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by`. Establish `h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)` using `ringKrullDim_nonneg_of_nontrivial`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢`. Proceed by induction on `d using WithBot.recBotCoe with`.

Consider the case `bot => simp at h0`. Consider the case `coe x`. Proceed by induction on `x using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction.

Simplify using `only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle`. Consider the case `coe e => exact ⟨e, rfl⟩`. Establish `he1 : (e : WithBot ℕ∞) ≤ 1`. Rewrite using `[← LocalDimDomain.proof n e J hJp he q hq, ← hdim]`. Conclude with `ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hIJ)) (Ideal.Quotient.factor_surjective _)`.

Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Establish `: Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J)` using `ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (by simpa using he)`. Establish `hJq : J = RingHom.ker (eval q)` using `(Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain).eq_of_le (RingHom.ker_ne_top _) fun f hf ↦ RingHom.mem_ker.2 (hq f hf)`. Establish `hr` using `c.radius_pos`.

Establish `ht : (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius`. Rewrite using `[mem_ball_zero_iff, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hct : c.toFun (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) = c.toFun 0`. Rewrite using `[c.map_zero]`.

Use function extensionality and compare the values at `i`. Establish `hmem : X i - C (q i) ∈ J`. Rewrite using `[hJq, RingHom.mem_ker]`. Simplify using the standard rewrite rules. Simplify `hmaps ht _ hmem` using `[sub_eq_zero]`.

Establish `h0` using `congrFun (c.injOn ht (Metric.mem_ball_self hr) hct) 0`. Simplify using `only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[he]`. Establish `: e ≤ 1` using `by exact_mod_cast he1`.

Establish `: e = 1` using `by omega`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem BranchInCurveComponent.proof (h₁ : BranchInComponent.Statement) :
    BranchInCurveComponent.Statement := by
  intro n I q c hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hq : q ∈ zeroSet J := c.map_zero ▸ hmaps (Metric.mem_ball_self c.radius_pos)
  refine ⟨J, hJ, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds _ c.radius_pos) hmaps⟩
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := inferInstance
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have he1 : (e : WithBot ℕ∞) ≤ 1 := by
    rw [← LocalDimDomain.proof n e J hJp he q hq, ← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hIJ))
      (Ideal.Quotient.factor_surjective _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (by simpa using he)
    have hJq : J = RingHom.ker (eval q) :=
      (Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain).eq_of_le
        (RingHom.ker_ne_top _) fun f hf ↦ RingHom.mem_ker.2 (hq f hf)
    have hr := c.radius_pos
    have ht : (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
      rw [mem_ball_zero_iff, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hct : c.toFun (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) = c.toFun 0 := by
      rw [c.map_zero]
      funext i
      have hmem : X i - C (q i) ∈ J := by
        rw [hJq, RingHom.mem_ker]
        simp
      simpa [sub_eq_zero] using hmaps ht _ hmem
    have h0 := congrFun (c.injOn ht (Metric.mem_ball_self hr) hct) 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    linarith
  rw [he]
  have : e ≤ 1 := by exact_mod_cast he1
  have : e = 1 := by omega
  subst this
  rfl

end GroundTheory.Heights₂.Heights
