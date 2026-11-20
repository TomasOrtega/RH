import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchDimOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. It suffices to derive a contradiction. Establish an intermediate fact. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

It suffices to derive a contradiction. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem PrimeBranchDimOne.proof : PrimeBranchDimOne.Statement := by
  intro n J q c hJ hloc

  have hq : q ∈ zeroSet J := by
    have := c.mapsTo (Metric.mem_ball_self c.radius_pos)
    rwa [c.map_zero] at this

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at hle hnn
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact absurd (WithBot.coe_le_coe.mp h3) (by simp)
      | coe e => exact ⟨e, rfl⟩
  have hdim : ringKrullDim (localRingAt J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have he1 : e ≤ 1 := by
    have h2 : ((e : ℕ) : WithBot ℕ∞) ≤ 1 := hdim ▸ hloc
    exact_mod_cast h2
  rw [he]
  obtain h0 | h1 : e = 0 ∨ e = 1 := by omega
  swap
  · rw [h1]
  exfalso
  subst h0

  have hfield : IsField (MvPolynomial (Fin n) ℂ ⧸ J) := by
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).2 (by simpa using he)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield
  have hJM : J = RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    hmax.eq_of_le (RingHom.ker_ne_top _) (fun f hf => RingHom.mem_ker.mpr (hq f hf))

  have hZ : ∀ x ∈ zeroSet J, x = q := by
    intro x hx
    funext i
    have hmem : X i - C (q i) ∈ J := by
      rw [hJM, RingHom.mem_ker]
      simp
    have := hx _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.mp this

  set r := c.radius
  let v : Fin 1 → ℂ := fun _ => ((r / 2 : ℝ) : ℂ)
  have hv : v ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff c.radius_pos]
    intro i
    simp only [v, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos c.radius_pos)]
    exact half_lt_self c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := Metric.mem_ball_self c.radius_pos
  have heq : c.toFun v = c.toFun 0 := by
    rw [hZ _ (c.mapsTo hv), hZ _ (c.mapsTo h0)]
  have := congrFun (c.injOn hv h0 heq) 0
  simp only [v, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  exact (half_pos c.radius_pos).ne' this

end GroundTheory.Heights₂.Heights
