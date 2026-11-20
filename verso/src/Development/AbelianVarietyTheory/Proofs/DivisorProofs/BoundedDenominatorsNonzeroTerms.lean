import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToPStatement

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKBound

/- English proof (translation)
Introduce `p _ G L f r K φ hG hr hf hφ`. Take `⟨Ω, hΩc, hΩ⟩` from `GlobalTheory.T.twistedHeckeTestFunction_support_compact p G L f hf`. Take `⟨D, hD, hDp⟩` from `GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP p G (Ω ∪ Ω⁻¹) (hΩc.union hΩc.inv)`. Take `⟨k, hk⟩` from `GlobalTheory.T.twisted_orbit_norm_bounds p G r K φ hr hφ`. Establish `hp` using `(Fact.out : p.Prime)`.

Use `⟨D * p ^ (2 * k * Module.finrank ℚ G.C), Nat.mul_pos hD (pow_pos hp.pos _), ?_⟩` and prove the remaining obligations. Introduce `P _ hP`. Establish `fin : ∀ (y0 : G.Cˣ) (c0 : ℚˣ), (y0 : G.C) * P.β * sh G y0 = algebraMap ℚ G.C c0 * P.β → ‖((c0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → ‖(((c0⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((G.rho w (y0 : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))) …`. Introduce `y0 c0 hy0 hc hc' hu hu' hAf`. Establish `hroots` using `GlobalTheory.T.bounded_eigenvalues_classes p G hG P.β y0 c0 hy0 _ hc hc' hu hu'`.

Establish `hroots' : ∀ μ : PadicAlgCl p, ((LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ (2 * k)` using `fun μ hμ => by`. Rewrite using `[show 2 * k = k + k by ring, pow_add]; exact hroots μ hμ`. Establish `h6` using `GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots p _ (LinearMap.charpoly_monic _) (2 * k) hroots'`. Rewrite `h6` using `[LinearMap.charpoly_natDegree]`. Apply `GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int G.C` to reduce the goal to its premises.

Introduce `i`. Take `⟨kk, hkk⟩` from `hAf i`. Conclude with `GlobalTheory.T.den_bound_combine_padic_primeToP p D (2 * k * Module.finrank ℚ G.C) kk hp _ (h6 i) hkk`. Rewrite `hP` using `[Pair.term]`. Use `split_ifs at hP with h`.

Use `swap`. Conclude with `absurd rfl hP`. Rewrite `hP` using `[Pair.termAt, pointSum]`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q, _ ≠ (0 : ℂ) := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hP (by rw [finsum_congr hc]; exact finsum_zero)`. Establish `hq2` using `(mul_ne_zero_iff.1 hq).2`. Establish `hfq` using `(mul_ne_zero_iff.1 hq2).1`. Establish `hφq` using `(mul_ne_zero_iff.1 hq2).2`.

Use `set x := P.trivAf.choose with hxdef`. Use `set o := Quotient.out q with hodef`. Establish `hgΩ` using `hΩ _ hfq`. Establish `hnrm` using `h.choose_spec`. Take `⟨hk1, hk2, hk3, hk4⟩` from `hk P.atP h.choose.1 h.choose.2 o.2 hnrm hφq`.

Use `set g := o.1⁻¹ * P.toAf x P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec P.self * o.1 with hg`. Establish `hg1 : ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) = ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ * ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x)⁻¹` using `by show ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) * (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = _ group`. Use `set X := (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x`. Establish `hA` using `hDp g (P.γ : G.C) X (Or.inl hgΩ) (by rw [hg1]; rfl)`. Establish `hgi : g⁻¹ ∈ Ω ∪ Ω⁻¹` using `Or.inr (by simpa using hgΩ)`.

Establish `hA'` using `hDp g⁻¹ ((P.γ⁻¹ : G.Cˣ) : G.C) X hgi (by show (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ).val = _`. Rewrite using `[hg1]`. Simplify using `[mul_assoc])`. Establish `hc1 : ((P.atP.1 : ℚ_[p]ˣ) : ℚ_[p]) = ((P.c : ℚ) : ℚ_[p])` using `by show algebraMap ℚ ℚ_[p] (P.c : ℚ) = _`. Simplify using the standard rewrite rules.

Establish `hc2 : ((P.atP.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (((P.c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])` using `by show algebraMap ℚ ℚ_[p] ((P.c⁻¹ : ℚˣ) : ℚ) = _`. Simplify using the standard rewrite rules. Establish `hw1 : ∀ w, (((P.atP.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) = G.rho w (P.γ : G.C)` using `fun w => rfl`. Establish `hw2 : ∀ w, ((((P.atP.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) = G.rho w ((P.γ⁻¹ : G.Cˣ) : G.C)` using `fun w => rfl`. Establish `hrel' : ((P.γ⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((P.γ⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C ((P.c⁻¹ : ℚˣ) : ℚ) * P.β` using `(P.cent.inv_mem P.self.2).2`.

Use `⟨fin P.γ P.c P.sim (hc1 ▸ hk1) (hc2 ▸ hk2) (fun w μ hμ => hk3 w μ (by rw [hw1]; exact hμ)) (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) hA, fin P.γ⁻¹ P.c⁻¹ hrel' (hc2 ▸ hk2) (by rw [inv_inv]; exact hc1 ▸ hk1) (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) (fun w μ hμ => hk3 w …` and prove the remaining obligations.
-/
theorem integral_of_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), IsSimple G → 0 < r → IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → ∃ N : ℕ, 0 < N ∧ ∀ P : Pair G, (∃ μ, P.Mark μ) → P.term L.K.toSubgroup f r K φ ≠ 0 → IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f r K φ hG hr hf hφ
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.twistedHeckeTestFunction_support_compact p G L f hf
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP p G (Ω ∪ Ω⁻¹) (hΩc.union hΩc.inv)
  obtain ⟨k, hk⟩ := GlobalTheory.T.twisted_orbit_norm_bounds p G r K φ hr hφ
  have hp := (Fact.out : p.Prime)
  refine ⟨D * p ^ (2 * k * Module.finrank ℚ G.C), Nat.mul_pos hD (pow_pos hp.pos _), ?_⟩
  intro P _ hP

  have fin : ∀ (y0 : G.Cˣ) (c0 : ℚˣ), (y0 : G.C) * P.β * sh G y0 = algebraMap ℚ G.C c0 * P.β →
      ‖((c0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → ‖(((c0⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w (y0 : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w ((y0⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ →
          ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ i, ∃ kk : ℕ, ∃ a : ℤ, ((D * p ^ kk : ℕ) : ℚ) * (LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.coeff i = a) →
      IsIntegral ℤ (((D * p ^ (2 * k * Module.finrank ℚ G.C) : ℕ) : ℤ) • (y0 : G.C)) := by
    intro y0 c0 hy0 hc hc' hu hu' hAf
    have hroots := GlobalTheory.T.bounded_eigenvalues_classes p G hG P.β y0 c0 hy0 _ hc hc' hu hu'
    have hroots' : ∀ μ : PadicAlgCl p,
        ((LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
        ‖μ‖ ≤ (p : ℝ) ^ (2 * k) := fun μ hμ => by
      rw [show 2 * k = k + k by ring, pow_add]; exact hroots μ hμ
    have h6 := GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots p _ (LinearMap.charpoly_monic _) (2 * k) hroots'
    rw [LinearMap.charpoly_natDegree] at h6
    apply GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int G.C
    intro i
    obtain ⟨kk, hkk⟩ := hAf i
    exact GlobalTheory.T.den_bound_combine_padic_primeToP p D (2 * k * Module.finrank ℚ G.C) kk hp _ (h6 i) hkk

  rw [Pair.term] at hP
  split_ifs at hP with h
  swap
  · exact absurd rfl hP
  rw [Pair.termAt, pointSum] at hP
  obtain ⟨q, hq⟩ : ∃ q, _ ≠ (0 : ℂ) := by
    by_contra hc
    push_neg at hc
    exact hP (by rw [finsum_congr hc]; exact finsum_zero)
  have hq2 := (mul_ne_zero_iff.1 hq).2
  have hfq := (mul_ne_zero_iff.1 hq2).1
  have hφq := (mul_ne_zero_iff.1 hq2).2
  set x := P.trivAf.choose with hxdef
  set o := Quotient.out q with hodef
  have hgΩ := hΩ _ hfq
  have hnrm := h.choose_spec
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk P.atP h.choose.1 h.choose.2 o.2 hnrm hφq
  set g := o.1⁻¹ * P.toAf x P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec P.self * o.1 with hg
  have hg1 : ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
      ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ *
        ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x)⁻¹ := by
    show ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) *
      (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = _
    group
  set X := (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x
  have hA := hDp g (P.γ : G.C) X (Or.inl hgΩ) (by rw [hg1]; rfl)
  have hgi : g⁻¹ ∈ Ω ∪ Ω⁻¹ := Or.inr (by simpa using hgΩ)
  have hA' := hDp g⁻¹ ((P.γ⁻¹ : G.Cˣ) : G.C) X hgi (by
    show (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ).val = _
    rw [hg1]; simp [mul_assoc])
  have hc1 : ((P.atP.1 : ℚ_[p]ˣ) : ℚ_[p]) = ((P.c : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] (P.c : ℚ) = _
    simp
  have hc2 : ((P.atP.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (((P.c⁻¹ : ℚˣ) : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] ((P.c⁻¹ : ℚˣ) : ℚ) = _
    simp
  have hw1 : ∀ w, (((P.atP.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w (P.γ : G.C) := fun w => rfl
  have hw2 : ∀ w, ((((P.atP.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w ((P.γ⁻¹ : G.Cˣ) : G.C) := fun w => rfl
  have hrel' : ((P.γ⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((P.γ⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C ((P.c⁻¹ : ℚˣ) : ℚ) * P.β := (P.cent.inv_mem P.self.2).2
  refine ⟨fin P.γ P.c P.sim (hc1 ▸ hk1) (hc2 ▸ hk2) (fun w μ hμ => hk3 w μ (by rw [hw1]; exact hμ))
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) hA,
    fin P.γ⁻¹ P.c⁻¹ hrel' (hc2 ▸ hk2) (by rw [inv_inv]; exact hc1 ▸ hk1)
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ))
      (fun w μ hμ => hk3 w μ (by rw [hw1, ← inv_inv P.γ]; exact hμ)) hA'⟩

end GlobalTheory.LKBound
