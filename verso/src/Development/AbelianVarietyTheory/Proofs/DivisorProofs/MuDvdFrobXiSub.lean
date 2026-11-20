import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMixedTsub

set_option autoImplicit false

noncomputable section

open GlobalTheory.QLog GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.WinLift

section Nil

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isNil_of_theta_eq {B R ι : Type} [CommRing B] [CommRing R] [IsLocalRing R] [Fintype ι]
    (p : ℕ) [Fact p.Prime] (θ : B →+* R) (σ : B →+* B) (hp : ¬IsUnit (p : R))
    (hσ : ∀ b, (p : B) ∣ σ b - b ^ p) (M M' : Matrix ι ι B) (h : ∀ i j, θ (M i j) = θ (M' i j))
    (hM : IsNil θ σ M) : IsNil θ σ M' := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun v i => ?_⟩
  have hs : ∀ z : B, θ z ∈ IsLocalRing.maximalIdeal R → θ (σ z) ∈ IsLocalRing.maximalIdeal R := by
    intro z hz
    obtain ⟨c, hc⟩ := hσ z
    have e : σ z = z ^ p + p * c := by rw [← hc]; ring
    rw [e, map_add, map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hz _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp))
  have key : ∀ (n : ℕ) (w : ι → B) (i : ι),
      θ (((fun w : ι → B => M.mulVec fun j => σ (w j))^[n] w) i) -
        θ (((fun w : ι → B => M'.mulVec fun j => σ (w j))^[n] w) i) ∈
          IsLocalRing.maximalIdeal R := by
    intro n
    induction n with
    | zero => intro w i; simp
    | succ n ih =>
      intro w i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Matrix.mulVec, dotProduct]
      rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul, map_mul, h i j, ← mul_sub, ← map_sub, ← map_sub]
      exact Ideal.mul_mem_left _ _ (hs _ (by rw [map_sub]; exact ih w j))
  intro hu
  have h1 := (IsLocalRing.mem_maximalIdeal _).2 (hN v i)
  have h2 := Ideal.sub_mem _ h1 (key N v i)
  rw [sub_sub_cancel] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Both sides reduce to the same expression. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem isNil_of_map {A B R ι : Type} [CommRing A] [CommRing B] [CommRing R] [Fintype ι]
    (a : A →+* B) (θA : A →+* R) (θB : B →+* R) (φ : A →+* A) (σ : B →+* B)
    (hθ : ∀ x, θB (a x) = θA x) (hσ : ∀ x, σ (a x) = a (φ x)) (M : Matrix ι ι A)
    (h : IsNil θB σ (M.map a)) : IsNil θA φ M := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun v i => ?_⟩
  have key : ∀ (n : ℕ) (w : ι → A),
      (fun w : ι → B => (M.map a).mulVec fun j => σ (w j))^[n] (fun j => a (w j)) =
        fun j => a (((fun w : ι → A => M.mulVec fun j => φ (w j))^[n] w) j) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext j
      simp [Matrix.mulVec, dotProduct, map_sum, hσ]
  have := hN (fun j => a (v j)) i
  rwa [key, hθ] at this

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem map_inv_of_isUnit {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) (hM : IsUnit M) : (M.map f)⁻¹ = M⁻¹.map f := by
  apply Matrix.inv_eq_right_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), map_one]

end Nil

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem frob_xi (ε : PreTilt O p) :
    WittVector.frobenius (xi ε) = ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
  have : root ε ^ p = ε := (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε
  simp only [xi, map_sum, map_pow, frob_teich]
  simp only [← map_pow, this]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem frob_mu (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  rw [frob_xi, Sandwich.mu, geom_sum_mul, map_sub, map_one, frob_teich]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mu_dvd_frob_xi_sub (ε : PreTilt O p) :
    Sandwich.mu ε ∣ WittVector.frobenius (xi ε) - p := by
  have : (p : Ainf p O) = ∑ i ∈ Finset.range p, 1 ^ i := by simp
  rw [this, frob_xi, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow _ _ i

end Frob

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p}

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem root_prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (PreTilt.untilt (root ε)) p := by
  simpa [zeta] using hε 1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theta_mu (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 :=
  Sandwich.Model.theta_mu hv (root_prim hε)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem theta_frob_xi (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (WittVector.frobenius (xi ε)) = p := by
  have h1 : WittVector.fontaineTheta O p (WittVector.teichmuller p ε) = 1 := by
    have := theta_mu hv hε
    rw [Sandwich.mu, map_sub, map_one, sub_eq_zero] at this
    exact this
  rw [frob_xi, map_sum]
  simp [h1]

variable (F : BFrame ε)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tf (b : F.B) (h : (p : F.B) * b = 0) : b = 0 := by
  apply F.frame.inj
  have h1 := congrArg (algebraMap F.B F.Q) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (F.frame.unit_p.mul_right_eq_zero).1 h1

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem theta_tau (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : F.θ F.τ = 0 := by
  apply F.frame.sat
  have h := congrArg F.θ F.p_τ
  rw [map_mul, map_natCast, F.θ_a, theta_mu hv hε] at h
  exact h

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigma_tau : F.σ F.τ = F.a (WittVector.frobenius (xi ε)) * F.τ := by
  apply sub_eq_zero.1
  apply tf F
  have h := congrArg F.σ F.p_τ
  rw [map_mul, map_natCast, F.σ_a, frob_mu, map_mul, ← F.p_τ] at h
  rw [mul_sub, h]
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem tau_dvd_sigma (b : F.B) (h : F.τ ∣ b) : F.τ ∣ F.σ b := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, sigma_tau]
  exact ⟨F.a (WittVector.frobenius (xi ε)) * F.σ c, by ring⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Chain the equalities or inequalities of the calculation.
-/
theorem mu_dvd_of_p_mul (F : BFrame ε) (z : Ainf p O) (h : Sandwich.mu ε ∣ (p : Ainf p O) * z) :
    Sandwich.mu ε ∣ z := by
  obtain ⟨w, hw⟩ := h
  apply (F.τ_mul z).1
  apply tf F
  have h1 := congrArg F.a hw
  rw [map_mul, map_natCast, map_mul, ← F.p_τ] at h1
  calc (p : F.B) * (F.τ * F.a z) = F.τ * ((p : F.B) * F.a z) := by ring
    _ = 0 := by rw [h1]; linear_combination (p * F.a w) * F.τ_sq

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem mu_dvd_of_xi_mul (F : BFrame ε) (z : Ainf p O)
    (h : Sandwich.mu ε ∣ WittVector.frobenius (xi ε) * z) : Sandwich.mu ε ∣ z := by
  apply mu_dvd_of_p_mul F
  have h2 := (mu_dvd_frob_xi_sub ε).mul_right z
  have := dvd_sub h h2
  rwa [sub_mul, sub_sub_cancel] at this

end Frame

end GlobalTheory.WinLift
