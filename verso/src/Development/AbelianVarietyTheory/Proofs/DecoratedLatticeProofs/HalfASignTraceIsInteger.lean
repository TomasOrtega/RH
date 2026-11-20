import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AlVEmbHEqNegOneZpow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfAStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TraceInt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SemiTrace

/- English proof (translation)
Establish `hd : 0 < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))`. Use `set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) with htdef`. Use `set M := LinearMap.toMatrix' y with hMdef`. Establish `hMij : ∀ i j, M i j = y (Pi.single j 1) i`. Introduce `i j`.

Simplify using `[M, LinearMap.toMatrix'_apply]`. Use `set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs`. Establish `hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ)`. Introduce `τ`. Simplify using `only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]`.

Simplify using `only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]`. Use `push_cast`. Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Use `_ = _ := Finset.sum_comm`.

Establish `hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2`. Introduce `τ`. Rewrite using `[map_mul, map_mul, map_pow, map_div₀, map_add, map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD, Complex.re_mul_ofReal, re_xi_mul_sq _ hd]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk' : (t : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ)`.

Establish `e1` using `sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)`. Rewrite `e1` using `[← htdef]`. Rewrite using `[← e1]`. Simplify using `only [hτ]`. Use `push_cast`.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹`. Rewrite using `[← Complex.sq_norm]`.

Conclude with `hP.scale`. Establish `hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ`. Simplify using `only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]`. Rewrite using `[show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) = ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]`. Repeatedly rewrite using `[Complex.normSq_mul, ← Finset.mul_sum]`.

Simplify using `only [hs, hMij]`. Rewrite using `[← mul_assoc sc, hsc]`. Clear the denominators using the available nonvanishing facts. Establish `hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(t : ℂ)` using `by rw [hk']; push_cast; ring`. Rewrite using `[alV, Formalism.L2.Th1.H.alphaQ, hq, hsum]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alV_embH_eq_exp_trace (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ)
    (hP : StdPair θ S T δ sc ψ) (y : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    alV D.host.d sc (embH (tauE D) δ y) = Complex.exp (-(Real.pi : ℂ) * Complex.I *
      ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) : ℚ) : ℂ)) := by
  have hd : 0 < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))
  set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) with htdef
  set M := LinearMap.toMatrix' y with hMdef
  have hMij : ∀ i j, M i j = y (Pi.single j 1) i := by
    intro i j; simp [M, LinearMap.toMatrix'_apply]
  set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs
  have hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ) := by
    intro τ
    simp only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]
    simp only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]
    push_cast
    rw [Finset.sum_comm]
    calc _ = ∑ j, ∑ i, ((Complex.normSq (tauE D τ (M i j)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
      _ = _ := Finset.sum_comm
  have hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2 := by
    intro τ
    rw [map_mul, map_mul, map_pow, map_div₀, map_add, map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD,
      Complex.re_mul_ofReal, re_xi_mul_sq _ hd]
    ring
  have hk' : (t : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ) := by
    have e1 := sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)
    rw [← htdef] at e1
    rw [← e1]
    simp only [hτ]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹ := by
    rw [← Complex.sq_norm]; exact hP.scale
  have hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ := by
    simp only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]
    rw [show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) =
        ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    simp_rw [Complex.normSq_mul, ← Finset.mul_sum]
    simp only [hs, hMij]
    rw [← mul_assoc sc, hsc]
    field_simp
  have hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(t : ℂ) := by rw [hk']; push_cast; ring
  rw [alV, Formalism.L2.Th1.H.alphaQ, hq, hsum]
  congr 1
  ring

/- English proof (translation)
Introduce `D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'`. Establish `h2` using `GlobalTheory.T.semicharacter_sq_eq_one_on_halfA D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'`. Rewrite `h2` using `[alV_embH_eq_exp_trace D ψ θ S T δ sc hP, ← Complex.exp_add]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h2`. Use `⟨-n, ?_⟩` and prove the remaining obligations.

Use `set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) with htdef`. Establish `hpi : (Real.pi : ℂ) * Complex.I ≠ 0` using `mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero`. Establish `: ((t : ℚ) : ℂ) = (((-n : ℤ) : ℚ) : ℂ)`. Apply `mul_left_cancel₀ hpi` to reduce the goal to its premises. Use `push_cast`.

Take the linear combination `(-1/2 : ℂ) * hn`. Conclude with `this.symm` after adjusting the coercions.
-/
theorem trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) := by
  intro D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'
  have h2 := GlobalTheory.T.semicharacter_sq_eq_one_on_halfA D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'
  rw [alV_embH_eq_exp_trace D ψ θ S T δ sc hP, ← Complex.exp_add] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨-n, ?_⟩
  set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) with htdef
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
  have : ((t : ℚ) : ℂ) = (((-n : ℤ) : ℚ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination (-1/2 : ℂ) * hn
  exact_mod_cast this.symm
end GlobalTheory.TraceInt
