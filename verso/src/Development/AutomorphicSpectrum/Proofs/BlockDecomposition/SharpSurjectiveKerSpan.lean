import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `y`. Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Conclude with `⟨x.coeff 0, A.sharpMap_coeff x⟩`.

Use extensionality with `a`. Rewrite using `[RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[A.sharpMap_eq, Ideal.Quotient.eq_zero_iff_mem, pow_one]`.

Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 h`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Establish `h0 : A.th (WittVector.teichmuller l a - y * (l : A.W)) = 0`. Rewrite using `[map_sub, map_mul, map_natCast]`. Conclude with `sub_eq_zero.2 hu.symm`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Establish `h1` using `congrArg (WittVector.constantCoeff : A.W →+* A.A) hc`. Rewrite `h1` using `[map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, A.xi_coeff_zero]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨-c.coeff 0, by rw [← h1, neg_mul, mul_neg]⟩`. Introduce `h`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[map_mul, A.sharpMap_eq A.pi, A.sharp_pi, Ideal.Quotient.eq_zero_iff_mem.2 (by`. Rewrite using `[pow_one]`. Conclude with `Ideal.mem_span_singleton_self _), mul_zero]`.
-/
theorem sharp_map_surjective_ker {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  constructor
  · intro y
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, A.sharpMap_coeff x⟩
  · ext a
    rw [RingHom.mem_ker]
    constructor
    · intro h
      rw [A.sharpMap_eq, Ideal.Quotient.eq_zero_iff_mem, pow_one] at h
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
      have h0 : A.th (WittVector.teichmuller l a - y * (l : A.W)) = 0 := by
        rw [map_sub, map_mul, map_natCast]
        exact sub_eq_zero.2 hu.symm
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      have h1 := congrArg (WittVector.constantCoeff : A.W →+* A.A) hc
      rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, A.xi_coeff_zero] at h1
      exact Ideal.mem_span_singleton'.2 ⟨-c.coeff 0, by rw [← h1, neg_mul, mul_neg]⟩
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      rw [map_mul, A.sharpMap_eq A.pi, A.sharp_pi,
        Ideal.Quotient.eq_zero_iff_mem.2 (by
          rw [pow_one]; exact Ideal.mem_span_singleton_self _), mul_zero]

end GlobalTheory.CompanionTheory.Untilt
