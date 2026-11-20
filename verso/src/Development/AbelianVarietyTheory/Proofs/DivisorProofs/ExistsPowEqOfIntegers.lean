import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.PDiv

/- English proof (translation)
Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) hn`. Establish `h1 : v c ^ n ≤ 1`. Rewrite using `[← map_pow, hc]`. Conclude with `hv.map_le_one a`. Take `⟨b, rfl⟩` from `hv.exists_of_le_one ((pow_le_one_iff hn.ne').1 h1)`.

Conclude with `⟨b, hv.hom_inj (by rw [map_pow, hc])⟩`.
-/
theorem exists_pow_eq_of_integers {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {n : ℕ} (hn : 0 < n) (a : O) : ∃ b : O, b ^ n = a := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) hn
  have h1 : v c ^ n ≤ 1 := by
    rw [← map_pow, hc]
    exact hv.map_le_one a
  obtain ⟨b, rfl⟩ := hv.exists_of_le_one ((pow_le_one_iff hn.ne').1 h1)
  exact ⟨b, hv.hom_inj (by rw [map_pow, hc])⟩

/- English proof (translation)
Establish `: IsDomain O` using `hv.hom_inj.isDomain _`. Establish `: ValuationRing O` using `ValuationRing.of_integers v hv`. Establish `hp : (p : O) ≠ 0` using `fun h => by`. Use `congrArg (algebraMap O C) h` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`.

Conclude with `(Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 this)`. Establish `htf : ∀ w : G.omega, (p : O) • w = 0 → w = 0` using `GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective p O G fun n => GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq O _ _ (G.mulP n) (GlobalTheory.T.mulP_mem_sq_counit_ker p O hp Fact.out (exists_pow_eq_of_integers hv (Fact.out : p.Prime).pos) G n)`. Establish `htfk : ∀ (k : ℕ) (w : G.omega), (p : O) ^ k • w = 0 → w = 0` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => intro w hw`.

Rewrite `hw` using `[pow_zero, one_smul]`. Then use the resulting hypothesis. Consider the case `succ k ih => intro w hw; exact htf w (ih _ (by rw [← mul_smul, ← pow_succ, hw]))`. Establish `: Module.Finite O G.omega`. Establish `h` using `Module.Finite.equiv (G.omegaQuotEquiv 1).symm`. Rewrite `h` using `[pow_one]`.

Conclude with `GlobalTheory.finite_of_isHausdorff_of_finite_quotient (Ideal.span {(p : O)}) _`. Establish `: Module.Flat O G.omega`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `w ⟨⟨a, ha⟩, hw⟩`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`.

Establish `: ∃ k, a ∣ (p : O) ^ k` using `by by_contra! hk`. Use `ha0 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) a fun k => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `(ValuationRing.dvd_total _ _).resolve_left (hk k)`. Take `⟨k, c, hc⟩` from `this`.

Establish `hw' : a • w = 0` using `hw`. Conclude with `htfk k w (by rw [hc, mul_comm, mul_smul, hw', smul_zero])`. Establish `: Module.Free O G.omega` using `Module.free_of_flat_of_isLocalRing`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem omega_finite_projective (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) :
    Module.Finite O G.omega ∧ Module.Projective O G.omega := by
  have : IsDomain O := hv.hom_inj.isDomain _
  have : ValuationRing O := ValuationRing.of_integers v hv
  have hp : (p : O) ≠ 0 := fun h => by
    have := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 this)
  have htf : ∀ w : G.omega, (p : O) • w = 0 → w = 0 :=
    GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective p O G fun n => GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq O _ _ (G.mulP n)
      (GlobalTheory.T.mulP_mem_sq_counit_ker p O hp Fact.out (exists_pow_eq_of_integers hv (Fact.out : p.Prime).pos) G n)
  have htfk : ∀ (k : ℕ) (w : G.omega), (p : O) ^ k • w = 0 → w = 0 := fun k => by
    induction k with
    | zero => intro w hw; rwa [pow_zero, one_smul] at hw
    | succ k ih => intro w hw; exact htf w (ih _ (by rw [← mul_smul, ← pow_succ, hw]))
  have : Module.Finite O G.omega := by
    have h := Module.Finite.equiv (G.omegaQuotEquiv 1).symm
    rw [pow_one] at h
    exact GlobalTheory.finite_of_isHausdorff_of_finite_quotient (Ideal.span {(p : O)}) _
  have : Module.Flat O G.omega := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro w ⟨⟨a, ha⟩, hw⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have : ∃ k, a ∣ (p : O) ^ k := by
      by_contra! hk
      refine ha0 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) a fun k => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact (ValuationRing.dvd_total _ _).resolve_left (hk k)
    obtain ⟨k, c, hc⟩ := this
    have hw' : a • w = 0 := hw
    exact htfk k w (by rw [hc, mul_comm, mul_smul, hw', smul_zero])
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.PDiv
