import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturatedStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

namespace GradedFiltration

/- English proof (translation)
The claim follows from `Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩`.
-/
theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨r, le_rfl, rfl⟩`.
-/
theorem dividedXi_mem_filtration {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.dxi0 r ∈ A.Fil0 r :=
  Ideal.subset_span ⟨r, le_rfl, rfl⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises. Apply `GlobalTheory.T.crystalline_filtration_saturated A r` to reduce the goal to its premises.

Rewrite `h` using `[pow_succ', mul_assoc, mul_comm, mul_assoc, mul_comm z, ← mul_assoc, mul_comm _ (l : A.Acr0), mul_assoc]`. Then use the resulting hypothesis.
-/
theorem mem_filtration_of_prime_pow_mul {l : ℕ} [Fact l.Prime] (A : PAlg l) (r n : ℕ) (z : A.Acr0)
    (h : (l : A.Acr0) ^ n * z ∈ A.Fil0 r) : z ∈ A.Fil0 r := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply GlobalTheory.T.crystalline_filtration_saturated A r
    rwa [pow_succ', mul_assoc, mul_comm, mul_assoc, mul_comm z, ← mul_assoc, mul_comm _ (l : A.Acr0), mul_assoc] at h

/- English proof (translation)
The claim follows from `Ideal.Quotient.mk_surjective`.
-/
theorem mkAcr_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

end GradedFiltration

open GradedFiltration in

/- English proof (translation)
Introduce `l _ A n r`. Establish `hF : ∀ s, A.Fil n s = (A.Fil0 s).map (A.mkAcr n)` using `(GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.1 n`. Establish `hsurj` using `mkAcr_surjective A n`. Establish `hto : ∀ w, A.toAcr n w = A.mkAcr n (algebraMap A.W A.Acr0 w)` using `fun _ => rfl`. Establish `hdx : A.dxi n r = A.mkAcr n (A.dxi0 r)` using `rfl`.

Use `⟨fun z hz => ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite `hz` using `[hF, Ideal.mem_map_iff_of_surjective _ hsurj]`. Take `⟨z0, hz0, rfl⟩` from `hz`. Take `⟨w, hw⟩` from `(GlobalTheory.T.crystalline_graded_pieces_description A r).1 z0 hz0`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Rewrite using `[hF, hto, hdx, ← map_mul, ← map_sub]`. Conclude with `Ideal.mem_map_of_mem _ hw`. Rewrite `h` using `[hF, Ideal.mem_map_iff_of_surjective _ hsurj, hto, hdx, ← map_mul]`. Take `⟨z', hz', e⟩` from `h`. Establish `hd : algebraMap A.W A.Acr0 w * A.dxi0 r - z' ∈ Ideal.span {(l : A.Acr0) ^ n}`.

Apply `Ideal.Quotient.eq.1` to reduce the goal to its premises. Conclude with `e.symm`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton.1 hd`. Establish `hzr : z ∈ A.Fil0 r`. Apply `mem_filtration_of_prime_pow_mul A r n` to reduce the goal to its premises.

Rewrite using `[← hz]`. Conclude with `sub_mem (Ideal.mul_mem_left _ _ (dividedXi_mem_filtration A r)) (Fil0_succ_le A r hz')`. Take `⟨w', hw'⟩` from `(GlobalTheory.T.crystalline_graded_pieces_description A r).1 z hzr`. Establish `hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi}`. Rewrite using `[← (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1]`.

Establish `: algebraMap A.W A.Acr0 (w - (l : A.W) ^ n * w') * A.dxi0 r = z' + (l : A.Acr0) ^ n * (z - algebraMap A.W A.Acr0 w' * A.dxi0 r)`. Rewrite using `[map_sub, map_mul, map_pow, map_natCast]`. Take the linear combination `hz`. Rewrite using `[this]`. Conclude with `add_mem hz' (Ideal.mul_mem_left _ _ hw')`.

Establish `: A.th w = (l : A.U) ^ n * A.th w'`. Establish `h0 : A.th (w - (l : A.W) ^ n * w') = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hxi`. Rewrite `h0` using `[map_sub, map_mul, map_pow, map_natCast, sub_eq_zero]`. Conclude with `h0`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton.1 h`. Take `⟨w', rfl⟩ : ∃ w', A.th w' = u` from `Ideal.Quotient.mk_surjective u`. Establish `hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi}`. Apply `Ideal.Quotient.eq_zero_iff_mem.1` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `A.th (w - (l : A.W) ^ n * w') = 0`. Rewrite using `[map_sub, map_mul, map_pow, map_natCast, hu, sub_self]`. Establish `h1` using `(GlobalTheory.T.crystalline_graded_pieces_description A r).2.1 _ |>.2 hxi`. Establish `h2 : A.toAcr n (w - (l : A.W) ^ n * w') * A.dxi n r ∈ A.Fil n (r + 1)`. Rewrite using `[hF, hto, hdx, ← map_mul]`.

Conclude with `Ideal.mem_map_of_mem _ h1`. Establish `h3 : A.toAcr n (w - (l : A.W) ^ n * w') = A.toAcr n w`. Rewrite using `[map_sub, map_mul, map_pow, map_natCast, pow_l_acr, zero_mul, sub_zero]`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
theorem graded_mod_pow : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ),
    (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧
    ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  intro l _ A n r
  have hF : ∀ s, A.Fil n s = (A.Fil0 s).map (A.mkAcr n) := (GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.1 n
  have hsurj := mkAcr_surjective A n
  have hto : ∀ w, A.toAcr n w = A.mkAcr n (algebraMap A.W A.Acr0 w) := fun _ => rfl
  have hdx : A.dxi n r = A.mkAcr n (A.dxi0 r) := rfl
  refine ⟨fun z hz => ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨w, hw⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z0 hz0
    refine ⟨w, ?_⟩
    rw [hF, hto, hdx, ← map_mul, ← map_sub]
    exact Ideal.mem_map_of_mem _ hw
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj, hto, hdx, ← map_mul] at h
    obtain ⟨z', hz', e⟩ := h
    have hd : algebraMap A.W A.Acr0 w * A.dxi0 r - z' ∈ Ideal.span {(l : A.Acr0) ^ n} := by
      apply Ideal.Quotient.eq.1
      exact e.symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 hd
    have hzr : z ∈ A.Fil0 r := by
      apply mem_filtration_of_prime_pow_mul A r n
      rw [← hz]
      exact sub_mem (Ideal.mul_mem_left _ _ (dividedXi_mem_filtration A r)) (Fil0_succ_le A r hz')
    obtain ⟨w', hw'⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z hzr
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      rw [← (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1]
      have : algebraMap A.W A.Acr0 (w - (l : A.W) ^ n * w') * A.dxi0 r =
          z' + (l : A.Acr0) ^ n * (z - algebraMap A.W A.Acr0 w' * A.dxi0 r) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hz
      rw [this]
      exact add_mem hz' (Ideal.mul_mem_left _ _ hw')
    have : A.th w = (l : A.U) ^ n * A.th w' := by
      have h0 : A.th (w - (l : A.W) ^ n * w') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxi
      rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at h0
      exact h0
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h
    obtain ⟨w', rfl⟩ : ∃ w', A.th w' = u := Ideal.Quotient.mk_surjective u
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      apply Ideal.Quotient.eq_zero_iff_mem.1
      change A.th (w - (l : A.W) ^ n * w') = 0
      rw [map_sub, map_mul, map_pow, map_natCast, hu, sub_self]
    have h1 := (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1 _ |>.2 hxi
    have h2 : A.toAcr n (w - (l : A.W) ^ n * w') * A.dxi n r ∈ A.Fil n (r + 1) := by
      rw [hF, hto, hdx, ← map_mul]
      exact Ideal.mem_map_of_mem _ h1
    have h3 : A.toAcr n (w - (l : A.W) ^ n * w') = A.toAcr n w := by
      rw [map_sub, map_mul, map_pow, map_natCast, pow_l_acr, zero_mul, sub_zero]
    rwa [h3] at h2

end GlobalTheory.CompanionTheory.PerfFil
