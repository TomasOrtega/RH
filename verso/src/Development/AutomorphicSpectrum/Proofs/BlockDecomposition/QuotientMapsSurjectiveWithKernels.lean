import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXiStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

/- English proof (translation)
Establish `h : A.dxi0 0 = 1` using `Subtype.ext (by simp [PAlg.dxi0, dpw])`. Rewrite using `[PAlg.dxi, h, map_one]`.
-/
theorem dxi_zero {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) : A.dxi n 0 = 1 := by
  have h : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])
  rw [PAlg.dxi, h, map_one]

/- English proof (translation)
Establish `h0 : z ∈ A.Fil n 0`. Rewrite using `[((GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.2.2.1 n)]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨w, hw⟩` from `(GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).1 z h0`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Simplify `hw` using `[dxi_zero]`.
-/
theorem exists_toAcr_sub_mem {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (z : A.Acr n) :
    ∃ w : A.W, z - A.toAcr n w ∈ A.Fil n 1 := by
  have h0 : z ∈ A.Fil n 0 := by
    rw [((GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.2.2.1 n)]; trivial
  obtain ⟨w, hw⟩ := (GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).1 z h0
  refine ⟨w, ?_⟩
  simpa [dxi_zero] using hw

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).2 w`. Simplify `h` using `[dxi_zero]`.
-/
theorem toAcr_mem_fil_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (w : A.W) :
    A.toAcr n w ∈ A.Fil n 1 ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  have h := (GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).2 w
  simpa [dxi_zero] using h

/- English proof (translation)
Introduce `y`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨w, hw⟩` from `exists_toAcr_sub_mem A n z`. Conclude with `⟨A.th w, (Ideal.Quotient.eq.2 hw).symm⟩`.
-/
theorem uToQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  exact ⟨A.th w, (Ideal.Quotient.eq.2 hw).symm⟩

/- English proof (translation)
Use extensionality with `x`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Express the relevant statement in the definitionally equal form `A.th w ∈ _ ↔ A.th w ∈ _`. Rewrite using `[RingHom.mem_ker, uToQ_th, Ideal.Quotient.eq_zero_iff_mem, toAcr_mem_fil_iff]`.
-/
theorem ker_uToQ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} := by
  ext x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change A.th w ∈ _ ↔ A.th w ∈ _
  rw [RingHom.mem_ker, uToQ_th, Ideal.Quotient.eq_zero_iff_mem, toAcr_mem_fil_iff]

/- English proof (translation)
Introduce `y`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨w, hw⟩` from `exists_toAcr_sub_mem A n z`. Establish `h : z - A.toAcr n w ∈ A.PFil n` using `Ideal.mem_sup_right hw`. Conclude with `⟨A.th w, (Ideal.Quotient.eq.2 h).symm⟩`.
-/
theorem uToPQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToPQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  have h : z - A.toAcr n w ∈ A.PFil n := Ideal.mem_sup_right hw
  exact ⟨A.th w, (Ideal.Quotient.eq.2 h).symm⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Express the relevant statement in the definitionally equal form `A.th w ∈ _`. Establish `h : A.toAcr n w ∈ A.PFil n` using `Ideal.Quotient.eq_zero_iff_mem.1 hx`.

Take `⟨u, hu, z, hz, e⟩` from `Submodule.mem_sup.1 h`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Take `⟨w', hw'⟩` from `exists_toAcr_sub_mem A n a`. Establish `h1 : A.toAcr n (w - (l : A.W) * w') ∈ A.Fil n 1`. Establish `e' : A.toAcr n (w - (l : A.W) * w') = (a - A.toAcr n w') * (l : A.Acr n) + z`.

Rewrite using `[map_sub, map_mul, map_natCast, ← e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `add_mem (Ideal.mul_mem_right _ _ hw') hz`. Establish `h2` using `(toAcr_mem_fil_iff A n _).1 h1`.

Establish `h3 : A.th (w - (l : A.W) * w') ∈ Ideal.span {(l : A.U)}` using `Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ hn) h2`. Establish `h4 : A.th w = A.th (w - (l : A.W) * w') + (l : A.U) * A.th w'`. Rewrite using `[map_sub, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`.

Conclude with `add_mem h3 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`. Rewrite using `[Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast, ← map_natCast (Ideal.Quotient.mk (A.PFil n))]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))`.
-/
theorem ker_uToPQ {l : ℕ} [Fact l.Prime] (A : PAlg l) {n : ℕ} (hn : n ≠ 0) :
    RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.th w ∈ _
    have h : A.toAcr n w ∈ A.PFil n := Ideal.Quotient.eq_zero_iff_mem.1 hx
    obtain ⟨u, hu, z, hz, e⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨w', hw'⟩ := exists_toAcr_sub_mem A n a
    have h1 : A.toAcr n (w - (l : A.W) * w') ∈ A.Fil n 1 := by
      have e' : A.toAcr n (w - (l : A.W) * w') = (a - A.toAcr n w') * (l : A.Acr n) + z := by
        rw [map_sub, map_mul, map_natCast, ← e]; ring
      rw [e']
      exact add_mem (Ideal.mul_mem_right _ _ hw') hz
    have h2 := (toAcr_mem_fil_iff A n _).1 h1
    have h3 : A.th (w - (l : A.W) * w') ∈ Ideal.span {(l : A.U)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ hn) h2
    have h4 : A.th w = A.th (w - (l : A.W) * w') + (l : A.U) * A.th w' := by
      rw [map_sub, map_mul, map_natCast]; ring
    rw [h4]
    exact add_mem h3 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast,
      ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

/- English proof (translation)
Introduce `A n` and use `⟨uToQ_surjective A n, ker_uToQ A n, uToPQ_surjective A n, fun hn => ker_uToPQ A hn⟩`.
-/
theorem uToQ_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧
    (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) :=
  fun A n => ⟨uToQ_surjective A n, ker_uToQ A n, uToPQ_surjective A n, fun hn => ker_uToPQ A hn⟩

end GlobalTheory.CompanionTheory.Untilt
