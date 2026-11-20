import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisorStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

/- English proof (translation)
The claim follows from `Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩`.
-/
theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

/- English proof (translation)
Introduce `l _ A r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `z _`. Rewrite using `[(GlobalTheory.T.crystalline_filtration_multiplicative A).1]`.

Conclude with `Submodule.mem_top`. Consider the case `succ r ih`. Introduce `z hz`. Establish `hzr : z ∈ A.Fil0 r` using `ih z (Fil0_succ_le A r hz)`. Take `⟨h1, h2, -⟩` from `GlobalTheory.T.crystalline_graded_pieces_description A r`.

Take `⟨w, hw⟩` from `h1 z hzr`. Establish `hlw : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r ∈ A.Fil0 (r + 1)`. Establish `e : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r = (l : A.Acr0) * z - (l : A.Acr0) * (z - algebraMap A.W A.Acr0 w * A.dxi0 r)`. Rewrite using `[map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `sub_mem hz (Ideal.mul_mem_left _ _ hw)`. Establish `hmem : (l : A.W) * w ∈ Ideal.span {A.xi}` using `(h2 _).1 hlw`. Establish `hth : (l : A.U) * A.th w = 0`. Rewrite using `[← map_natCast A.th, ← map_mul]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hmem`. Establish `hth0 : A.th w = 0` using `(mem_nonZeroDivisors_iff_left.1 (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1) _ hth`. Establish `hwx : w ∈ Ideal.span {A.xi}` using `Ideal.Quotient.eq_zero_iff_mem.1 hth0`. Use `add_mem hw ((h2 w).2 hwx)` as an intermediate fact. Simplify using `using this`.
-/
theorem crystalline_filtration_l_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0),
    (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  intro l _ A r
  induction r with
  | zero =>
    intro z _
    rw [(GlobalTheory.T.crystalline_filtration_multiplicative A).1]
    exact Submodule.mem_top
  | succ r ih =>
    intro z hz
    have hzr : z ∈ A.Fil0 r := ih z (Fil0_succ_le A r hz)
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.crystalline_graded_pieces_description A r
    obtain ⟨w, hw⟩ := h1 z hzr
    have hlw : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r ∈ A.Fil0 (r + 1) := by
      have e : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r =
          (l : A.Acr0) * z - (l : A.Acr0) * (z - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
        rw [map_mul, map_natCast]; ring
      rw [e]
      exact sub_mem hz (Ideal.mul_mem_left _ _ hw)
    have hmem : (l : A.W) * w ∈ Ideal.span {A.xi} := (h2 _).1 hlw
    have hth : (l : A.U) * A.th w = 0 := by
      rw [← map_natCast A.th, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
    have hth0 : A.th w = 0 :=
      (mem_nonZeroDivisors_iff_left.1 (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1) _ hth
    have hwx : w ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hth0
    have := add_mem hw ((h2 w).2 hwx)
    simpa using this

end GlobalTheory.CompanionTheory.PerfFil
