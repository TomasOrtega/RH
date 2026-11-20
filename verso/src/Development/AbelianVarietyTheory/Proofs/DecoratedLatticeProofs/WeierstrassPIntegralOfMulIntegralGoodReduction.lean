import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionSetSubgroup

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

/- English proof (translation)
Introduce `L l _ hl ι h2 h3 hd z N hN hP`. Establish `hg : GlobalTheory.Klein.Good ι L 0`. Use `⟨by omega, by simp, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using h2`. Simplify using `using h3`.

Simplify `hd` using `[map_sub, map_mul, map_pow, map_ofNat]`. Take `⟨-, -, -, G, hG, -⟩` from `GlobalTheory.Klein.not_red_addSubgroup l ι L 0 hg`. Assume the negation of the conclusion as `hc`. Establish `hz : z ∈ G`. Rewrite using `[hG]; intro h; exact hc (by simpa using h.2)`.

Establish `hNz : (N : ℂ) * z ∈ G`. Use `G.nsmul_mem hz N` as an intermediate fact. Simplify `this` using `[nsmul_eq_mul]`. Rewrite `hNz` using `[hG]`. Conclude with `hNz ⟨hN, by simpa using hP⟩`.
-/
theorem integral_of_mul_integral : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  intro L l _ hl ι h2 h3 hd z N hN hP
  have hg : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, by simp, ?_, ?_, ?_⟩
    · simpa using h2
    · simpa using h3
    · simpa [map_sub, map_mul, map_pow, map_ofNat] using hd
  obtain ⟨-, -, -, G, hG, -⟩ := GlobalTheory.Klein.not_red_addSubgroup l ι L 0 hg
  by_contra hc
  have hz : z ∈ G := by
    rw [hG]; intro h; exact hc (by simpa using h.2)
  have hNz : (N : ℂ) * z ∈ G := by
    have := G.nsmul_mem hz N
    simpa [nsmul_eq_mul] using this
  rw [hG] at hNz
  exact hNz ⟨hN, by simpa using hP⟩

end GlobalTheory.Honda
