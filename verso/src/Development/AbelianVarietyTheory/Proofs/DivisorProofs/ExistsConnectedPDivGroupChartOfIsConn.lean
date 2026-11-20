import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankOmegaLeFinrankFrobeniusKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqZeroOfEvAEqZeroOfLeFinrankStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.aeval_X]`. Simplify using `only [MvPolynomial.coe_X, map_X]`. Conclude with `GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i`.
-/
theorem evA_comp_coe {K A : Type} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
    (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) :
    (evA K x hx).comp (MvPolynomial.coeToMvPowerSeries.algHom K) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.aeval_X]
  simp only [MvPolynomial.coe_X, map_X]
  exact GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i

/- English proof (translation)
Take `⟨x, hres, haug, hsurj⟩` from `GlobalTheory.T.exists_coordinates_generate_connected_levels p K h G hG`. Establish `hmem : ∀ n i, x n i ∈ augIdeal K (G.A n)` using `fun n i => by`. Simplify using `[augIdeal, haug n i]`. Establish `hnil : ∀ n i, IsNilpotent (x n i)` using `fun n i => hG n _ (hmem n i)`. Use `⟨_, ⟨{ x := x, nil := hnil, res := hres, aug := haug, presents := ⟨?_, ?_⟩ }⟩⟩` and prove the remaining obligations.

Introduce `n a`. Take `⟨P, hP⟩` from `hsurj n a`. Use `⟨(P : MvPowerSeries _ K), ?_⟩` and prove the remaining obligations. Use `congrArg (fun φ => φ P) (evA_comp_coe (x n) (hnil n))` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply] at this`.

Rewrite using `[← hP, ← this]`. Both sides reduce to the same expression. Introduce `N`. Use `⟨N, fun f hf α hα => ?_⟩` and prove the remaining obligations. Establish `hq : ∀ i, x N i ^ (p ^ N) ∈ frobKerIdeal (p ^ N) K (G.A N)` using `fun i => pow_mem_frobKerIdeal (hmem N i)`.

Conclude with `GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' K (G.A N) _ (p ^ N) (x N) (hnil N) _ (hsurj N) hq (GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel p K h G N) f hf α (lt_of_lt_of_le hα (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)`.
-/
theorem exists_chart_of_isConn (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) : ∃ d, Nonempty (Chart G d) := by
  obtain ⟨x, hres, haug, hsurj⟩ := GlobalTheory.T.exists_coordinates_generate_connected_levels p K h G hG
  have hmem : ∀ n i, x n i ∈ augIdeal K (G.A n) := fun n i => by
    simp [augIdeal, haug n i]
  have hnil : ∀ n i, IsNilpotent (x n i) := fun n i => hG n _ (hmem n i)
  refine ⟨_, ⟨{ x := x, nil := hnil, res := hres, aug := haug, presents := ⟨?_, ?_⟩ }⟩⟩
  · intro n a
    obtain ⟨P, hP⟩ := hsurj n a
    refine ⟨(P : MvPowerSeries _ K), ?_⟩
    have := congrArg (fun φ => φ P) (evA_comp_coe (x n) (hnil n))
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply] at this
    rw [← hP, ← this]
    rfl
  · intro N
    refine ⟨N, fun f hf α hα => ?_⟩
    have hq : ∀ i, x N i ^ (p ^ N) ∈ frobKerIdeal (p ^ N) K (G.A N) :=
      fun i => pow_mem_frobKerIdeal (hmem N i)
    exact GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' K (G.A N) _ (p ^ N) (x N) (hnil N) _ (hsurj N) hq
      (GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel p K h G N) f hf α
      (lt_of_lt_of_le hα (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)

end GlobalTheory.Katz
