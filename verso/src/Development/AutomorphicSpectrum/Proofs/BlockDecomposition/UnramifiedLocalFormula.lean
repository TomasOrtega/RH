import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianMatricesModPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSuccStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens Filter Topology

namespace GlobalTheory.CompanionTheory.UnrDens

/- English proof (translation)
Introduce `R _ σ ϖ q ε hR m n hnm S T hS hT`. Establish `hq : (0 : ℝ) < q` using `by exact_mod_cast lt_trans zero_lt_one hR.one_lt`. Establish `hsq : n ^ 2 ≤ 2 * m * n` using `by nlinarith`. Take `⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a` from `⟨_, rfl⟩`. Establish `ha' : a + n ^ 2 = 2 * m * n` using `by omega`.

Establish `hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) = (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[GlobalTheory.T.card_unimodular_hermitian_reps_level_one R σ ϖ q ε hR m n hnm S T hS hT, ha]`.

Simplify using the standard rewrite rules. Consider the case `succ j ih`. Rewrite using `[GlobalTheory.T.unimodular_hermitian_reps_count_succ R σ ϖ q ε hR m n hnm S T hS hT (j + 1) (by omega), ha]`. Use `push_cast`. Rewrite using `[ih, add_mul, one_mul, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdens : ∀ j : ℕ, densAt σ ϖ S T (j + 1) = ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))`. Introduce `j`. Unfold `densAt`. Establish `hM : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n))` using `by show Nat.card (Fin m → Fin n → R ⧸ lev ϖ (j + 1)) = _`.

Rewrite using `[Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1), ← pow_mul, ← pow_mul]`. Put the polynomial expressions in normal form. Rewrite using `[hsol j, GlobalTheory.T.card_hermitian_matrices_mod_pow R σ ϖ q ε hR n (j + 1), hM]`. Establish `he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1) * (m * n))` using `pow_pos hq _`. Use `push_cast`. Rewrite using `[div_eq_iff hpos.ne', ← he, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [Filter.eventually_ge_atTop 1] with k hk`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Conclude with `(hdens j).symm`.
-/
theorem unrFormula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hq : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one hR.one_lt
  have hsq : n ^ 2 ≤ 2 * m * n := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a := ⟨_, rfl⟩
  have ha' : a + n ^ 2 = 2 * m * n := by omega
  have hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) =
      (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a) := by
    intro j
    induction j with
    | zero =>
      rw [GlobalTheory.T.card_unimodular_hermitian_reps_level_one R σ ϖ q ε hR m n hnm S T hS hT, ha]
      simp
    | succ j ih =>
      rw [GlobalTheory.T.unimodular_hermitian_reps_count_succ R σ ϖ q ε hR m n hnm S T hS hT (j + 1) (by omega), ha]
      push_cast
      rw [ih, add_mul, one_mul, pow_add]
      ring
  have hdens : ∀ j : ℕ, densAt σ ϖ S T (j + 1) = ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
    intro j
    unfold densAt
    have hM : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n)) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ (j + 1)) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1), ← pow_mul,
        ← pow_mul]
      ring_nf
    rw [hsol j, GlobalTheory.T.card_hermitian_matrices_mod_pow R σ ϖ q ε hR n (j + 1), hM]
    have he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n) := by
      calc a + j * a + (j + 1) * n ^ 2 = (j + 1) * (a + n ^ 2) := by ring
        _ = (j + 1) * (2 * m * n) := by rw [ha']
        _ = 2 * (j + 1) * (m * n) := by ring
    have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1) * (m * n)) := pow_pos hq _
    push_cast
    rw [div_eq_iff hpos.ne', ← he, pow_add, pow_add]
    ring
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hdens j).symm

end GlobalTheory.CompanionTheory.UnrDens
