import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShapeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirstStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchangeStatement

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

/- English proof (translation)
Take `⟨L₀, h₀, x, hx, hu⟩` from `hρ`. Set `L' : Lev g N` to `{ L₀ with s := L.s, k := L.k, hk := L.hk }`. Establish `hs : L'.sharp = false` using `h₀`. Rewrite using `[GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L' (hL.trans hs.symm) rfl rfl]`. Take `⟨a1, a2, a3, a4, -⟩` from `GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L'`.

Take `⟨-, -, -, h⟩` from `GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L'.Mem L'.chi a1 a2 a3 a4`. Use `h 1 (fun _ => x) (linearIndependent_unique_iff.2 hx) ?_` and prove the remaining obligations. Introduce `i u hm`. Establish `hchi : L'.chi u = L₀.chi u`. Simplify using `only [Lev.chi, Lev.Edge, hs, h₀, Bool.false_eq_true, if_false]`.

Both sides reduce to the same expression. Rewrite using `[hchi]`. Conclude with `hu u hm.1`.
-/
theorem one_le_rk_of_not_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (L : Lev g N)
    (hL : L.sharp = false) : 1 ≤ rk ρ L.e := by
  obtain ⟨L₀, h₀, x, hx, hu⟩ := hρ
  let L' : Lev g N := { L₀ with s := L.s, k := L.k, hk := L.hk }
  have hs : L'.sharp = false := h₀
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L' (hL.trans hs.symm) rfl rfl]
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L'
  obtain ⟨-, -, -, h⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L'.Mem L'.chi a1 a2 a3 a4
  refine h 1 (fun _ => x) (linearIndependent_unique_iff.2 hx) ?_
  intro i u hm
  have hchi : L'.chi u = L₀.chi u := by
    simp only [Lev.chi, Lev.Edge, hs, h₀, Bool.false_eq_true, if_false]
    rfl
  rw [hchi]
  exact hu u hm.1

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => exact fun L h1 h2 => GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first g N M ρ hρ L h1 h2`. Consider the case `succ s ih`. Introduce `L h1 h2`. Establish `hk : s + L.k < N` using `by have := L.hk; omega`.

Set `L' : Lev g N` to `{ L with s := s, hk := hk }`. Establish `h3` using `ih L' h1 rfl`. Establish `h4` using `GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange g N M ρ L L' h1 h1 rfl h2`. Conclude with `h3.trans (by exact_mod_cast h4)`.
-/
theorem rk_lower_of_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (s : ℕ) :
    ∀ L : Lev g N, L.sharp = true → L.s = s → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  induction s with
  | zero => exact fun L h1 h2 => GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first g N M ρ hρ L h1 h2
  | succ s ih =>
    intro L h1 h2
    have hk : s + L.k < N := by have := L.hk; omega
    let L' : Lev g N := { L with s := s, hk := hk }
    have h3 := ih L' h1 rfl
    have h4 := GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange g N M ρ L L' h1 h1 rfl h2
    exact h3.trans (by exact_mod_cast h4)

/- English proof (translation)
Introduce `g _ N M _ _ _ ρ hρ L`. Distinguish the cases in `h : L.sharp = true`. Rewrite using `[if_pos h]`. Conclude with `rk_lower_of_sharp g N M ρ hρ L.s L h rfl`. Rewrite using `[if_neg h, pow_zero, mul_one]`.

Establish `h1 : (1 : ℝ) ≤ rk ρ L.e`. Conclude with `one_le_rk_of_not_sharp g N M ρ hρ L (by simpa using h)` after adjusting the coercions. Establish `h2 : (0 : ℝ) ≤ 1 / (g : ℝ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rk_lev_lower : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  intro g _ N M _ _ _ ρ hρ L
  by_cases h : L.sharp = true
  · rw [if_pos h]
    exact rk_lower_of_sharp g N M ρ hρ L.s L h rfl
  · rw [if_neg h, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ rk ρ L.e := by
      exact_mod_cast one_le_rk_of_not_sharp g N M ρ hρ L (by simpa using h)
    have h2 : (0 : ℝ) ≤ 1 / (g : ℝ) := by positivity
    linarith

end GlobalTheory.BadShare
