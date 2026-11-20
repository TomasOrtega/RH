import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelIdempotentLowerBoundGenericStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterPropsStatement

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Introduce `g hg N L τ hτ f hf`. Take `⟨V, hV, hchar, hgen, hdim⟩` from `hτ.2 f hf`. Take `⟨h1, hmul, hc1, hcmul, -⟩` from `GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L`. Take `⟨hproj, he1, -, -⟩` from `GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) V V.ρ L.Mem L.chi h1 hmul hc1 hcmul`. Establish `hz` using `(GlobalTheory.T.centralIdempotent_irreducible_character_props (GG g N) V).2.2.2 L.e hproj.1`.

Establish `hT : 0 < torusCard g f` using `((GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf).1`. Establish `hr` using `GlobalTheory.T.rank_levelIdempotent_lower_bound_generic g N V V.ρ hgen L`. Establish `hJ` using `GlobalTheory.T.card_levelDatum_group_mul_pow g N L`. Establish `hG` using `GlobalTheory.T.card_generalLinearGroup_primeField g N`. Establish `hGpos : 0 < Fintype.card (GG g N)` using `Fintype.card_pos`.

Establish `hgpos : 0 < g` using `hg.out.pos`. Use `set k : ℕ := (if L.sharp = true then L.k else 0) with hk`. Rewrite `hG` using `[← hJ, ← hdim]`. Establish `he : L.e 1 = ((Nat.card {u // L.Mem u} : ℂ))⁻¹` using `he1`. Use `set J : ℕ := Nat.card {u // L.Mem u}`.

Use `set d : ℕ := Module.finrank ℂ V`. Use `set T : ℕ := torusCard g f`. Use `set r : ℕ := rk V.ρ L.e`. Establish `hJ0 : J ≠ 0`. Introduce `h`.

Rewrite `hGpos` using `[hG, h]`. Simplify using `at hGpos`. Establish `hd0 : d ≠ 0`. Introduce `h`. Rewrite `hGpos` using `[hG, h]`.

Simplify using `at hGpos`. Use `⟨(r : ℝ) / ((g : ℝ) ^ k * (T : ℝ)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hchar, hz, he, hG]`. Establish `a1 : (J : ℂ) ≠ 0` using `by exact_mod_cast hJ0`. Establish `a2 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd0`.

Establish `a3 : (T : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`. Establish `a4 : (g : ℂ) ≠ 0` using `by exact_mod_cast hgpos.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `a3 : (0 : ℝ) < T` using `by exact_mod_cast hT`.

Establish `a4 : (0 : ℝ) < (g : ℝ) ^ k` using `by positivity`. Rewrite using `[le_div_iff₀ (mul_pos a4 a3)]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ r := hr`.
-/
theorem series_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  intro g hg N L τ hτ f hf
  obtain ⟨V, hV, hchar, hgen, hdim⟩ := hτ.2 f hf
  obtain ⟨h1, hmul, hc1, hcmul, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  obtain ⟨hproj, he1, -, -⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) V V.ρ L.Mem L.chi h1 hmul hc1 hcmul
  have hz := (GlobalTheory.T.centralIdempotent_irreducible_character_props (GG g N) V).2.2.2 L.e hproj.1
  have hT : 0 < torusCard g f := ((GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf).1
  have hr := GlobalTheory.T.rank_levelIdempotent_lower_bound_generic g N V V.ρ hgen L
  have hJ := GlobalTheory.T.card_levelDatum_group_mul_pow g N L
  have hG := GlobalTheory.T.card_generalLinearGroup_primeField g N
  have hGpos : 0 < Fintype.card (GG g N) := Fintype.card_pos
  have hgpos : 0 < g := hg.out.pos
  set k : ℕ := (if L.sharp = true then L.k else 0) with hk
  rw [← hJ, ← hdim] at hG
  have he : L.e 1 = ((Nat.card {u // L.Mem u} : ℂ))⁻¹ := he1
  set J : ℕ := Nat.card {u // L.Mem u}
  set d : ℕ := Module.finrank ℂ V
  set T : ℕ := torusCard g f
  set r : ℕ := rk V.ρ L.e
  have hJ0 : J ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  have hd0 : d ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  refine ⟨(r : ℝ) / ((g : ℝ) ^ k * (T : ℝ)), ?_, ?_⟩
  · rw [← hchar, hz, he, hG]
    have a1 : (J : ℂ) ≠ 0 := by exact_mod_cast hJ0
    have a2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have a3 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have a4 : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  · have a3 : (0 : ℝ) < T := by exact_mod_cast hT
    have a4 : (0 : ℝ) < (g : ℝ) ^ k := by positivity
    rw [le_div_iff₀ (mul_pos a4 a3)]
    calc (1 - 1 / (g : ℝ)) * (T : ℝ)⁻¹ * ((g : ℝ) ^ k * T) = (1 - 1 / (g : ℝ)) * (g : ℝ) ^ k := by
          field_simp
      _ ≤ r := hr

end GlobalTheory.BadShare
