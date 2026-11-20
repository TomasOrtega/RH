import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `N s hN B`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `hφ : ((N.totient : ℂ)) ≠ 0` using `by exact_mod_cast (Nat.totient_pos.mpr hN).ne'`. Establish `h1` using `DirichletCharacter.sum_characters_eq ℂ (B : ZMod N)`. Establish `h2` using `DirichletCharacter.sum_characters_eq ℂ (-(B : ZMod N))`.

Establish `h3 : ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N) = ∑ ν : DirichletCharacter ℂ N, ν (-(B : ZMod N))`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul, neg_one_mul]`. Establish `h4 : (-(B : ZMod N) = 1) ↔ ((B : ZMod N) = -1)` using `neg_eq_iff_eq_neg`. Establish `hsum : ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B = ∑ ν : DirichletCharacter ℂ N, ν (B : ZMod N) - s * ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N)`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Simplify using `only [ch]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, h3, h1, h2]`.

Simplify using `only [tw2, h4]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem eisensteinTameWeightSecond_eq_character_sum :
    ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ,
      tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  intro N s hN B
  haveI : NeZero N := ⟨hN.ne'⟩
  have hφ : ((N.totient : ℂ)) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have h1 := DirichletCharacter.sum_characters_eq ℂ (B : ZMod N)
  have h2 := DirichletCharacter.sum_characters_eq ℂ (-(B : ZMod N))
  have h3 : ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N)
      = ∑ ν : DirichletCharacter ℂ N, ν (-(B : ZMod N)) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← map_mul, neg_one_mul]
  have h4 : (-(B : ZMod N) = 1) ↔ ((B : ZMod N) = -1) := neg_eq_iff_eq_neg
  have hsum : ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B
      = ∑ ν : DirichletCharacter ℂ N, ν (B : ZMod N)
        - s * ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [ch]
    ring
  rw [hsum, h3, h1, h2]
  simp only [tw2, h4]
  field_simp
  split_ifs <;> ring

end GlobalTheory.EisM
