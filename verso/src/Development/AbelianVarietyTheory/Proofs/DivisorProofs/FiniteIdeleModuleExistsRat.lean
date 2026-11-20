import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.ModFRat

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  intro E _ _ y
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), ?_⟩
  have h := MonoidHom.map_finprod_of_injective ((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ) Rat.cast_injective
    (fun v : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))))
  simp only [MonoidHom.coe_coe, Rat.coe_castHom, Rat.cast_zpow, Rat.cast_natCast] at h
  rw [h]
  rfl

end GlobalTheory.CMVal.ModFRat
