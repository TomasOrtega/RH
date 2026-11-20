import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelUnitDiscriminantAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortOfSixUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCubeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortTwistFourMulAddOneStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LocAll

/- English proof (translation)
Take `⟨C, h1, h2, h3, h4, h5, h6⟩` from `h`. Conclude with `⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩`.
-/
theorem modelAt_of_val {V : ValuationSubring ℂ} {F : IntermediateField ℚ ℂ} {W : WeierstrassCurve ℂ} {D D' : ℂ}
    (h : ModelAt V F W D) (hv : V.valuation D = V.valuation D') : ModelAt V F W D' := by
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))`. Conclude with `hz ▸ z.2`.
-/
theorem mem_of_isIntegral (V : ValuationSubring ℂ) {y : ℂ} (hy : IsIntegral ℤ y) : y ∈ V := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))
  exact hz ▸ z.2

/- English proof (translation)
Simplify using `only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem short_Δ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).Δ =
    d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/- English proof (translation)
Simplify using `only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem short_c₄ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).c₄ =
    d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

end GlobalTheory.CMModel.LocAll

open GlobalTheory.CMModel.LocAll in

/- English proof (translation)
Introduce `p F L t hp h4 h3 hD hsq V`. Establish `h27 : (27 : ℂ) ∈ F` using `by simpa using F.algebraMap_mem (27 : ℚ)`. Establish `h4F : (4 : ℂ) ∈ F` using `by simpa using F.algebraMap_mem (4 : ℚ)`. Establish `hg2 : -L.g₂ / 4 ∈ F` using `div_mem (neg_mem hD.g₂_mem) h4F`. Establish `hg3 : -L.g₃ / 4 ∈ F` using `div_mem (neg_mem hD.g₃_mem) h4F`.

Establish `hpF : (p : ℂ) ∈ F` using `by simpa using F.algebraMap_mem (p : ℚ)`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Distinguish the cases in `hv : V.valuation (p : ℂ) = 1`. Establish `hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1` using `GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p p F L t hp h4 h3 hD hsq V hv split_ifs with h8`. Establish `hk` using `GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood`.

Establish `e : (4 * ((0 : ℤ) : ℂ) + 1) = 1` using `by simp`. Rewrite `hk` using `[e]`. Conclude with `modelAt_of_val hk (by simp [hv])`. Take `⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m` from `⟨(p + 1) / 4, by omega⟩`. Establish `hk` using `GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood`.

Establish `hmC : (p : ℂ) + 1 = 4 * m` using `by exact_mod_cast hm`. Establish `e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ)` using `by push_cast; linear_combination hmC`. Rewrite `hk` using `[e]`. Conclude with `modelAt_of_val hk (by simp [hv])`. Establish `h6 : V.valuation (6 : ℂ) = 1`.

Establish `hc : Nat.Coprime p 6`. Establish `h2 : Nat.Coprime p 2` using `(Nat.coprime_primes hp Nat.prime_two).2 (by omega)`. Establish `h3' : Nat.Coprime p 3` using `(Nat.coprime_primes hp Nat.prime_three).2 (by omega)`. Simplify using `using Nat.Coprime.mul_right h2 h3'`. Break down `GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h` into its components or cases.

Conclude with `absurd h hv`. Conclude with `h` after adjusting the coercions. Take `⟨A, hAF, hA0, hA⟩` from `GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V`. Establish `hsq8` using `GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD`. Establish `hΔF : (latticeCurve L).Δ ∈ F`.

Rewrite using `[latticeCurve_Δ]`. Conclude with `sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))`. Take `⟨u, huF, hu0, hu⟩` from `GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq (latticeCurve_Δ_ne_zero L) hA0 hA hsq8`. Establish `him : (sqrtNegNat p).im ≠ 0`. Simplify using `[sqrtNegNat]`.

Conclude with `hp.pos.ne'`. Establish `hj : (latticeCurve L).j ∈ V` using `mem_of_isIntegral V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul him)`. Establish `hjΔ` using `GlobalTheory.j_mul_Δ (latticeCurve L)`. Establish `hDV : -(p : ℂ) ^ 3 ∈ V` using `neg_mem (pow_mem (natCast_mem V p) 3)`. Establish `hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3` using `by simp`.

Use `set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd`. Use `show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)`. Establish `hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3`. Rewrite using `[short_Δ, short_c₄]`. Rewrite using `[show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]`.

Take the linear combination `d ^ 6 * hjΔ`. Distinguish the cases in `h8 : p % 8 = 3`. Establish `hd1 : d = 1` using `by rw [hd, if_pos h8]`. Rewrite `hu` using `[if_pos h8]`. Use `GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_` and prove the remaining obligations.

Rewrite using `[short_Δ, hvD, hd1, one_pow, one_mul]`. Conclude with `hu`. Establish `hdp : d = -(p : ℂ)` using `by rw [hd, if_neg h8]`. Rewrite `hu` using `[if_neg h8]`. Use `GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_` and prove the remaining obligations.

Rewrite using `[short_Δ, hvD, hdp]`. Express the relevant statement in the definitionally equal form `V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)`. Rewrite using `[map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]`. Rewrite using `[show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add], show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]`. The two sides agree by associativity and commutativity.
-/
theorem GlobalTheory.CMModel.twist_modelAt_all : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  intro p F L t hp h4 h3 hD hsq V
  have h27 : (27 : ℂ) ∈ F := by simpa using F.algebraMap_mem (27 : ℚ)
  have h4F : (4 : ℂ) ∈ F := by simpa using F.algebraMap_mem (4 : ℚ)
  have hg2 : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) h4F
  have hg3 : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) h4F
  have hpF : (p : ℂ) ∈ F := by simpa using F.algebraMap_mem (p : ℚ)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  by_cases hv : V.valuation (p : ℂ) = 1
  · have hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1 := GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p p F L t hp h4 h3 hD hsq V hv
    split_ifs with h8
    · have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood
      have e : (4 * ((0 : ℤ) : ℂ) + 1) = 1 := by simp
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
      have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood
      have hmC : (p : ℂ) + 1 = 4 * m := by exact_mod_cast hm
      have e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ) := by push_cast; linear_combination hmC
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
  · have h6 : V.valuation (6 : ℂ) = 1 := by
      have hc : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
        have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
        simpa using Nat.Coprime.mul_right h2 h3'
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h
      · exact absurd h hv
      · exact_mod_cast h
    obtain ⟨A, hAF, hA0, hA⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V
    have hsq8 := GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD
    have hΔF : (latticeCurve L).Δ ∈ F := by
      rw [latticeCurve_Δ]
      exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))
    obtain ⟨u, huF, hu0, hu⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq
      (latticeCurve_Δ_ne_zero L) hA0 hA hsq8
    have him : (sqrtNegNat p).im ≠ 0 := by
      simp [sqrtNegNat]
      exact hp.pos.ne'
    have hj : (latticeCurve L).j ∈ V := mem_of_isIntegral V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul him)
    have hjΔ := GlobalTheory.j_mul_Δ (latticeCurve L)
    have hDV : -(p : ℂ) ^ 3 ∈ V := neg_mem (pow_mem (natCast_mem V p) 3)
    have hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3 := by simp
    set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd
    show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)
    have hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ =
        (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3 := by
      rw [short_Δ, short_c₄]
      rw [show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]
      linear_combination d ^ 6 * hjΔ
    by_cases h8 : p % 8 = 3
    · have hd1 : d = 1 := by rw [hd, if_pos h8]
      rw [if_pos h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_
      rw [short_Δ, hvD, hd1, one_pow, one_mul]
      exact hu
    · have hdp : d = -(p : ℂ) := by rw [hd, if_neg h8]
      rw [if_neg h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_
      rw [short_Δ, hvD, hdp]
      change V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)
      rw [map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]
      rw [show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add],
        show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]
      ac_rfl
