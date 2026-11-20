import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Proceed by induction on `𝔭 using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => simp [extP]`. Consider the case `h₂ x hx`. Rewrite using `[Ideal.isUnit_iff.mp hx]`. Simplify using `only [extP]`.

Simplify using `only [Ideal.map_top, Ideal.absNorm_top, one_pow]`. Consider the case `h₃ a p ha hp ih`. Establish `hpm : p.IsMaximal` using `(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero`. Establish `hq` using `idealPowerSpanBounds.absNorm_extP_eq_sq hK hF hpm`. Simplify using `only [extP] at ih hq ⊢`.

Rewrite using `[Ideal.map_mul, map_mul, map_mul, ih, hq, mul_pow]`.
-/
theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  induction 𝔭 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [extP]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx]
    simp only [extP]
    simp only [Ideal.map_top, Ideal.absNorm_top, one_pow]
  | h₃ a p ha hp ih =>
    have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hq := idealPowerSpanBounds.absNorm_extP_eq_sq hK hF hpm
    simp only [extP] at ih hq ⊢
    rw [Ideal.map_mul, map_mul, map_mul, ih, hq, mul_pow]

/- English proof (translation)
Take `⟨θ, hθ⟩` from `exists_sub_conjO_notMem hK hP`. Rewrite `hc` using `[conjIdeal_eq_comap]`. Conclude with `SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ`.
-/
theorem map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [conjIdeal_eq_comap] at hc
  exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

/- English proof (translation)
Establish `hP'` using `conjIdeal_isMaximal hK hP`. Establish `h1 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P` using `Ideal.map_comap_le`. Establish `h2 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P := by`. Establish `: (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P).comap (algebraMap (𝓞 F) (𝓞 K)) = P.comap (algebraMap (𝓞 F) (𝓞 K)) := by`. Rewrite using `[conjIdeal_eq_comap]`.

Conclude with `SplitPrimeIdeals.comap_ι_comap (conjO_eq_iff_mem_range hF) P`. Rewrite using `[← this]`. Conclude with `Ideal.map_comap_le`. Establish `hcop : IsCoprime P (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P) := (Ideal.isCoprime_iff_sup_eq).2 (hP.coprime_of_ne hP' (Ne.symm hc))`. Establish `h3 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P := by`.

Rewrite using `[Ideal.mul_eq_inf_of_isCoprime hcop]`. Conclude with `le_inf h1 h2`. Take `⟨C, hC⟩` from `Ideal.dvd_iff_le.2 h3`. Establish `hN` using `absNorm_extP hK hF (P.comap (algebraMap (𝓞 F) (𝓞 K)))`. Rewrite `hN` using `[hC, map_mul, map_mul, absNorm_conjIdeal hK, absNorm_comap_split hK hF hP hc, sq]`.

Establish `hpos : 0 < Ideal.absNorm P * Ideal.absNorm P`. Establish `: 0 < Ideal.absNorm P`. Use `IdealNormInequalities.one_lt_absNorm hP` as an intermediate fact. Conclude with `zero_lt_one.trans this` after adjusting the coercions. Check the signs of the components of the expression.

Establish `hC1 : Ideal.absNorm C = 1` using `Nat.eq_of_mul_eq_mul_left hpos (by rw [hN, mul_one])`. Rewrite using `[hC, Ideal.absNorm_eq_one_iff.1 hC1, Ideal.mul_top]`.
-/
theorem extP_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hP' := conjIdeal_isMaximal hK hP
  have h1 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  have h2 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    have : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) =
        P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [conjIdeal_eq_comap]
      exact SplitPrimeIdeals.comap_ι_comap (conjO_eq_iff_mem_range hF) P
    rw [← this]
    exact Ideal.map_comap_le
  have hcop : IsCoprime P (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) :=
    (Ideal.isCoprime_iff_sup_eq).2 (hP.coprime_of_ne hP' (Ne.symm hc))
  have h3 : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf h1 h2
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 h3
  have hN := absNorm_extP hK hF (P.comap (algebraMap (𝓞 F) (𝓞 K)))
  rw [hC, map_mul, map_mul, absNorm_conjIdeal hK, absNorm_comap_split hK hF hP hc, sq] at hN
  have hpos : 0 < Ideal.absNorm P * Ideal.absNorm P := by
    have : 0 < Ideal.absNorm P := by
      have := IdealNormInequalities.one_lt_absNorm hP
      exact_mod_cast zero_lt_one.trans this
    positivity
  have hC1 : Ideal.absNorm C = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [hN, mul_one])
  rw [hC, Ideal.absNorm_eq_one_iff.1 hC1, Ideal.mul_top]

/- English proof (translation)
Simplify using `[alphaStd]`.
-/
theorem alphaStd_one (𝔭 : Ideal (𝓞 F)) :
    alphaStd K 𝔭 1 = 1 - etaF K F 𝔭 * (Ideal.absNorm 𝔭 : ℝ)⁻¹ := by
  simp [alphaStd]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `exists_maximal_over hK hF h𝔭`. Establish `h1 : (1 : 𝓞 K) ∉ P` using `fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)`. Establish `hd` using `localDensity K hK P hP 1 j le_rfl hj 1 (map_one _) h1`. Rewrite using `[alphaStd_one, etaF_comap hK hF hP]`. Distinguish the cases in `hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P`.

Rewrite using `[map_comap_eq_of_inert hK hF hP hc, hd.1 hc, if_pos hc, ← absNorm_comap_inert hK hF hP hc]`. Use `push_cast`. Rewrite using `[Real.sqrt_sq (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Rewrite using `[extP_split hK hF hP hc, hd.2 hc, if_neg hc, absNorm_comap_split hK hF hP hc]`.

Simplify using the standard rewrite rules.
-/
theorem normRepCount_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : 1 ≤ j) :
    (normRepCount K (extP K 𝔭 ^ j) 1 1 : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ j * alphaStd K 𝔭 1 := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have h1 : (1 : 𝓞 K) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hd := localDensity K hK P hP 1 j le_rfl hj 1 (map_one _) h1
  rw [alphaStd_one, etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [map_comap_eq_of_inert hK hF hP hc, hd.1 hc, if_pos hc, ← absNorm_comap_inert hK hF hP hc]
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    simp
  · rw [extP_split hK hF hP hc, hd.2 hc, if_neg hc, absNorm_comap_split hK hF hP hc]
    simp

end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
