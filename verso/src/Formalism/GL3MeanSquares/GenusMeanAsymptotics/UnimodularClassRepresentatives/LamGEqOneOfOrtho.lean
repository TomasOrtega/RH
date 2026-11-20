import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaLEqOfBridge

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `haveI : Fact (IsFixF K F) := ⟨hF⟩`. Take `⟨b, u, -, hb, hH, hu, hunit⟩` from `OrthogonalBases.exists_orth_basis hK hF hs hd hL hLi h𝔭 hv`. Conclude with `IsotropicCounts.alphaL_eq_of_bridge hK h𝔭 u hu hunit fun k => integralBasisSpans.akCount_eq h h𝔭 b hb hH k`.
-/
theorem alphaL_of_vd_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, u, -, hb, hH, hu, hunit⟩ := OrthogonalBases.exists_orth_basis hK hF hs hd hL hLi h𝔭 hv
  exact IsotropicCounts.alphaL_eq_of_bridge hK h𝔭 u hu hunit fun k => integralBasisSpans.akCount_eq h h𝔭 b hb hH k

/- English proof (translation)
Establish `h1 : Ideal.absNorm 𝔭 ≠ 1` using `fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)`. Establish `h0 : Ideal.absNorm 𝔭 ≠ 0` using `fun h => (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)) (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hN : (1 : ℝ) < Ideal.absNorm 𝔭`. Establish `: 1 < Ideal.absNorm 𝔭` using `by omega`. Conclude with `this` after adjusting the coercions.

Unfold `alphaStd`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j hj`. Establish `hj1 : 1 ≤ j` using `(Finset.mem_Icc.mp hj).1`. Establish `hpow : (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) < 1` using `zpow_lt_one_of_neg₀ hN (by omega)`.

Establish `hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ))` using `zpow_pos (by linarith) _`. Establish `hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1`. Unfold `etaF`. Apply the tactic sequence `split_ifs <;> simp`. Apply the tactic sequence `rcases hη with h | h <;> rw [h]`.

Rewrite using `[one_pow, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `rcases neg_one_pow_eq_or ℝ j with h' | h' <;> rw [h'] <;> linarith`.
-/
theorem alphaStd_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (m : ℕ) : 0 < alphaStd K 𝔭 m := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (1 : ℝ) < Ideal.absNorm 𝔭 := by
    have : 1 < Ideal.absNorm 𝔭 := by omega
    exact_mod_cast this
  unfold alphaStd
  apply Finset.prod_pos
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpow : (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hN (by omega)
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by linarith) _
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h]
  · rw [one_pow, one_mul]
    linarith
  · rcases neg_one_pow_eq_or ℝ j with h' | h' <;> rw [h'] <;> linarith

/- English proof (translation)
Unfold `lamP`. Rewrite using `[hv, mul_zero, pow_zero, mul_one, alphaL_of_vd_zero hK hF hs hd hL hLi h𝔭 hv]`. Conclude with `div_self (alphaStd_pos hK hF h𝔭 _).ne'`.
-/
theorem localMassFactor_of_valuation_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : lamP h L 𝔭 = 1 := by
  unfold lamP
  rw [hv, mul_zero, pow_zero, mul_one, alphaL_of_vd_zero hK hF hs hd hL hLi h𝔭 hv]
  exact div_self (alphaStd_pos hK hF h𝔭 _).ne'

/- English proof (translation)
Unfold `lamG`. Establish `hd` using `isTotPosDef_of_ortho hK hs hI`. Establish `hL` using `isLattice_of_ortho hI`. Establish `hLi` using `isIntegralLat_of_ortho hI`. Establish `: ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h I 𝔭.1 = 1`.

Introduce `𝔭`. Take `⟨P, hP, hP𝔭⟩` from `exists_maximal_over hK hF 𝔭.2`. Apply `localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2` to reduce the goal to its premises. Rewrite using `[← hP𝔭]`. Conclude with `(isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mp (isUnimodularAt_of_ortho hK hs hI P hP)`.

Simplify using `only [this, tprod_one]`.
-/
theorem lamG_eq_one_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) : lamG F h I = 1 := by
  unfold lamG
  have hd := isTotPosDef_of_ortho hK hs hI
  have hL := isLattice_of_ortho hI
  have hLi := isIntegralLat_of_ortho hI
  have : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h I 𝔭.1 = 1 := by
    intro 𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2
    rw [← hP𝔭]
    exact (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mp (isUnimodularAt_of_ortho hK hs hI P hP)
  simp only [this, tprod_one]

end Formalism.HermitianLattices.Ext.L3
