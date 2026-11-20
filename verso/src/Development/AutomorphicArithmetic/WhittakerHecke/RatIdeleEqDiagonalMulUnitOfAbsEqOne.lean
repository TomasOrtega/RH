import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import GroundTheory.GlobalFields.IdeleGroups.Rational
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

/- English proof (translation)
Use `le_antisymm ha ?_` and prove the remaining obligations. Use `mul_le_mul' (le_refl a) hb` as an intermediate fact. Rewrite `this` using `[h, mul_one]`. Then use the resulting hypothesis.
-/
private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

/- English proof (translation)
Take `⟨h1, h2⟩` from `RationalIdeles.mem_positiveSubgroup.1 hp`. Establish `hw` using `RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)`. Establish `hmult : (default : InfinitePlace ℚ).mult = 1`. Simplify using `[InfinitePlace.mult, hw]`. Establish `hn : ‖(p : AdeleRing (𝓞 ℚ) ℚ).1 default‖ = (RationalIdeles.realPart p : ℝ)`.

Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), ← RationalIdeles.realEquiv_apply, ← RationalIdeles.coe_realPart, Real.norm_eq_abs, abs_of_pos h2]`. Unfold `ab`. Rewrite using `[IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule, Fintype.prod_subsingleton _ (default : InfinitePlace ℚ), hmult, pow_one, hn]`.
-/
private lemma ab_pos_eq {p : IdeleGroup ℚ} (hp : p ∈ RationalIdeles.positiveSubgroup) :
    ab p = (RationalIdeles.realPart p : ℝ) := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  have hw := RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [InfinitePlace.mult, hw]
  have hn : ‖(p : AdeleRing (𝓞 ℚ) ℚ).1 default‖ = (RationalIdeles.realPart p : ℝ) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _), ← RationalIdeles.realEquiv_apply, ← RationalIdeles.coe_realPart, Real.norm_eq_abs, abs_of_pos h2]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule,
    Fintype.prod_subsingleton _ (default : InfinitePlace ℚ), hmult, pow_one, hn]

/- English proof (translation)
Introduce `a ha`. Take `⟨⟨r, p⟩, hp⟩` from `RationalIdeles.mulMap_bijective.2 a`. Rewrite `hp` using `[RationalIdeles.mulMap_apply]`. Establish `hp' : a = IdeleGroup.diagonal ℚ r * (p : IdeleGroup ℚ)` using `hp.symm`. Establish `hab : ab (p : IdeleGroup ℚ) = 1`.

Rewrite `ha` using `[hp', ab_mul, ab_diagonal, one_mul]`. Conclude with `ha`. Take `⟨h1, -⟩` from `RationalIdeles.mem_positiveSubgroup.1 p.2`. Establish `hre : RationalIdeles.realEquiv ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1`. Rewrite using `[← RationalIdeles.coe_realPart, ← ab_pos_eq p.2, hab]`.

Establish `hone : ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1` using `RationalIdeles.realEquiv.injective (hre.trans (map_one _).symm)`. Use `⟨r, p, ⟨hone, fun v => ?_⟩, hp'⟩` and prove the remaining obligations. Take `⟨ha', hb'⟩` from `(IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v`. Establish `hm` using `IdeleGroup.finite_mul_inv (p : IdeleGroup ℚ) v`. Establish `hmv` using `congrArg Valued.v hm`.

Rewrite `hmv` using `[map_mul, map_one]`. Conclude with `eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha') ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb') hmv`.
-/
theorem UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one :
    ∀ a : IdeleGroup ℚ, ab a = 1 → ∃ (r : ℚˣ), ∃ u ∈ UU, a = IdeleGroup.diagonal ℚ r * u := by
  intro a ha
  obtain ⟨⟨r, p⟩, hp⟩ := RationalIdeles.mulMap_bijective.2 a
  rw [RationalIdeles.mulMap_apply] at hp
  have hp' : a = IdeleGroup.diagonal ℚ r * (p : IdeleGroup ℚ) := hp.symm
  have hab : ab (p : IdeleGroup ℚ) = 1 := by
    rw [hp', ab_mul, ab_diagonal, one_mul] at ha
    exact ha
  obtain ⟨h1, -⟩ := RationalIdeles.mem_positiveSubgroup.1 p.2
  have hre : RationalIdeles.realEquiv ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    rw [← RationalIdeles.coe_realPart, ← ab_pos_eq p.2, hab]
  have hone : ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
    RationalIdeles.realEquiv.injective (hre.trans (map_one _).symm)
  refine ⟨r, p, ⟨hone, fun v => ?_⟩, hp'⟩
  obtain ⟨ha', hb'⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
  have hm := IdeleGroup.finite_mul_inv (p : IdeleGroup ℚ) v
  have hmv := congrArg Valued.v hm
  rw [map_mul, map_one] at hmv
  exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha')
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb') hmv
