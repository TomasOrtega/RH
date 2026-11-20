import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JordanExponentsMaximalHermitianLatticeBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantModuleIsometriesEqNormOneResiduesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

namespace GlobalTheory.Mass.MaxFormula

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] in
/- English proof (translation)
Establish `han : ∀ x, h x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `h0`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Use `hd x h0 φ` as an intermediate fact.

Simplify using `[hx] at this`. Conclude with `⟨fun x hx => han x (hx x), fun x hx => han x (hx x)⟩`.
-/
theorem nondegenerate_of_pos {h : V →ₗ⋆[K] V →ₗ[K] K} [NumberField K] (hd : IsTotPosDef h) :
    h.Nondegenerate := by
  have han : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x h0 φ
    simp [hx] at this
  exact ⟨fun x hx => han x (hx x), fun x hx => han x (hx x)⟩

/- English proof (translation)
Establish `hnd` using `nondegenerate_of_pos hd`. Take `⟨hc, hq2, hq, -⟩` from `(GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P hP`. Establish `hPm : P.IsMaximal` using `hP.1`. Use `set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def`. Establish `h𝔭 : 𝔭.IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`.

Take `⟨hJ1, hJ2⟩` from `jordan_splitting_exists K F V hK hF h hs`. Take `⟨b, a, hJ⟩` from `hJ1 ⊤ M (fun x _ hx => hnd.1 x fun y => hx y trivial) ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩ hM.1.2 𝔭 h𝔭`. Take `⟨i, hi, hj⟩` from `GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime K F V hK hF h hs hd M hM P hP b a hJ`. Establish `hv : vd h M 𝔭 = 1`. Rewrite using `[hJ2 M hM.1.1 𝔭 h𝔭 b a hJ, vJof, Finset.sum_eq_single i (fun j _ => hj j) (by simp)]`.

Conclude with `hi`. Establish `hcJ : cJof 𝔭 a = 1`. Rewrite using `[cJof, Finset.card_eq_one]`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use extensionality with `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Use `⟨fun h1 => by_contra fun h2 => h1 (hj j h2), ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite using `[hi]`. Conclude with `one_ne_zero`.

Establish `hN : Ideal.absNorm 𝔭 = qIn P`. Use `absNorm_comap_inert hK hF hPm hc` as an intermediate fact. Rewrite `this` using `[hq]`. Conclude with `Nat.pow_left_injective two_ne_zero this`. Establish `hη : etaF K F 𝔭 = -1` using `by rw [h𝔭def, etaF_comap hK hF hPm, if_pos hc]`.

Establish `hdisc : (discAut h ⊤ M 𝔭 : ℝ) = (qIn P : ℝ) + 1`. Establish `hq0 : (qIn P : ℝ) ≠ 0` using `by exact_mod_cast (by omega : qIn P ≠ 0)`. Rewrite using `[GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues K F V hK hF h hs M hM.1.1 𝔭 h𝔭 b a hJ i hi hj, ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 le_rfl, ThirdPropositionSlot.alphaStd_one, hη, hN]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hm : 1 ≤ Module.finrank K V`. Use `i.pos` as an intermediate fact. Rewrite `this` using `[finrank_top]`. Then use the resulting hypothesis. Take `⟨m, hm'⟩ : ∃ m, Module.finrank K V = m + 1` from `⟨_, (Nat.sub_add_cancel hm).symm⟩`. Establish `hpos` using `alphaStd_pos hK hF h𝔭 m`.

Establish `hq0 : (0 : ℝ) < qIn P` using `by exact_mod_cast (by omega : 0 < qIn P)`. Rewrite using `[lamP, alpha_discriminant_holds K F V hK hF h hs hd M hM.1.1 hM.1.2 𝔭 h𝔭 b a hJ, hv, hcJ, hdisc, hm', Nat.add_sub_cancel, mul_one]`. Establish `hstep : alphaStd K 𝔭 (m + 1) = alphaStd K 𝔭 m * (1 - (-1) ^ (m + 1) * ((qIn P : ℝ) ^ (m + 1))⁻¹)`. Rewrite using `[alphaStd, Finset.prod_Icc_succ_top (by omega), hη, hN, zpow_neg, zpow_natCast, ← hN, ← hη]`. Both sides reduce to the same expression.

Rewrite using `[hstep, hN]`. Clear the denominators using the available nonvanishing facts.
-/
theorem localMassFactor_eq_of_mem_badPrimes (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) {P : Ideal (𝓞 K)}
    (hP : P ∈ badP h M) :
    lamP h M (P.comap (algebraMap (𝓞 F) (𝓞 K))) =
      ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1) := by
  have hnd := nondegenerate_of_pos hd
  obtain ⟨hc, hq2, hq, -⟩ := (GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P hP
  have hPm : P.IsMaximal := hP.1
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  obtain ⟨hJ1, hJ2⟩ := jordan_splitting_exists K F V hK hF h hs
  obtain ⟨b, a, hJ⟩ := hJ1 ⊤ M (fun x _ hx => hnd.1 x fun y => hx y trivial)
    ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩ hM.1.2 𝔭 h𝔭
  obtain ⟨i, hi, hj⟩ := GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime K F V hK hF h hs hd M hM P hP b a hJ
  have hv : vd h M 𝔭 = 1 := by
    rw [hJ2 M hM.1.1 𝔭 h𝔭 b a hJ, vJof, Finset.sum_eq_single i (fun j _ => hj j) (by simp)]
    exact hi
  have hcJ : cJof 𝔭 a = 1 := by
    rw [cJof, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun h1 => by_contra fun h2 => h1 (hj j h2), ?_⟩
    rintro rfl
    rw [hi]
    exact one_ne_zero
  have hN : Ideal.absNorm 𝔭 = qIn P := by
    have := absNorm_comap_inert hK hF hPm hc
    rw [hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  have hη : etaF K F 𝔭 = -1 := by rw [h𝔭def, etaF_comap hK hF hPm, if_pos hc]
  have hdisc : (discAut h ⊤ M 𝔭 : ℝ) = (qIn P : ℝ) + 1 := by
    have hq0 : (qIn P : ℝ) ≠ 0 := by exact_mod_cast (by omega : qIn P ≠ 0)
    rw [GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues K F V hK hF h hs M hM.1.1 𝔭 h𝔭 b a hJ i hi hj,
      ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 le_rfl, ThirdPropositionSlot.alphaStd_one, hη, hN]
    field_simp
    ring
  have hm : 1 ≤ Module.finrank K V := by
    have := i.pos
    rwa [finrank_top] at this
  obtain ⟨m, hm'⟩ : ∃ m, Module.finrank K V = m + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
  have hpos := alphaStd_pos hK hF h𝔭 m
  have hq0 : (0 : ℝ) < qIn P := by exact_mod_cast (by omega : 0 < qIn P)
  rw [lamP, alpha_discriminant_holds K F V hK hF h hs hd M hM.1.1 hM.1.2 𝔭 h𝔭 b a hJ, hv, hcJ, hdisc, hm',
    Nat.add_sub_cancel, mul_one]
  have hstep : alphaStd K 𝔭 (m + 1) =
      alphaStd K 𝔭 m * (1 - (-1) ^ (m + 1) * ((qIn P : ℝ) ^ (m + 1))⁻¹) := by
    rw [alphaStd, Finset.prod_Icc_succ_top (by omega), hη, hN, zpow_neg, zpow_natCast, ← hN, ← hη]
    rfl
  rw [hstep, hN]
  field_simp

/- English proof (translation)
Establish `hst` using `GlobalTheory.MaxLatStruct.main K V h hK hs (nondegenerate_of_pos hd) M hM`. Establish `hfin` using `hst.1`. Set `g : {P // P ∈ hfin.toFinset} → {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}` to `fun P => ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 K)), by`. Establish `: P.1.IsMaximal` using `(hfin.mem_toFinset.1 P.2).1`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.1⟩`.

Establish `hg : Function.Injective g`. Introduce `P Q hPQ`. Establish `hP` using `hfin.mem_toFinset.1 P.2`. Establish `hQ` using `hfin.mem_toFinset.1 Q.2`. Use `(comap_eq_comap_iff hK hF hP.1 hQ.1).1 (congrArg Subtype.val hPQ)` as an intermediate fact.

Rewrite `this` using `[(hst.2.2.2 P.1 hP).1, or_self]`. Conclude with `Subtype.ext this.symm`. Rewrite using `[lamG, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin, tprod_eq_prod (s := hfin.toFinset.attach.image g), Finset.prod_image fun _ _ _ _ e => hg e, ← Finset.prod_attach hfin.toFinset]`. Conclude with `Finset.prod_congr rfl fun P _ => localMassFactor_eq_of_mem_badPrimes hK hF hs hd hM (hfin.mem_toFinset.1 P.2)`. Introduce `𝔭 h𝔭`.

Take `⟨P, hP, hP𝔭⟩` from `exists_maximal_over hK hF 𝔭.2`. Apply `localMassFactor_of_valuation_eq_zero hK hF hs hd hM.1.1 hM.1.2 𝔭.2` to reduce the goal to its premises. Rewrite using `[← hP𝔭]`. Use `(isUnimodularAt_iff_vd hK hF hs hd hM.1.1 hM.1.2 hP).1 (by_contra fun hb => h𝔭 ?_)` and prove the remaining obligations. Conclude with `Finset.mem_image.2 ⟨⟨P, hfin.mem_toFinset.2 ⟨hP, hb⟩⟩, Finset.mem_attach _ _, Subtype.ext hP𝔭⟩`.
-/
theorem lamG_eq_lamMax (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) :
    lamG F h M = lamMax h M := by
  have hst := GlobalTheory.MaxLatStruct.main K V h hK hs (nondegenerate_of_pos hd) M hM
  have hfin := hst.1
  let g : {P // P ∈ hfin.toFinset} → {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 K)), by
      have : P.1.IsMaximal := (hfin.mem_toFinset.1 P.2).1
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.1⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    have hP := hfin.mem_toFinset.1 P.2
    have hQ := hfin.mem_toFinset.1 Q.2
    have := (comap_eq_comap_iff hK hF hP.1 hQ.1).1 (congrArg Subtype.val hPQ)
    rw [(hst.2.2.2 P.1 hP).1, or_self] at this
    exact Subtype.ext this.symm
  rw [lamG, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin,
    tprod_eq_prod (s := hfin.toFinset.attach.image g), Finset.prod_image fun _ _ _ _ e => hg e,
    ← Finset.prod_attach hfin.toFinset]
  · exact Finset.prod_congr rfl fun P _ => localMassFactor_eq_of_mem_badPrimes hK hF hs hd hM (hfin.mem_toFinset.1 P.2)
  · intro 𝔭 h𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hM.1.1 hM.1.2 𝔭.2
    rw [← hP𝔭]
    refine (isUnimodularAt_iff_vd hK hF hs hd hM.1.1 hM.1.2 hP).1 (by_contra fun hb => h𝔭 ?_)
    exact Finset.mem_image.2 ⟨⟨P, hfin.mem_toFinset.2 ⟨hP, hb⟩⟩, Finset.mem_attach _ _,
      Subtype.ext hP𝔭⟩

/- English proof (translation)
Introduce `K _ _ _ hK n hn`. Take `⟨F, _, _, _, hF⟩` from `exists_fixF K hK`. Take `⟨c₁, -, hall⟩` from `massConst_all binary_hermitian_represents liStat hK hF`. Use `⟨c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j, fun V _ _ _ _ _ h hs hp hr M hM => ?_⟩` and prove the remaining obligations. Establish `hd : IsTotPosDef h` using `fun x hx φ => hp φ x hx`.

Rewrite using `[hall n hn V h M hs hd hr hM.1.1 hM.1.2, lamG_eq_lamMax hK hF hs hd hM]`.
-/
theorem main : MaxMass := by
  intro K _ _ _ hK n hn
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all binary_hermitian_represents liStat hK hF
  refine ⟨c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j, fun V _ _ _ _ _ h hs hp hr M hM => ?_⟩
  have hd : IsTotPosDef h := fun x hx φ => hp φ x hx
  rw [hall n hn V h M hs hd hr hM.1.1 hM.1.2, lamG_eq_lamMax hK hF hs hd hM]

end GlobalTheory.Mass.MaxFormula
