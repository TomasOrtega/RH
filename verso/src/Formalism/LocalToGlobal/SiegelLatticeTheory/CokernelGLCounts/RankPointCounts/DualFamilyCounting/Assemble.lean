import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Asm

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Gen

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Unfold `cJ`. Distinguish the cases in `hS : ∃ b a, IsJordanIn h X L 𝔭 b a`. Take `⟨b, a, hJ⟩` from `hS`. Use `(Nat.sInf_le (show cJof 𝔭 a ∈ {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} from ⟨b, a, hJ, rfl⟩)).trans ?_` and prove the remaining obligations. Unfold `cJof`.

Conclude with `(Finset.card_filter_le _ _).trans (by simp)`. Establish `he : {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} = ∅`. Use extensionality with `c`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨b, a, hJ, -⟩`.

Conclude with `hS ⟨b, a, hJ⟩`. Rewrite using `[he, Nat.sInf_empty]`. Conclude with `Nat.zero_le _`.
-/
theorem cJ_le (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : cJ h X L 𝔭 ≤ finrank K X := by
  unfold cJ
  by_cases hS : ∃ b a, IsJordanIn h X L 𝔭 b a
  · obtain ⟨b, a, hJ⟩ := hS
    refine (Nat.sInf_le (show cJof 𝔭 a ∈ {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} from
      ⟨b, a, hJ, rfl⟩)).trans ?_
    unfold cJof
    exact (Finset.card_filter_le _ _).trans (by simp)
  · have he : {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a} = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨b, a, hJ, -⟩
      exact hS ⟨b, a, hJ⟩
    rw [he, Nat.sInf_empty]
    exact Nat.zero_le _

/- English proof (translation)
Introduce `x hx y hy`. Establish `hy' : y ∈ Formalism.HermitianLatticesTheory.dual h Λ` using `by rw [hU]; exact hy`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'`. Conclude with `hy' x hx`.
-/
theorem integral_of_unimod {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : Submodule (𝓞 K) V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h Λ) : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ := by
  intro x hx y hy
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual h Λ := by rw [hU]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx

/- English proof (translation)
Use extensionality with `Λ`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨-, hU, hΛ⟩`. Apply `hM` to reduce the goal to its premises. Introduce `x hx y hy`.

Rewrite `hx`, `hy` using `[← hΛ]`. Conclude with `integral_of_unimod hU x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).1`.
-/
theorem glueSet_eq_empty {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : ¬ Formalism.HermitianLatticesTheory.IsIntegralLat h M) : GlueSet h U M = ∅ := by
  ext Λ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hU, hΛ⟩
  apply hM
  intro x hx y hy
  rw [← hΛ] at hx hy
  exact integral_of_unimod hU x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).1

/- English proof (translation)
Use `⟨fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ), fun Λ hΛ => ?_, fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ)⟩` and prove the remaining obligations. Rewrite `hΛ` using `[hE]`. Conclude with `absurd hΛ (Set.notMem_empty Λ)`.
-/
theorem isGlueReps_empty {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hE : GlueSet h U M = ∅) : IsGlueReps h U M ∅ := by
  refine ⟨fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ), fun Λ hΛ => ?_,
    fun Λ hΛ => absurd hΛ (Finset.notMem_empty Λ)⟩
  rw [hE] at hΛ
  exact absurd hΛ (Set.notMem_empty Λ)

end Gen

section Mass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
Take `⟨c₁, hc₁, hall⟩` from `massConst_all hermRepUnram liStat hK hF`. Establish `he : Finset.Icc 2 1 = ∅` using `Finset.Icc_eq_empty (by norm_num)`. Establish `h1` using `hall 1 le_rfl`. Rewrite `h1` using `[he, Finset.prod_empty, mul_one]`. Establish `hex : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c` using `⟨c₁, hc₁, h1⟩`.

Unfold `cOne`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`.
-/
theorem cOne_spec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    0 < cOne K F ∧ MassConst K F 1 (cOne K F) := by
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have he : Finset.Icc 2 1 = ∅ := Finset.Icc_eq_empty (by norm_num)
  have h1 := hall 1 le_rfl
  rw [he, Finset.prod_empty, mul_one] at h1
  have hex : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := ⟨c₁, hc₁, h1⟩
  unfold cOne
  rw [dif_pos hex]
  exact hex.choose_spec

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
Introduce `m hm`. Proceed by induction on `m with`. Consider the case `zero => omega`. Consider the case `succ m ih`. Break down `Nat.eq_zero_or_pos m with rfl | hpos` into its components or cases.

Establish `he : Finset.Icc 2 (0 + 1) = ∅` using `Finset.Icc_eq_empty (by norm_num)`. Unfold `cMass`. Rewrite using `[he, Finset.prod_empty, mul_one]`. Conclude with `cOne_spec hK hF`. Take `⟨h0, hc⟩` from `ih hpos`.

Establish `hstep` using `massConst_succ hermRepUnram liStat hK hF (m := m + 1) (by omega) h0 (by simpa using hc)`. Establish `hr` using `massRatio_pos hK (m + 1) (by omega)`. Establish `heq : cMass K F (m + 1) = cMass K F m * Formalism.HermitianLatticesTheory.massRatioRightSide K (m + 1)`. Unfold `cMass`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), mul_assoc]`.

Rewrite using `[heq]`. Conclude with `⟨mul_pos h0 hr, hstep⟩`.
-/
theorem cMass_spec (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∀ m : ℕ, 1 ≤ m → 0 < cMass K F m ∧ MassConst K F m (cMass K F m) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have he : Finset.Icc 2 (0 + 1) = ∅ := Finset.Icc_eq_empty (by norm_num)
      unfold cMass
      rw [he, Finset.prod_empty, mul_one]
      exact cOne_spec hK hF
    · obtain ⟨h0, hc⟩ := ih hpos
      have hstep := massConst_succ hermRepUnram liStat hK hF (m := m + 1) (by omega) h0
        (by simpa using hc)
      have hr := massRatio_pos hK (m + 1) (by omega)
      have heq : cMass K F (m + 1) = cMass K F m * Formalism.HermitianLatticesTheory.massRatioRightSide K (m + 1) := by
        unfold cMass
        rw [Finset.prod_Icc_succ_top (by omega), mul_assoc]
      rw [heq]
      exact ⟨mul_pos h0 hr, hstep⟩

/- English proof (translation)
Set `π` to `fun x : {P : Ideal (𝓞 K) // P.IsMaximal} => (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})`. Establish `hf` using `multipliable_eulerFac hK i hi`. Establish `h1 : HasProd (fun p : (Σ b, {x // π x = b}) => Formalism.HermitianLatticesTheory.eulerFac K i (Equiv.sigmaFiberEquiv π p).1) (Formalism.HermitianLatticesTheory.lValEta K i)` using `(Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd`. Establish `h2` using `HasProd.sigma h1 (Regroup.hasProd_fibre hK hF i (by omega))`. Rewrite using `[← lValEta_eq_lValEtaF hK hF i hi]`.

Conclude with `h2`.
-/
theorem hasProd_lF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (i : ℕ) (hi : 2 ≤ i) :
    HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
      (1 - etaF K F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹) (lValEtaF K F i) := by
  let π := fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
    (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
      {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
  have hf := multipliable_eulerFac hK i hi
  have h1 : HasProd (fun p : (Σ b, {x // π x = b}) =>
      Formalism.HermitianLatticesTheory.eulerFac K i (Equiv.sigmaFiberEquiv π p).1) (Formalism.HermitianLatticesTheory.lValEta K i) :=
    (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  have h2 := HasProd.sigma h1 (Regroup.hasProd_fibre hK hF i (by omega))
  rw [← lValEta_eq_lValEtaF hK hF i hi]
  exact h2

/- English proof (translation)
Establish `hsplit : alphaStd K 𝔭 r = alphaStd K 𝔭 (k - 1) * ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))`. Unfold `alphaStd`. Rewrite using `[← Finset.prod_union]`. Use `congr 1`. Use extensionality with `i`.

Simplify using `only [Finset.mem_union, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_left]`. Introduce `i hi hi'`. Simplify using `only [Finset.mem_Icc] at hi hi'`.

Use linear arithmetic over natural numbers and integers. Establish `hpos` using `alphaStd_pos hK hF h𝔭 r`. Establish `hne : (∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))) ≠ 0`. Introduce `h0`. Rewrite `hpos` using `[hsplit, h0, mul_zero]`.

Conclude with `lt_irrefl _ hpos`. Rewrite using `[hsplit, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hne, mul_one]`.
-/
theorem alpha_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k r : ℕ} (hk : 1 ≤ k) (hkr : k - 1 ≤ r) :
    alphaStd K 𝔭 (k - 1) = alphaStd K 𝔭 r *
      ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))⁻¹ := by
  have hsplit : alphaStd K 𝔭 r = alphaStd K 𝔭 (k - 1) *
      ∏ i ∈ Finset.Icc k r, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
    unfold alphaStd
    rw [← Finset.prod_union]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_Icc] at hi hi'
      omega
  have hpos := alphaStd_pos hK hF h𝔭 r
  have hne : (∏ i ∈ Finset.Icc k r,
      (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ)))) ≠ 0 := by
    intro h0
    rw [hsplit, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [hsplit, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hne, mul_one]

def plEquiv : IsDedekindDomain.HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} where
  toFun P := ⟨P.asIdeal, P.isMaximal⟩
  invFun 𝔭 := ⟨𝔭.1, 𝔭.2.isPrime, fun h =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h ▸ 𝔭.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Mass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.SG.Pf.Asm

namespace Formalism.L2.SG.Pf

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

/- English proof (translation)
Introduce `D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hP`. Take `⟨hK, hF, hN⟩` from `h0 D`. Take `⟨F', hz, hZ⟩` from `h1 D u u' hT F0 what₂ hR Z hP`. Take `⟨hC, hPD, hUr, hWr⟩` from `h2 D u u' hT F0 what₂ hR Z F' hz hZ hP`. Take `⟨hLat, -⟩` from `h3 D u u' hT F0 what₂ hR Z F' hz hZ hP`.

Establish `e4` using `h4 D u u' hT F0 what₂ hR Z F' hz hZ hP`. Take `⟨h5i, h5n⟩` from `h5 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP`. Establish `hk : D.R.m + 3 ≤ D.R.k` using `D.R.m_add_three_le_k`. Establish `hnu0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0 → Formalism.L2.SG.CntLocal.nu (Tn u') F0 what₂ Z = 0`. Introduce `h0`.

Unfold `Formalism.L2.SG.CntLocal.nu`. Rewrite using `[show (∑ Λ ∈ what₂, wRow D F0 Λ) = Formalism.MainNotions.S.Cnt.massRows D F0 what₂ from rfl, h0, div_zero]`. Distinguish the cases in `hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')`. Establish `hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal → cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭 < finrank D.host.E (orthK (VS D).hT (UPair D F0 F'))`. Introduce `𝔭 _`.

Use `cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭` as an intermediate fact. Rewrite using `[hWr]`. Use linear arithmetic over natural numbers and integers. Establish `hne` using `g7 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 F') hLat hI hcJ`. Establish `hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 F'))) (cMass D.host.E D.host.F (D.R.k - 1))`.

Rewrite using `[hWr]`. Conclude with `(cMass_spec hK hF (D.R.k - 1) (by omega)).2`. Take `⟨s, hs1, hs2, hs3, hsum⟩` from `g9 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD (MMof D F0 F') hLat hI hne _ hMC`. Establish `e4'` using `e4 s ⟨hs1, hs2, hs3⟩`. Rewrite `e4'` using `[hsum, hWr]`.

Take `⟨hd, hmult⟩` from `h5i hI`. Establish `h6'` using `h6 D u u' hT F0 what₂ hR Z F' hz hZ hP hI`. Establish `hg : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} => alphaStd D.host.E 𝔭.1 D.R.r / alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) (∏' p, densP L δ ϖ (Tn u) (Tn u') Z p)`. Use `(plEquiv (F := D.host.F)).hasProd_iff.mp ?_` and prove the remaining obligations. Establish `hh` using `hmult.hasProd`.

Use `hh using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Conclude with `(hd p).symm`. Establish `hl : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} => ∏ i ∈ Finset.Icc D.R.k D.R.r, (1 - etaF D.host.E D.host.F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹) (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i)` using `hasProd_prod fun i hi => hasProd_lF hK hF i (by simp only [Finset.mem_Icc] at hi; omega)`. Establish `hrk : D.R.k - 1 ≤ D.R.r` using `by show D.R.k - 1 ≤ D.R.k + D.R.m - 1`.

Use linear arithmetic over natural numbers and integers. Establish `hT1 : (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal}, alphaStd D.host.E 𝔭.1 (D.R.k - 1) / alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) = (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) * ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p`. Use `HasProd.tprod_eq ?_` and prove the remaining obligations. Use `hl.mul hg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `𝔭`.

Rewrite using `[alpha_split hK hF 𝔭.2 (by omega) hrk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e4'` using `[hT1, h6']`. Distinguish the cases in `hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0`. Rewrite using `[hnu0 hm0]`.

Unfold `cExpl`. Rewrite using `[hm0, div_zero, zero_mul, zero_mul]`. Establish `e1 : (|(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))) ^ (D.R.k - 1) = |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ))`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e4'` using `[mul_pow, e1]`. Unfold `cExpl`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `e4'`. Establish `hE` using `glueSet_eq_empty (U := UPair D F0 F') hI`. Establish `e4'` using `e4 ∅ (isGlueReps_empty hE)`. Rewrite `e4'` using `[Finset.sum_empty]`. Take `⟨p, hp⟩` from `h5n hI`.

Establish `hz0 : ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p = 0` using `(hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).tprod_eq`. Rewrite using `[hz0, mul_zero]`. Distinguish the cases in `hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0`. Conclude with `hnu0 hm0`. Conclude with `(mul_eq_zero.mp e4').resolve_right hm0`.
-/
theorem formulaExplicit_of (h0 : HostDict) (h1 : RatPair) (h2 : PerpDef) (h3 : MMChar)
    (h4 : RowsGroupoid) (h5 : DensAll) (h6 : NormMM) (g7 : GlueExists) (g9 : GlueMass) :
    FormulaExplicit := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hP
  obtain ⟨hK, hF, hN⟩ := h0 D
  obtain ⟨F', hz, hZ⟩ := h1 D u u' hT F0 what₂ hR Z hP
  obtain ⟨hC, hPD, hUr, hWr⟩ := h2 D u u' hT F0 what₂ hR Z F' hz hZ hP
  obtain ⟨hLat, -⟩ := h3 D u u' hT F0 what₂ hR Z F' hz hZ hP
  have e4 := h4 D u u' hT F0 what₂ hR Z F' hz hZ hP
  obtain ⟨h5i, h5n⟩ := h5 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hnu0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0 → Formalism.L2.SG.CntLocal.nu (Tn u') F0 what₂ Z = 0 := by
    intro h0
    unfold Formalism.L2.SG.CntLocal.nu
    rw [show (∑ Λ ∈ what₂, wRow D F0 Λ) = Formalism.MainNotions.S.Cnt.massRows D F0 what₂ from rfl, h0, div_zero]
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')
  ·
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭 <
          finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭
      rw [hWr]
      omega
    have hne := g7 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 F') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 F') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 F')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, hsum⟩ := g9 D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 F') hC hPD (MMof D F0 F') hLat hI hne _ hMC
    have e4' := e4 s ⟨hs1, hs2, hs3⟩
    rw [hsum, hWr] at e4'
    obtain ⟨hd, hmult⟩ := h5i hI
    have h6' := h6 D u u' hT F0 what₂ hR Z F' hz hZ hP hI

    have hg : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
        alphaStd D.host.E 𝔭.1 D.R.r /
          alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1))
        (∏' p, densP L δ ϖ (Tn u) (Tn u') Z p) := by
      refine (plEquiv (F := D.host.F)).hasProd_iff.mp ?_
      have hh := hmult.hasProd
      convert hh using 1
      funext p
      exact (hd p).symm
    have hl : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
        ∏ i ∈ Finset.Icc D.R.k D.R.r,
          (1 - etaF D.host.E D.host.F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹)
        (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) :=
      hasProd_prod fun i hi => hasProd_lF hK hF i (by simp only [Finset.mem_Icc] at hi; omega)
    have hrk : D.R.k - 1 ≤ D.R.r := by
      show D.R.k - 1 ≤ D.R.k + D.R.m - 1
      omega
    have hT1 : (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
        alphaStd D.host.E 𝔭.1 (D.R.k - 1) /
          alphaStd D.host.E 𝔭.1 (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') 𝔭.1)) =
        (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) *
          ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p := by
      refine HasProd.tprod_eq ?_
      convert hl.mul hg using 1
      funext 𝔭
      rw [alpha_split hK hF 𝔭.2 (by omega) hrk]
      ring
    rw [hT1, h6'] at e4'
    by_cases hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0
    · rw [hnu0 hm0]
      unfold cExpl
      rw [hm0, div_zero, zero_mul, zero_mul]
    · have e1 : (|(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))) ^ (D.R.k - 1) =
          |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [mul_pow, e1] at e4'
      unfold cExpl
      field_simp
      linear_combination e4'
  ·
    have hE := glueSet_eq_empty (U := UPair D F0 F') hI
    have e4' := e4 ∅ (isGlueReps_empty hE)
    rw [Finset.sum_empty] at e4'
    obtain ⟨p, hp⟩ := h5n hI
    have hz0 : ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p = 0 :=
      (hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).tprod_eq
    rw [hz0, mul_zero]
    by_cases hm0 : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = 0
    · exact hnu0 hm0
    · exact (mul_eq_zero.mp e4').resolve_right hm0

end Formalism.L2.SG.Pf
