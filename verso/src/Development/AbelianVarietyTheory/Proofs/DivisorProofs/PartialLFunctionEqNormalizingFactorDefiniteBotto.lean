import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsConjPlOfUnderEqOfNe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomLVal

open GlobalTheory.LFun

/- English proof (translation)
Introduce `w hw`. Establish `hx` using `h _ hw w rfl`. Establish `h0 : (fun _ : GAd D.sp.cm.sig J => (1 : ℂ)) ≠ 0` using `fun e => one_ne_zero (congrFun e 1)`. Use `hx.unique ?_` and prove the remaining obligations. Break down `hx with ⟨hs, e, he, -⟩ | ⟨hw', τ, ϖ, e, α, hϖ, he, -, -⟩` into its components or cases.

Conclude with `Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w n).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩`. Use `Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero _) n).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]`. Conclude with `GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero _) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _`.
-/
private theorem par_eq_trivPar {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (S : Set (FinPl D)) (par : Fam D.host.E)
    (h : IsParamFun D.sp.cm.sig J L S (fun _ => (1 : ℂ)) par) :
    ∀ w ∉ above D.host.E S, par w = GlobalTheory.BottomRallis.trivPar (D := D) n w := by
  intro w hw
  have hx := h _ hw w rfl
  have h0 : (fun _ : GAd D.sp.cm.sig J => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  refine hx.unique ?_
  rcases hx with ⟨hs, e, he, -⟩ | ⟨hw', τ, ϖ, e, α, hϖ, he, -, -⟩
  · exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w n).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩
  · refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero _) n).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩
    rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
    exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero _) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

/- English proof (translation)
Simplify using `only [GlobalTheory.BottomIPData.sfB, GlobalTheory.FunObj.locPl, GlobalTheory.ChiGrid.Places.W0, Finset.mem_image, Finset.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, ⟨u, hu, rfl⟩ | hw, rfl⟩`. Conclude with `Or.inl ((G.pl.under_w hu).symm ▸ hu)`. Conclude with `Or.inr ⟨w, hw, rfl⟩`.

Introduce and unpack `(hv | ⟨P, hP, rfl⟩)`. Conclude with `⟨_, Or.inl ⟨v, hv, rfl⟩, G.pl.under_w hv⟩`. Conclude with `⟨P, Or.inr hP, rfl⟩`.
-/
private theorem mem_sfB (G : GridData L sc) (t : T) (v : FinPl D) :
    v ∈ GlobalTheory.BottomIPData.sfB G t ↔ v ∈ G.pl.S0 ∨ ∃ P ∈ L.Q t, P.under (𝓞 D.host.F) = v := by
  classical
  simp only [GlobalTheory.BottomIPData.sfB, GlobalTheory.FunObj.locPl, GlobalTheory.ChiGrid.Places.W0, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩ | hw, rfl⟩
    · exact Or.inl ((G.pl.under_w hu).symm ▸ hu)
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (hv | ⟨P, hP, rfl⟩)
    · exact ⟨_, Or.inl ⟨v, hv, rfl⟩, G.pl.under_w hv⟩
    · exact ⟨P, Or.inr hP, rfl⟩

/- English proof (translation)
Establish `hS1 : P.under (𝓞 D.host.F) ∉ S1 D` using `fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))`. Establish `a1 : 1 ≤ D.R.m - i` using `by have := i.2; omega`. Establish `a2 : D.R.m - i ≤ D.R.m` using `by omega`. Establish `hchi : (G.ch.chiH (D.R.m - i)).UnrAt P` using `G.ch.unr _ a1 a2 P hS0`. Establish `hmu : (L.C.mu0 j).UnrAt P` using `(L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 (by`.

Establish `: ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hk`. Use `fin_cases k`. Conclude with `Or.inl this`.

Conclude with `Or.inr (Or.inl this)))`. Use `⟨fun hnu => ?_, fun hxi => ?_⟩` and prove the remaining obligations. Establish `e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i)`. Rewrite using `[nuH]`. Establish `key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c` using `fun a x c => by`.

Rewrite using `[div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]`. Conclude with `key _ _ _`. Rewrite using `[e]`. Conclude with `(hnu.mul hmu.inv).mul hchi`. Rewrite using `[nuH, div_eq_mul_inv]`.

Conclude with `(hmu.mul hxi).mul hchi.inv`.
-/
private theorem nuH_unrAt_iff (G : GridData L sc) (t : T) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0) : (nuH G t i j).UnrAt P ↔ (L.xiH t).UnrAt P := by
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 (by
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  refine ⟨fun hnu => ?_, fun hxi => ?_⟩
  · have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv

/- English proof (translation)
Rewrite using `[mem_sfB]`. Distinguish the cases in `h0 : P.under (𝓞 D.host.F) ∈ G.pl.S0`. Conclude with `iff_of_true (GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j P h0) (Or.inl h0)`. Rewrite using `[nuH_unrAt_iff G t i j P h0, hL.Q_ram t P, or_iff_right h0]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(h | ⟨Q, h, hc⟩)`. Conclude with `⟨P, h, rfl⟩`. Conclude with `⟨Q, h, GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc⟩`. Introduce and unpack `⟨Q, h, e⟩`. Distinguish the cases in `hq : Q = P`.

Conclude with `Or.inl (hq ▸ h)`. Conclude with `Or.inr ⟨Q, h, GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D Q P e hq⟩`.
-/
private theorem nuH_not_unrAt_iff {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ (nuH G t i j).UnrAt P ↔ P.under (𝓞 D.host.F) ∈ GlobalTheory.BottomIPData.sfB G t := by
  rw [mem_sfB]
  by_cases h0 : P.under (𝓞 D.host.F) ∈ G.pl.S0
  · exact iff_of_true (GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j P h0) (Or.inl h0)
  · rw [nuH_unrAt_iff G t i j P h0, hL.Q_ram t P, or_iff_right h0]
    constructor
    · rintro (h | ⟨Q, h, hc⟩)
      · exact ⟨P, h, rfl⟩
      · exact ⟨Q, h, GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc⟩
    · rintro ⟨Q, h, e⟩
      by_cases hq : Q = P
      · exact Or.inl (hq ▸ h)
      · exact Or.inr ⟨Q, h, GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D Q P e hq⟩

/- English proof (translation)
Use `Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Finset.mem_range] at hi`. Simplify using `only [Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Introduce `s hs`. Simplify using `only [Finset.mem_Icc] at hs`. Simplify using `only [Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `i _`.

Simplify using the standard rewrite rules. Introduce `s hs`. Simplify using `only [Finset.mem_Icc] at hs`. Use linear arithmetic over natural numbers and integers. Introduce `i _`.

Both sides reduce to the same expression.
-/
private theorem prod_range_sub (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `ranks_exact D i j`. Establish `e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D` using `by simp only [rankV]; ring`. Establish `h4 : D.R.r ≤ rankV D i j` using `by simp only [rankV]; omega`. Establish `h5 : D.R.m < D.R.r` using `by have := D.R.m_add_three_le_k; unfold Ranks.r; omega`. Simplify using `only [h0, e0]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem bot_ranks (D : D7) (i j : ℕ) : 1 ≤ botSmall D i j ∧ botBig D i j + botSmall D i j = 2 * h0 D i j ∧
    botBig D i j = h0 D i j + e0 D i j := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have h4 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h5 : D.R.m < D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  simp only [h0, e0]
  omega

end GlobalTheory.BottomLVal

/- English proof (translation)
Use `⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W i j A A' WW X hX t par hpar => ?_⟩⟩` and prove the remaining obligations. Take `⟨r1, r2, r3⟩` from `GlobalTheory.BottomLVal.bot_ranks D i j`. Rewrite `r1`, `r2` using `[← hX.rank']`. Rewrite `r2`, `r3` using `[← hX.rank]`. Establish `hd` using `GlobalTheory.LFun.dSfun_ne_zero_of_re_pos (E := D.host.E) ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank (s := (A'.rank : ℂ) / 2) (by`.

Establish `: (1 : ℝ) ≤ A'.rank` using `by exact_mod_cast r1`. Simplify using `only [Complex.div_ofNat_re, Complex.natCast_re]`. Use the proof step `linarith)`. Use `⟨_, inv_ne_zero hd, fun Λ hΛ => ?_⟩` and prove the remaining obligations. Rewrite using `[inv_mul_cancel₀ hd, one_mul]`.

Establish `hν : (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)⁻¹ = G.nu t i (j + 1)`. Rewrite using `[inv_div]`. Conclude with `mul_div_mul_right_eq_div _ _ _`. Establish `hc` using `chrEq_nu G t i j hL`. Establish `hU : GlobalTheory.LFun.UnrOff (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D))` using `fun w hw => by`.

Rewrite using `[← inv_inv (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t), hν]`. Conclude with `((GlobalTheory.LFun.unrAt_iff_of_chrEq hc w).2 (not_not.1 (mt (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).1 hw))).inv`. Take `⟨σ, hσ⟩` from `GlobalTheory.RallisEuler.trivPar_euler _ _ A.rank hU`. Establish `hH : Differentiable ℂ fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k)` using `Differentiable.fun_finset_prod fun k _ => hΛ.1.comp (by fun_prop)`. Use `⟨fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k), ⟨Set.univ, trivial, isRightDomain_univ, fun s _ => (hH.analyticAt s).meromorphicAt, max σ ((A.rank : ℝ) / 2 + 1), fun s hs => ?_⟩, hH.analyticAt _, ?_⟩` and prove the remaining obligations.

Establish `hs1 : σ < s.re` using `(le_max_left _ _).trans_lt hs`. Establish `hs2 : (A.rank : ℝ) / 2 + 1 < s.re` using `(le_max_right _ _).trans_lt hs`. Use `Eq.trans ?_ ((hσ hs1).trans (GlobalTheory.LFun.LSTw_congr (GlobalTheory.BottomLVal.par_eq_trivPar _ _ _ par hpar) _ _).symm)` and prove the remaining obligations. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : (k : ℝ) + 1 ≤ A.rank` using `by exact_mod_cast Finset.mem_range.1 hk`.

Rewrite using `[hν, GlobalTheory.LFun.charL_eq_of_chrEq hc]`. Use `(GlobalTheory.SqStep.heckeL_eq_of_ram (fun w hw => (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).2 hw) hΛ ?_).symm` and prove the remaining obligations. Simplify using `only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← GlobalTheory.BottomLVal.prod_range_sub (fun s => Λ s) A.rank (h0 D i j) (e0 D i j) (by exact_mod_cast r3)]`.

Use `Finset.prod_congr rfl fun k _ => congrArg Λ ?_` and prove the remaining obligations. Establish `: (A.rank : ℂ) + A'.rank = 2 * (h0 D i j : ℕ)` using `by exact_mod_cast r2`. Use `push_cast`. Take the linear combination `this / 2`.
-/
theorem _root_.GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par →
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
    HolValueAt (fun s => GlobalTheory.LFun.LSD D (GlobalTheory.BottomIPData.sfB G t) par (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (s + 1 / 2)) ((A'.rank : ℂ) / 2)
      (κ * GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
        ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W i j A A' WW X hX t par hpar => ?_⟩⟩
  obtain ⟨r1, r2, r3⟩ := GlobalTheory.BottomLVal.bot_ranks D i j
  rw [← hX.rank'] at r1 r2
  rw [← hX.rank] at r2 r3
  have hd := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos (E := D.host.E)
    ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank
    (s := (A'.rank : ℂ) / 2) (by
      have : (1 : ℝ) ≤ A'.rank := by exact_mod_cast r1
      simp only [Complex.div_ofNat_re, Complex.natCast_re]
      linarith)
  refine ⟨_, inv_ne_zero hd, fun Λ hΛ => ?_⟩
  rw [inv_mul_cancel₀ hd, one_mul]
  have hν : (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)⁻¹ = G.nu t i (j + 1) := by
    rw [inv_div]
    exact mul_div_mul_right_eq_div _ _ _
  have hc := chrEq_nu G t i j hL
  have hU : GlobalTheory.LFun.UnrOff (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)
      ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) := fun w hw => by
    rw [← inv_inv (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t), hν]
    exact ((GlobalTheory.LFun.unrAt_iff_of_chrEq hc w).2
      (not_not.1 (mt (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).1 hw))).inv
  obtain ⟨σ, hσ⟩ := GlobalTheory.RallisEuler.trivPar_euler _ _ A.rank hU
  have hH : Differentiable ℂ fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k) :=
    Differentiable.fun_finset_prod fun k _ => hΛ.1.comp (by fun_prop)
  refine ⟨fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k),
    ⟨Set.univ, trivial, isRightDomain_univ, fun s _ => (hH.analyticAt s).meromorphicAt,
      max σ ((A.rank : ℝ) / 2 + 1), fun s hs => ?_⟩, hH.analyticAt _, ?_⟩
  · have hs1 : σ < s.re := (le_max_left _ _).trans_lt hs
    have hs2 : (A.rank : ℝ) / 2 + 1 < s.re := (le_max_right _ _).trans_lt hs
    refine Eq.trans ?_ ((hσ hs1).trans
      (GlobalTheory.LFun.LSTw_congr (GlobalTheory.BottomLVal.par_eq_trivPar _ _ _ par hpar) _ _).symm)
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ A.rank := by exact_mod_cast Finset.mem_range.1 hk
    rw [hν, GlobalTheory.LFun.charL_eq_of_chrEq hc]
    refine (GlobalTheory.SqStep.heckeL_eq_of_ram
      (fun w hw => (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).2 hw) hΛ ?_).symm
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  · rw [← GlobalTheory.BottomLVal.prod_range_sub (fun s => Λ s) A.rank (h0 D i j) (e0 D i j) (by exact_mod_cast r3)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    have : (A.rank : ℂ) + A'.rank = 2 * (h0 D i j : ℕ) := by exact_mod_cast r2
    push_cast
    linear_combination this / 2
