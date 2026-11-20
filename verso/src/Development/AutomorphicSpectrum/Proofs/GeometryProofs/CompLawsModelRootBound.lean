import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosLowerBoundSections
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge

/- English proof (translation)
Use `⟨h.1, fun f hf => ?_⟩` and prove the remaining obligations. Use `h.2 f hf` as an intermediate fact. Rewrite `this` using `[MvPolynomial.eval_map]`. Rewrite using `[MvPolynomial.aeval_def]`. Conclude with `this`.
-/
theorem mem_ptsOver_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P := by
  refine ⟨h.1, fun f hf => ?_⟩
  have := h.2 f hf
  rw [MvPolynomial.eval_map] at this
  rw [MvPolynomial.aeval_def]
  exact this

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_ringHom cst.injective`. Set `b` to `Module.finBasis ℚ F`. Take `⟨v, hv, H⟩` from `GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val K ι Ω y hb (Finset.univ.image fun i => cst (b i))`. Use `⟨v, hv, fun z hz hzv => ?_⟩` and prove the remaining obligations. Take `⟨A, ev, hB, hinv, hval⟩` from `H ℂ z (mem_ptsOver_mcPts hz) hzv`.

Establish `hq : ∀ q : ℚ, cst (algebraMap ℚ F q) ∈ A` using `fun q => by`. Establish `e : cst (algebraMap ℚ F q) = (q.num : Ω) * ((q.den : ℕ) : Ω)⁻¹`. Establish `e1 : cst (algebraMap ℚ F q) = (q : Ω)` using `eq_ratCast (cst.comp (algebraMap ℚ F)) q`. Rewrite using `[e1, Rat.cast_def, div_eq_mul_inv]`. Rewrite using `[e]`.

Conclude with `A.mul_mem (intCast_mem A _) (hinv _ q.den_nz)`. Establish `hA : ∀ t : F, cst t ∈ A` using `fun t => by`. Rewrite using `[← b.sum_repr t, map_sum]`. Use `A.sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`.

Conclude with `A.mul_mem (hq _) (hB (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))))`. Conclude with `⟨ev.comp (cst.codRestrict A hA), fun t => hval ⟨cst t, hA t⟩⟩`.
-/
theorem exists_form_const {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (hb : Birational y) {F : Type} [Field F] [NumberField F] (cst : F →+* Ω) :
    ∃ v : MRing ι, Small.IsFormOff (mCoordIdeal y) v ∧ ∀ z ∈ mcPts (mCoordIdeal y), MvPolynomial.aeval z v ≠ 0 →
      ∃ σ : F →+* ℂ, ∀ t : F, Small.HasVal y 0 (cst t) z (σ t) := by
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom cst.injective
  let b := Module.finBasis ℚ F
  obtain ⟨v, hv, H⟩ := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val K ι Ω y hb
    (Finset.univ.image fun i => cst (b i))
  refine ⟨v, hv, fun z hz hzv => ?_⟩
  obtain ⟨A, ev, hB, hinv, hval⟩ := H ℂ z (mem_ptsOver_mcPts hz) hzv
  have hq : ∀ q : ℚ, cst (algebraMap ℚ F q) ∈ A := fun q => by
    have e : cst (algebraMap ℚ F q) = (q.num : Ω) * ((q.den : ℕ) : Ω)⁻¹ := by
      have e1 : cst (algebraMap ℚ F q) = (q : Ω) := eq_ratCast (cst.comp (algebraMap ℚ F)) q
      rw [e1, Rat.cast_def, div_eq_mul_inv]
    rw [e]
    exact A.mul_mem (intCast_mem A _) (hinv _ q.den_nz)
  have hA : ∀ t : F, cst t ∈ A := fun t => by
    rw [← b.sum_repr t, map_sum]
    refine A.sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    exact A.mul_mem (hq _) (hB (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  exact ⟨ev.comp (cst.codRestrict A hA), fun t => hval ⟨cst t, hA t⟩⟩

/- English proof (translation)
Introduce `hG E _ _ _ H Dw l Xo c r U h e hL x hx O _ β Y SS RM Sys Fx Or Fr Z Rd u f hf`. Take `⟨a, ha⟩ : ∃ a, a = (GlobalTheory.AllWt.wtOf Dw u 0).1` from `⟨_, rfl⟩`. Take `⟨hw1, hw2, -, hw4, -⟩` from `GlobalTheory.CompanionTheory.Ar.Plug.integer_weights_vocab E H Dw l Xo c RM u`. Rewrite `hw1`, `hw2` using `[← ha]`. Take `⟨-, -, hco, -, -⟩` from `GlobalTheory.T.all_weight_sections_compat E H Dw l Xo c r U h e hL a Z`.

Rewrite `hf` using `[hw2, ← hco]`. Establish `hcz : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.cuspZ Xo c U a` using `hf.1`. Establish `hsec : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a` using `hcz.1`. Establish `hhol : ∀ σ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laZ (U σ) a)` using `fun σ hσ => by`. Establish `h2 : f ∈ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ))` using `hcz.2`.

Conclude with `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 σ) hσ`. Establish `hM : ∀ σ : c.F →+* ℂ, ∃ M : ℝ, 0 ≤ M ∧ (GoodEmb c σ → ∀ k, ∀ y ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laZ (U σ) a k) (rdU (U σ) f k) y ≤ M)` using `fun σ => by`. Distinguish the cases in `hσ : GoodEmb c σ`. Take `⟨M, hM⟩` from `GlobalTheory.BignessCompare.bdd_of_mem_holSub (U σ).X (laZ (U σ) a) (hhol σ hσ)`. Conclude with `⟨|M|, abs_nonneg M, fun _ k y hy => (hM ⟨k, ⟨y, hy⟩⟩).trans (le_abs_self M)⟩`.

Conclude with `⟨0, le_rfl, fun h' => absurd h' hσ⟩`. Use `choose M hM0 hMb using hM`. Take `⟨u₀, hu₀, hread⟩` from `GlobalTheory.T.component_norm_constant_models hG E H Dw l Xo c r U h e hL x hx O β Y SS RM Sys Fx Or Fr Z Rd`. Take `⟨v, hv, hcst⟩` from `exists_form_const RM.y RM.birational Or.𝔐.cst`. Establish `hform : Small.IsFormOff (mCoordIdeal RM.y) (u₀ * v)`.

Take `⟨d₁, h₁⟩` from `hu₀.1`. Take `⟨d₂, h₂⟩` from `hv.1`. Use `⟨⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h₁ h₂⟩, fun h' => ?_⟩` and prove the remaining obligations. Establish `hp : (mCoordIdeal RM.y).IsPrime` using `RingHom.ker_isPrime _`. Break down `hp.mem_or_mem h' with h' | h'` into its components or cases.

Conclude with `hu₀.2 h'`. Conclude with `hv.2 h'`. Establish `hgauge : gauge Rd u * Rd.φ (evC h Z f) = Fr.rd f * ∏ r', Or.e r' ^ (-nOf u (some r'))`. Rewrite using `[Rd.rd_eq a f hsec, gauge, ← ha]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hn' : ∀ j, (nOf u j : ℝ) = RM.coef (towerWt Dw a) 0 j` using `fun j => by`. Rewrite using `[hw1]`. Conclude with `hw4 j`. Use `⟨lieFacZ Dw x a * ∑ σ, M σ, u₀ * v, hform, fun z hz hne w hw => ?_⟩` and prove the remaining obligations. Rewrite `hne` using `[map_mul]`.

Take `⟨σ, hσ⟩` from `hcst z hz (right_ne_zero_of_mul hne)`. Take `⟨k, -, y, hy, hr⟩` from `hread σ z hz hσ (left_ne_zero_of_mul hne)`. Take `⟨θ, hθ, hval⟩` from `hr a (nOf u) hn'`. Take `⟨hg, hb⟩` from `hval f hsec`. Establish `hzp` using `mem_ptsOver_mcPts hz`.

Establish `hw' : Small.HasVal RM.y (Top.combLine (RM.line 1) (nOf u)).a (Fr.rd f * ∏ r', Or.e r' ^ (-nOf u (some r'))) z w`. Rewrite using `[← hgauge]`. Conclude with `hw`. Establish `hnorm : ‖w‖ = ‖θ‖ * ‖rdU (U (goodOf c σ)) f k y‖`. Distinguish the cases in `hgd : GoodEmb c σ`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hzp hw' (hg hgd), norm_mul]`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hzp hw' (hb hgd), norm_mul, RCLike.norm_conj]`. Establish `hP : 0 < ∏ r', (Or.sing r').h z ^ nOf u (some r')` using `Finset.prod_pos fun r' _ => zpow_pos ((Or.sing r').pos z hz.1) _`. Establish `hL0 : 0 < lieFacZ Dw x a` using `Real.exp_pos _`. Establish `hmain : ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y * ‖rdU (U (goodOf c σ)) f k y‖ = ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (rdU (U (goodOf c σ)) f k) y`.

Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbd : ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (rdU (U (goodOf c σ)) f k) y ≤ ∑ σ, M σ` using `(hMb _ (goodEmb_goodOf c σ) k y hy).trans (Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_univ _))`. Rewrite using `[hnorm, hθ, mul_assoc, mul_assoc, hmain]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cusp_hodgeLe : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), ∃ R : ℝ, HodgeLe Or u (gauge Rd u * Rd.φ (evC h Z f)) R := by
  intro hG E _ _ _ H Dw l Xo c r U h e hL x hx O _ β Y SS RM Sys Fx Or Fr Z Rd u f hf
  classical
  obtain ⟨a, ha⟩ : ∃ a, a = (GlobalTheory.AllWt.wtOf Dw u 0).1 := ⟨_, rfl⟩
  obtain ⟨hw1, hw2, -, hw4, -⟩ := GlobalTheory.CompanionTheory.Ar.Plug.integer_weights_vocab E H Dw l Xo c RM u
  rw [← ha] at hw1 hw2
  obtain ⟨-, -, hco, -, -⟩ := GlobalTheory.T.all_weight_sections_compat E H Dw l Xo c r U h e hL a Z
  rw [hw2, ← hco] at hf
  have hcz : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.cuspZ Xo c U a := hf.1
  have hsec : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a := hcz.1
  have hhol : ∀ σ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laZ (U σ) a) := fun σ hσ => by
    have h2 : f ∈ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ)) := hcz.2
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 σ) hσ
  have hM : ∀ σ : c.F →+* ℂ, ∃ M : ℝ, 0 ≤ M ∧ (GoodEmb c σ → ∀ k, ∀ y ∈ ((U σ).X k).dom,
      ((U σ).X k).pnorm (laZ (U σ) a k) (rdU (U σ) f k) y ≤ M) := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨M, hM⟩ := GlobalTheory.BignessCompare.bdd_of_mem_holSub (U σ).X (laZ (U σ) a) (hhol σ hσ)
      exact ⟨|M|, abs_nonneg M, fun _ k y hy => (hM ⟨k, ⟨y, hy⟩⟩).trans (le_abs_self M)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hσ⟩
  choose M hM0 hMb using hM
  obtain ⟨u₀, hu₀, hread⟩ := GlobalTheory.T.component_norm_constant_models hG E H Dw l Xo c r U h e hL x hx O β Y SS RM Sys Fx Or Fr Z Rd
  obtain ⟨v, hv, hcst⟩ := exists_form_const RM.y RM.birational Or.𝔐.cst
  have hform : Small.IsFormOff (mCoordIdeal RM.y) (u₀ * v) := by
    obtain ⟨d₁, h₁⟩ := hu₀.1
    obtain ⟨d₂, h₂⟩ := hv.1
    refine ⟨⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h₁ h₂⟩, fun h' => ?_⟩
    have hp : (mCoordIdeal RM.y).IsPrime := RingHom.ker_isPrime _
    rcases hp.mem_or_mem h' with h' | h'
    · exact hu₀.2 h'
    · exact hv.2 h'
  have hgauge : gauge Rd u * Rd.φ (evC h Z f) = Fr.rd f * ∏ r', Or.e r' ^ (-nOf u (some r')) := by
    rw [Rd.rd_eq a f hsec, gauge, ← ha]
    ring
  have hn' : ∀ j, (nOf u j : ℝ) = RM.coef (towerWt Dw a) 0 j := fun j => by
    rw [hw1]
    exact hw4 j
  refine ⟨lieFacZ Dw x a * ∑ σ, M σ, u₀ * v, hform, fun z hz hne w hw => ?_⟩
  rw [map_mul] at hne
  obtain ⟨σ, hσ⟩ := hcst z hz (right_ne_zero_of_mul hne)
  obtain ⟨k, -, y, hy, hr⟩ := hread σ z hz hσ (left_ne_zero_of_mul hne)
  obtain ⟨θ, hθ, hval⟩ := hr a (nOf u) hn'
  obtain ⟨hg, hb⟩ := hval f hsec
  have hzp := mem_ptsOver_mcPts hz
  have hw' : Small.HasVal RM.y (Top.combLine (RM.line 1) (nOf u)).a
      (Fr.rd f * ∏ r', Or.e r' ^ (-nOf u (some r'))) z w := by
    rw [← hgauge]
    exact hw
  have hnorm : ‖w‖ = ‖θ‖ * ‖rdU (U (goodOf c σ)) f k y‖ := by
    by_cases hgd : GoodEmb c σ
    · rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hzp hw' (hg hgd), norm_mul]
    · rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hzp hw' (hb hgd), norm_mul, RCLike.norm_conj]
  have hP : 0 < ∏ r', (Or.sing r').h z ^ nOf u (some r') :=
    Finset.prod_pos fun r' _ => zpow_pos ((Or.sing r').pos z hz.1) _
  have hL0 : 0 < lieFacZ Dw x a := Real.exp_pos _
  have hmain : ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y * ‖rdU (U (goodOf c σ)) f k y‖ =
      ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (rdU (U (goodOf c σ)) f k) y := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]
    ring
  have hbd : ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (rdU (U (goodOf c σ)) f k) y ≤ ∑ σ, M σ :=
    (hMb _ (goodEmb_goodOf c σ) k y hy).trans
      (Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_univ _))
  rw [hnorm, hθ, mul_assoc, mul_assoc, hmain]
  calc _ ≤ (∏ r', (Or.sing r').h z ^ nOf u (some r')) * (lieFacZ Dw x a * ∑ σ, M σ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbd hL0.le) hP.le
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.Plug.CuspHodge
