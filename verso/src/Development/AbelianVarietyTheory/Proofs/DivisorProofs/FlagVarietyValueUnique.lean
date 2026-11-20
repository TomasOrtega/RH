import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightPolynomialInDegrees
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmWd

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `h : (lin x).IsHomogeneous 1` using `IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X ℝ i).C_mul _`. Simplify using `using h.pow D`.
-/
theorem isHomogeneous_lin_pow (x : ι → ℝ) (D : ℕ) : (lin x ^ D).IsHomogeneous D := by
  have h : (lin x).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X ℝ i).C_mul _
  simpa using h.pow D

/- English proof (translation)
Use `⟨T ∘ₗ homogeneousComponent D, fun x => ?_, fun P d hd hP => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, homogeneousComponent_of_mem (isHomogeneous_lin_pow x D), if_pos rfl]`. Rewrite using `[LinearMap.comp_apply, homogeneousComponent_of_mem hP, if_neg hd.symm, map_zero]`.
-/
theorem exists_cut (T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (D : ℕ) : ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ,
    (∀ x : ι → ℝ, Φ (lin x ^ D) = T (lin x ^ D)) ∧
      ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Φ P = 0 := by
  refine ⟨T ∘ₗ homogeneousComponent D, fun x => ?_, fun P d hd hP => ?_⟩
  · rw [LinearMap.comp_apply, homogeneousComponent_of_mem (isHomogeneous_lin_pow x D), if_pos rfl]
  · rw [LinearMap.comp_apply, homogeneousComponent_of_mem hP, if_neg hd.symm, map_zero]

/- English proof (translation)
Break down `hY.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, e', he'⟩` into its components or cases. Conclude with `GlobalTheory.VertFun.exists_vertical_functional k Y p D hY Z i ℓ e he ι L`. Take `rfl : e = e' + 1` from `by exact_mod_cast he.symm.trans he'`. Establish `hZ : IsArithVar (i ≫ p) e'` using `hY.of_isClosedImmersion i hc he`. Take `⟨Ψ, hΨ⟩` from `((hC.arExists k Z (i ≫ p) e' hZ).2 ι (fun j => (L j).restr i)).1`.

Use `⟨Ψ, fun n g hg => ?_⟩` and prove the remaining obligations. Establish `e₁ : ((comb L n).restr i).Isometric (comb (fun j => (L j).restr i) n)` using `(isometric_comb_pull L n i rfl).symm`. Conclude with `(e₁.isSelfInter hZ (hg.isSelfInter_restrict hY i rfl)).unique hZ (hΨ.1 n)`.
-/
theorem exists_height_functional (hC : ArCalc) {D : ℕ} (hY : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] {e : ℕ} (he : topologicalKrullDim Z = e) (L : ι → HermLB p) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ e) := by
  rcases hY.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, e', he'⟩
  · exact GlobalTheory.VertFun.exists_vertical_functional k Y p D hY Z i ℓ e he ι L
  · obtain rfl : e = e' + 1 := by exact_mod_cast he.symm.trans he'
    have hZ : IsArithVar (i ≫ p) e' := hY.of_isClosedImmersion i hc he
    obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Z (i ≫ p) e' hZ).2 ι (fun j => (L j).restr i)).1
    refine ⟨Ψ, fun n g hg => ?_⟩
    have e₁ : ((comb L n).restr i).Isometric (comb (fun j => (L j).restr i) n) :=
      (isometric_comb_pull L n i rfl).symm
    exact (e₁.isSelfInter hZ (hg.isSelfInter_restrict hY i rfl)).unique hZ (hΨ.1 n)

/- English proof (translation)
Establish `h₁` using `(genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme).image (redι (clo y)).continuous`. Rewrite `h₁` using `[Set.image_univ, range_redι]`. Use `h₁.eq ?_` and prove the remaining obligations. Conclude with `closure_closure.symm`.
-/
theorem redι_clo (y : Y) : redι (clo y) (genericPoint _) = y := by
  have h₁ := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme).image
    (redι (clo y)).continuous
  rw [Set.image_univ, range_redι] at h₁
  refine h₁.eq ?_
  exact closure_closure.symm

/- English proof (translation)
The claim follows from `(topologicalKrullDim_eq_of_isEmbedding (redι (clo y)).isClosedEmbedding.isEmbedding (range_redι (clo y))).symm`.
-/
theorem dim_clo (y : Y) : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme =
    topologicalKrullDim (closure ({y} : Set Y)) :=
  (topologicalKrullDim_eq_of_isEmbedding (redι (clo y)).isClosedEmbedding.isEmbedding (range_redι (clo y))).symm

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_height_functional hC hY (redι (clo y)) ((dim_clo y).trans he) L`. Take `⟨Φ, h₁, h₂⟩` from `exists_cut T e`. Use `⟨Φ, fun n => ?_, h₂⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `(hC.arExists k Y p D hY).1 (comb L n)`. Conclude with `⟨g, hg, by rw [h₁, ← hT n g hg, redι_clo]⟩`.
-/
theorem exists_isHtFun (hC : ArCalc) [IsIntegral Y] {D : ℕ} (hY : IsArithVar p D) (L : ι → HermLB p) (y : Y) {e : ℕ}
    (he : topologicalKrullDim (closure ({y} : Set Y)) = e) : ∃ Φ, IsHtFun L y e Φ := by
  obtain ⟨T, hT⟩ := exists_height_functional hC hY (redι (clo y)) ((dim_clo y).trans he) L
  obtain ⟨Φ, h₁, h₂⟩ := exists_cut T e
  refine ⟨Φ, fun n => ?_, h₂⟩
  obtain ⟨g, hg⟩ := (hC.arExists k Y p D hY).1 (comb L n)
  exact ⟨g, hg, by rw [h₁, ← hT n g hg, redι_clo]⟩

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (Model.eq_zero_of_pow e _ (fun n => sub_eq_zero.2 (by obtain ⟨g, hg, e₁⟩ := h.1 n obtain ⟨g', hg', e₂⟩ := h'.1 n rw [← e₁, ← e₂, hg.unique hY hg'])) fun P d hd hP => sub_eq_zero.2 ((h.2 P d hd hP).trans (h'.2 P d hd hP).symm))`.
-/
theorem isHtFun_unique {D : ℕ} (hY : IsArithVar p D) {L : ι → HermLB p} {y : Y} {e : ℕ}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : IsHtFun L y e Φ) (h' : IsHtFun L y e Φ') : Φ = Φ' :=
  sub_eq_zero.1 (Model.eq_zero_of_pow e _ (fun n => sub_eq_zero.2 (by
      obtain ⟨g, hg, e₁⟩ := h.1 n
      obtain ⟨g', hg', e₂⟩ := h'.1 n
      rw [← e₁, ← e₂, hg.unique hY hg']))
    fun P d hd hP => sub_eq_zero.2 ((h.2 P d hd hP).trans (h'.2 P d hd hP).symm))

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (Model.eq_zero_of_pow e _ (fun n => sub_eq_zero.2 ((h.1 n).trans (h'.1 n).symm)) fun P d hd hP => sub_eq_zero.2 ((h.2 P d hd hP).trans (h'.2 P d hd hP).symm))`.
-/
theorem isIntFun_unique {L : ι → HermLB p} {f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {e : ℕ}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : IsIntFun L f e Φ) (h' : IsIntFun L f e Φ') : Φ = Φ' :=
  sub_eq_zero.1 (Model.eq_zero_of_pow e _ (fun n => sub_eq_zero.2 ((h.1 n).trans (h'.1 n).symm))
    fun P d hd hP => sub_eq_zero.2 ((h.2 P d hd hP).trans (h'.2 P d hd hP).symm))

/- English proof (translation)
Use `hY.isLocallyNoetherian` as an intermediate fact. Use `hY.isNoetherian` as an intermediate fact. Establish `hr` using `isRatSec_ratOfSec s hs`. Take `⟨Φ, hΦ⟩` from `((hC.arExists k Y p D hY).2 (Option ι) (fun o => o.elim M L)).1`. Establish `hT (z : Y) : ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (M.div hr).mult z ≠ 0 → ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g → g z = T (lin (fun j => (n j : ℝ)) ^ D)`.

Distinguish the cases in `hz : (M.div hr).mult z = 0`. Conclude with `⟨0, fun h => absurd hz h⟩`. Take `⟨Z, i, _, _, rfl⟩` from `exists_isClosedImmersion_genericPoint z`. Take `⟨T, hT⟩` from `exists_height_functional hC hY i (GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one k Y p D hY Z i (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)) L`. Conclude with `⟨T, fun _ => hT⟩`.

Use `choose T hT using hT`. Establish `hfin` using `(M.div hr).finite_support_mult`. Take `⟨Λ, h₁, h₂⟩` from `exists_cut (∑ z ∈ hfin.toFinset, ((M.div hr).mult z : ℝ) • T z - Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (some : ι → Option ι)).toLinearMap) D`. Use `⟨Λ, fun n => ?_, h₂⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `(hC.arExists k Y p D hY).1 (comb L n)`.

Establish `hmix` using `(hC.arMix k Y p D hY ι M L Φ hΦ n g hg _ hr).2`. Establish `e₁ : (comb L n).archInt M D hr = chInt (comb L n) D fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2`. Use `finsum_congr fun σ => ?_` and prove the remaining obligations. Establish `hnull (ε : ℤˣ) : ((comb L n).φ σ).chernPart D ε (offSupp p σ (M.div hr))ᶜ = 0`. Establish `e : (offSupp p σ (M.div hr))ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((M.div hr).supp : Set Y)}`.

Use extensionality with `y`. Simplify using `only [Set.mem_compl_iff, mem_offSupp, not_not]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `GlobalTheory.ChernNull.chernPart_over_closed hY _ (M.div hr).supp.isClosed (CartierDiv.genericPoint_notMem_supp _) σ _ ε`.

Rewrite using `[Weight.chernInt_congr (g := fun v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2) (isOpen_offSupp _).measurableSet fun y hy => logNorm_ratOfSec _ ((offSupp_divOfSec (q := p) (σ := σ) (hL := M.isLB) (hs := hs)).le hy)]`. Simplify using `only [Weight.chernInt, MeasureTheory.Measure.restrict_univ]`. Rewrite using `[MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (divOfSec M.isLB s hs)) (hnull 1), MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (divOfSec M.isLB s hs)) (hnull (-1))]`. Establish `e₂ : ∑ᶠ z, ((M.div hr).mult z : ℝ) * g z = ∑ z ∈ hfin.toFinset, ((M.div hr).mult z : ℝ) * T z (lin (fun j => (n j : ℝ)) ^ D)`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun z hz => by`.

Simplify using `using fun h0 : (M.div hr).mult z = 0 => hz (by simp [h0])]`. Conclude with `Finset.sum_congr rfl fun z hz => by rw [hT z (by simpa using hz) n g hg]`. Rewrite using `[h₁, ← e₁, LinearMap.sub_apply, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_pow]`. Rewrite using `[hmix, e₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isIntFun_horizontal (hC : ArCalc) [IsIntegral Y] {D : ℕ} (hY : IsArithVar p D) (L : ι → HermLB p)
    (M : HermLB p) (s : M.B.Sec) (hs : genericPoint Y ∈ Out.nonzeroLocus s) :
    ∃ Λ, IsIntFun L (fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2) D Λ := by
  have := hY.isLocallyNoetherian
  have := hY.isNoetherian
  have hr := isRatSec_ratOfSec s hs
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hY).2 (Option ι) (fun o => o.elim M L)).1
  have hT (z : Y) : ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (M.div hr).mult z ≠ 0 → ∀ (n : ι → ℤ) (g : Y → ℝ),
      (comb L n).IsArithHeight g → g z = T (lin (fun j => (n j : ℝ)) ^ D) := by
    by_cases hz : (M.div hr).mult z = 0
    · exact ⟨0, fun h => absurd hz h⟩
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    obtain ⟨T, hT⟩ := exists_height_functional hC hY i (GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one
      k Y p D hY Z i (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)) L
    exact ⟨T, fun _ => hT⟩
  choose T hT using hT
  have hfin := (M.div hr).finite_support_mult
  obtain ⟨Λ, h₁, h₂⟩ := exists_cut (∑ z ∈ hfin.toFinset, ((M.div hr).mult z : ℝ) • T z -
    Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (some : ι → Option ι)).toLinearMap) D
  refine ⟨Λ, fun n => ?_, h₂⟩
  obtain ⟨g, hg⟩ := (hC.arExists k Y p D hY).1 (comb L n)
  have hmix := (hC.arMix k Y p D hY ι M L Φ hΦ n g hg _ hr).2
  have e₁ : (comb L n).archInt M D hr =
      chInt (comb L n) D fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2 := by
    refine finsum_congr fun σ => ?_
    have hnull (ε : ℤˣ) : ((comb L n).φ σ).chernPart D ε (offSupp p σ (M.div hr))ᶜ = 0 := by
      have e : (offSupp p σ (M.div hr))ᶜ =
          {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((M.div hr).supp : Set Y)} := by
        ext y
        simp only [Set.mem_compl_iff, mem_offSupp, not_not]
        rfl
      rw [e]
      exact GlobalTheory.ChernNull.chernPart_over_closed hY _ (M.div hr).supp.isClosed
        (CartierDiv.genericPoint_notMem_supp _) σ _ ε
    rw [Weight.chernInt_congr (g := fun v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2)
      (isOpen_offSupp _).measurableSet fun y hy => logNorm_ratOfSec _ ((offSupp_divOfSec (q := p) (σ := σ) (hL := M.isLB) (hs := hs)).le hy)]
    simp only [Weight.chernInt, MeasureTheory.Measure.restrict_univ]
    rw [MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (divOfSec M.isLB s hs)) (hnull 1),
      MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (divOfSec M.isLB s hs)) (hnull (-1))]
  have e₂ : ∑ᶠ z, ((M.div hr).mult z : ℝ) * g z =
      ∑ z ∈ hfin.toFinset, ((M.div hr).mult z : ℝ) * T z (lin (fun j => (n j : ℝ)) ^ D) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) fun z hz => by
      simpa using fun h0 : (M.div hr).mult z = 0 => hz (by simp [h0])]
    exact Finset.sum_congr rfl fun z hz => by rw [hT z (by simpa using hz) n g hg]
  rw [h₁, ← e₁, LinearMap.sub_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, map_pow]
  rw [hmix, e₂]
  ring

/- English proof (translation)
Use `⟨fun y => ?_⟩` and prove the remaining obligations. Set `f : ZMod ℓ →+* ℂ` to `((y.1.appTop ≫ (Scheme.ΓSpecIso (.of ℂ)).hom).hom).comp (algebraMap (ZMod ℓ) Γ(Y, ⊤))`. Establish `h` using `map_natCast f ℓ`. Rewrite `h` using `[ZMod.natCast_self, map_zero]`. Conclude with `(Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast h.symm)`.
-/
theorem isEmpty_cxPts (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ(Y, ⊤)] (σ : k →+* ℂ) : IsEmpty (CxPts p σ) := by
  refine ⟨fun y => ?_⟩
  let f : ZMod ℓ →+* ℂ := ((y.1.appTop ≫ (Scheme.ΓSpecIso (.of ℂ)).hom).hom).comp (algebraMap (ZMod ℓ) Γ(Y, ⊤))
  have h := map_natCast f ℓ
  rw [ZMod.natCast_self, map_zero] at h
  exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast h.symm)

/- English proof (translation)
Break down `hY.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩` into its components or cases. Use `⟨0, fun n => (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm, fun _ _ _ _ => rfl⟩` and prove the remaining obligations. Use `isEmpty_cxPts (p := i ≫ p) ℓ σ` as an intermediate fact. Simplify using `[Weight.chernInt, MeasureTheory.integral_of_isEmpty]`. Conclude with `exists_isIntFun_horizontal hC (hY.of_isClosedImmersion i hc he) _ M s hs`.
-/
theorem exists_isIntFun (hC : ArCalc) {D : ℕ} (hY : IsArithVar p D) (L : ι → HermLB p) {Z : Scheme.{0}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] {e : ℕ} (he : topologicalKrullDim Z = (e + 1 : ℕ))
    (M : HermLB (i ≫ p)) (s : M.B.Sec) (hs : genericPoint Z ∈ Out.nonzeroLocus s) :
    ∃ Λ, IsIntFun (fun o => (L o).restr i) (fun σ v => Real.log ((M.φ σ).nsq (secVal _ σ s) v) / 2) e Λ := by
  rcases hY.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
  · refine ⟨0, fun n => (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm, fun _ _ _ _ => rfl⟩
    have := isEmpty_cxPts (p := i ≫ p) ℓ σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  · exact exists_isIntFun_horizontal hC (hY.of_isClosedImmersion i hc he) _ M s hs

/- English proof (translation)
The claim follows from `((h.2 y' h'.1).antisymm (h'.2 y h.1)).eq`.
-/
theorem isTop_unique {X : Scheme.{0}} {E : X.Modules} {r : ℕ} {F : FlagSp E r} {z : X} {y y' : F.Y}
    (h : F.IsTop z y) (h' : F.IsTop z y') : y = y' :=
  ((h.2 y' h'.1).antisymm (h'.2 y h.1)).eq

/- English proof (translation)
Introduce `hC k _ X _ _ p d hX E r h H F N z e`. Take `⟨hY, -, hz⟩` from `(GlobalTheory.T.flag_variety_arith_dimension k X p d hX E r h.isVB).2 F`. Take `⟨y, hy, -, hd⟩` from `hz z`. Use `hY.isIntegral` as an intermediate fact. Use `⟨fun he => ?_, fun he M s hs => ?_⟩` and prove the remaining obligations.

Take `⟨Φ, hΦ⟩` from `exists_isHtFun hC hY (F.fam H N) y (hd _ he)`. Use `⟨_, ⟨y, Φ, hy, hΦ, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y', Φ', hy', hΦ', rfl⟩`. Take `rfl` from `isTop_unique hy hy'`. Rewrite using `[isHtFun_unique hY hΦ hΦ']`.

Establish `hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme = (e + 2 + r.choose 2 + 1 : ℕ)`. Rewrite using `[dim_clo, hd _ he]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Take `⟨Λ, hΛ⟩` from `exists_isIntFun hC hY (F.fam H N) (redι (clo y)) hdim (M.pull (redι (clo y) ≫ F.π) (Category.assoc _ _ _)) (Cartier.secPull s _) (by`.

Use `(Cartier.nonzeroLocus_secPull s _).ge ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.π (redι (clo y) (genericPoint _)) ∈ Out.nonzeroLocus s`. Rewrite using `[redι_clo, hy.1]`. Conclude with `hs)`. Establish `hΛ' : IsIntFun (fun o => (F.fam H N o).restr (redι (clo y))) (fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s) (PtsOver.map (redι (clo y) ≫ F.π) (Category.assoc _ _ _) (spMap σ) v)) / 2) (e + 2 + r.choose 2) Λ`.

Use `hΛ using 4 with σ v` and compare the differences between its conclusion and the goal. Conclude with `congrArg Real.log ((M.φ σ).nsq_pull_secPull (redι (clo y) ≫ F.π) (Category.assoc _ _ _) s v).symm`. Use `⟨_, ⟨y, Λ, hy, hΛ', rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y', Λ', hy', hΛ'', rfl⟩`. Take `rfl` from `isTop_unique hy hy'`.

Rewrite using `[isIntFun_unique hΛ' hΛ'']`.
-/
theorem existsUnique_val_arch : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p), ∀ (z : X) (e : ℕ), (topologicalKrullDim (closure ({z} : Set X)) = (e + 2 : ℕ) → ∃! a, F.IsVal H N z e a) ∧ (topologicalKrullDim (closure ({z} : Set X)) = (e + 3 : ℕ) → ∀ (M : HermLB p) (s : M.B.Sec), z ∈ Out.nonzeroLocus s → ∃! a, F.IsArch H N M s z e a) := by
  intro hC k _ X _ _ p d hX E r h H F N z e
  obtain ⟨hY, -, hz⟩ := (GlobalTheory.T.flag_variety_arith_dimension k X p d hX E r h.isVB).2 F
  obtain ⟨y, hy, -, hd⟩ := hz z
  have := hY.isIntegral
  refine ⟨fun he => ?_, fun he M s hs => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := exists_isHtFun hC hY (F.fam H N) y (hd _ he)
    refine ⟨_, ⟨y, Φ, hy, hΦ, rfl⟩, ?_⟩
    rintro _ ⟨y', Φ', hy', hΦ', rfl⟩
    obtain rfl := isTop_unique hy hy'
    rw [isHtFun_unique hY hΦ hΦ']
  · have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme =
        (e + 2 + r.choose 2 + 1 : ℕ) := by
      rw [dim_clo, hd _ he]
      congr 1
      omega
    obtain ⟨Λ, hΛ⟩ := exists_isIntFun hC hY (F.fam H N) (redι (clo y)) hdim
      (M.pull (redι (clo y) ≫ F.π) (Category.assoc _ _ _)) (Cartier.secPull s _) (by
        refine (Cartier.nonzeroLocus_secPull s _).ge ?_
        change F.π (redι (clo y) (genericPoint _)) ∈ Out.nonzeroLocus s
        rw [redι_clo, hy.1]
        exact hs)
    have hΛ' : IsIntFun (fun o => (F.fam H N o).restr (redι (clo y)))
        (fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s)
          (PtsOver.map (redι (clo y) ≫ F.π) (Category.assoc _ _ _) (spMap σ) v)) / 2) (e + 2 + r.choose 2) Λ := by
      convert hΛ using 4 with σ v
      exact congrArg Real.log ((M.φ σ).nsq_pull_secPull (redι (clo y) ≫ F.π) (Category.assoc _ _ _) s v).symm
    refine ⟨_, ⟨y, Λ, hy, hΛ', rfl⟩, ?_⟩
    rintro _ ⟨y', Λ', hy', hΛ'', rfl⟩
    obtain rfl := isTop_unique hy hy'
    rw [isIntFun_unique hΛ' hΛ'']

end GlobalTheory.VdmWd

end
