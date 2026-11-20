import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeightShift

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

/- English proof (translation)
Establish `hA : IsAlgAtlas R.finAtlas` using `R.isAlgAtlas_finAtlas`. Establish `hv' : R.SmoothOn univ v` using `(cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y`. Establish `hw : R.finAtlas.Smooth fun y => v y / 2` using `(hA.smooth_iff R).2 fun c => (hv' c).div_const 2`. Establish `hΩ` using `h.isPotential hA`. Establish `hpos` using `(h.isPosPot_iff hA).2 hp`.

Establish `hpsh : IsPsh R.finAtlas φ.locPot` using `fun x j z hz w => by`. Distinguish the cases in `h0 : w = 0`. Rewrite using `[h0, ReciprocityTheory.AnForm.levi_zero]`. Conclude with `(hpos x j z hz w h0).le`. Take `⟨C, hC⟩` from `pshShift R.finAtlas φ.locPot hΩ hpos _ hw`.

Use `⟨⌈C⌉₊, fun m hm i c y hy ξ => ?_⟩` and prove the remaining obligations. Establish `hmC : 0 ≤ (m : ℝ) - C` using `sub_nonneg.2 (Nat.ceil_le.1 hm)`. Establish `hχ : ((φ.pow m).addFn v).IsSmooth R` using `(h.zpow m).addFn hv'`. Take `⟨j, hj⟩` from `R.finAtlas.cover y`. Take `⟨c', hc'⟩` from `hA j`.

Rewrite `hj` using `[hc']`. Establish `hb : y ∈ ptsIn p σ ((lbPow B m).U fun _ => pick φ.isLB y)` using `mem_pow_iff.2 (mem_pick φ.isLB y)`. Take `⟨w, -, e⟩` from `hχ.exists_levi_eq c c' hy.1 hj hy.2 hb ξ`. Rewrite using `[hχ.leviV_re_eq c hy.1 hy.2, e]`. Establish `hz : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' φ.locPot.U y` using `mem_over c'.e hj (φ.locPot.mem_U y)`.

Establish `h₁` using `hC y j (c'.finChart y) (by rw [hc']; exact ⟨hz.1, trivial, hz.2⟩) w`. Establish `h₂` using `hpsh y j (c'.finChart y) (by rw [hc']; exact hz) w`. Rewrite `h₁`, `h₂` using `[hc']`. Establish `d₁ : ContDiffAt ℝ 2 (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) (c'.finChart y)` using `hχ.contDiffAt_finChart c' hj hb`. Establish `d₂ : ContDiffAt ℝ 2 (φ.locPot.φ y ∘ c'.finChart.symm) (c'.finChart y)` using `(h.contDiffAt_finChart c' hj (mem_pick φ.isLB y)).div_const 2`.

Establish `e₁` using `ReciprocityTheory.AnForm.levi_add_smul (w := w) (C - m) (d₁.div_const 2) d₂`. Rewrite `e₁` using `[FinChart.levi_half]`. Establish `e₂ : (LocPot.ofFun (fun y => v y / 2) + φ.locPot.rsmul C).φ y ∘ c'.finChart.symm = fun z => (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) z / 2 + (C - m) * (φ.locPot.φ y ∘ c'.finChart.symm) z`. Use function extensionality and compare the values at `z`. Use `φ.zpow_φ (m : ℤ) (fun _ => pick φ.isLB y) (c'.finChart.symm z)` as an intermediate fact.

Express the relevant statement in the definitionally equal form `v (c'.finChart.symm z) / 2 + C * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2) = ((φ.zpow (m : ℤ)).φ (fun _ => pick φ.isLB y) (c'.finChart.symm z) + v (c'.finChart.symm z)) / 2 + (C - m) * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2)`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h₁` using `[e₂, e₁]`.

Use polynomial arithmetic with `[mul_nonneg hmC h₂]`.
-/
theorem exists_semiPosReg_pow_addFn [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (R : AnRead p σ D) {φ : Weight p σ B} (h : φ.IsSmooth R) (hp : φ.StrictPos R)
    {v : CxPts p σ → ℝ} (hv : ∀ y, CInfAt v y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((φ.pow m).addFn v).SemiPosReg D := by
  have hA : IsAlgAtlas R.finAtlas := R.isAlgAtlas_finAtlas
  have hv' : R.SmoothOn univ v := (cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y
  have hw : R.finAtlas.Smooth fun y => v y / 2 :=
    (hA.smooth_iff R).2 fun c => (hv' c).div_const 2
  have hΩ := h.isPotential hA
  have hpos := (h.isPosPot_iff hA).2 hp
  have hpsh : IsPsh R.finAtlas φ.locPot := fun x j z hz w => by
    by_cases h0 : w = 0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (hpos x j z hz w h0).le
  obtain ⟨C, hC⟩ := pshShift R.finAtlas φ.locPot hΩ hpos _ hw
  refine ⟨⌈C⌉₊, fun m hm i c y hy ξ => ?_⟩
  have hmC : 0 ≤ (m : ℝ) - C := sub_nonneg.2 (Nat.ceil_le.1 hm)
  have hχ : ((φ.pow m).addFn v).IsSmooth R := (h.zpow m).addFn hv'
  obtain ⟨j, hj⟩ := R.finAtlas.cover y
  obtain ⟨c', hc'⟩ := hA j
  rw [hc'] at hj
  have hb : y ∈ ptsIn p σ ((lbPow B m).U fun _ => pick φ.isLB y) :=
    mem_pow_iff.2 (mem_pick φ.isLB y)
  obtain ⟨w, -, e⟩ := hχ.exists_levi_eq c c' hy.1 hj hy.2 hb ξ
  rw [hχ.leviV_re_eq c hy.1 hy.2, e]
  have hz : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' φ.locPot.U y :=
    mem_over c'.e hj (φ.locPot.mem_U y)
  have h₁ := hC y j (c'.finChart y) (by rw [hc']; exact ⟨hz.1, trivial, hz.2⟩) w
  have h₂ := hpsh y j (c'.finChart y) (by rw [hc']; exact hz) w
  rw [hc'] at h₁ h₂
  have d₁ : ContDiffAt ℝ 2 (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm)
      (c'.finChart y) := hχ.contDiffAt_finChart c' hj hb
  have d₂ : ContDiffAt ℝ 2 (φ.locPot.φ y ∘ c'.finChart.symm) (c'.finChart y) :=
    (h.contDiffAt_finChart c' hj (mem_pick φ.isLB y)).div_const 2
  have e₁ := ReciprocityTheory.AnForm.levi_add_smul (w := w) (C - m) (d₁.div_const 2) d₂
  rw [FinChart.levi_half] at e₁
  have e₂ : (LocPot.ofFun (fun y => v y / 2) + φ.locPot.rsmul C).φ y ∘ c'.finChart.symm =
      fun z => (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) z / 2 +
        (C - m) * (φ.locPot.φ y ∘ c'.finChart.symm) z := by
    funext z
    have := φ.zpow_φ (m : ℤ) (fun _ => pick φ.isLB y) (c'.finChart.symm z)
    change v (c'.finChart.symm z) / 2 + C * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2) =
      ((φ.zpow (m : ℤ)).φ (fun _ => pick φ.isLB y) (c'.finChart.symm z) + v (c'.finChart.symm z)) / 2 +
        (C - m) * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2)
    rw [this]
    push_cast
    ring
  rw [e₂, e₁] at h₁
  nlinarith [mul_nonneg hmC h₂]

/- English proof (translation)
Introduce `i c y hy ξ h0` and use `by have := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos (σ := σ) (𝟙 _) (Category.id_comp (PSpace.str k N)) R (fun _ => i) c y ⟨hy.1, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy.2)⟩ ξ h0 have e (z) : ((ProjAn.fsO1 k σ N).pull (𝟙 _) (Category.id_comp (PS …`.
-/
theorem strictPos_fsO1 (N : ℕ) (R : AnRead (PSpace.str k N) σ N) :
    (ProjAn.fsO1 k σ N).StrictPos R := fun i c y hy ξ h0 => by
  have := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos (σ := σ) (𝟙 _) (Category.id_comp (PSpace.str k N)) R
    (fun _ => i) c y ⟨hy.1, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy.2)⟩ ξ h0
  have e (z) : ((ProjAn.fsO1 k σ N).pull (𝟙 _) (Category.id_comp (PSpace.str k N))).φ (fun _ => i) z =
      (ProjAn.fsO1 k σ N).φ i z := by
    refine (Weight.pull_φ _ _ _ _ _).trans ?_
    have e : PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str k N)) _ z = z :=
      Subtype.ext (Category.comp_id _)
    erw [e]
  simpa only [e] using this

/- English proof (translation)
Introduce `k _ σ N v hv` and use `haveI : T2Space (CxPts (PSpace.str k N) σ) := CxPts.t2Space_cxPts_of_isProjOver σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩ exists_semiPosReg_pow_addFn (AnRead.all _ σ N) ((Weight.isCInf_iff_isSmooth _).1 ((ProjSpace.hermitianTwistingSheaf k N).cInf σ)) (strictPos_fsO1 N _) hv`.
-/
theorem exists_semiPosReg_fubiniStudy : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := fun k _ σ N v hv =>
  haveI : T2Space (CxPts (PSpace.str k N) σ) :=
    CxPts.t2Space_cxPts_of_isProjOver σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exists_semiPosReg_pow_addFn (AnRead.all _ σ N)
    ((Weight.isCInf_iff_isSmooth _).1 ((ProjSpace.hermitianTwistingSheaf k N).cInf σ)) (strictPos_fsO1 N _) hv

end GlobalTheory.WeightShift
