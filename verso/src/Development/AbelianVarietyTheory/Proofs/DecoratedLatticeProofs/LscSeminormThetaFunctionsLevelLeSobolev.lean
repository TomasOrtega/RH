import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsOpenLevelCompleteSobolevStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.SobBaire

open Filter Topology
open scoped Uniformity

/- English proof (translation)
Use `letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology`. Establish `hp : WithSeminorms p` using `⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup`. Use `letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E`. Use `haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup`.

Use `haveI : ContinuousSMul ℂ E := hp.continuousSMul`. Use `haveI : FirstCountableTopology E := hp.firstCountableTopology`. Use `haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated`. Use `haveI : CompleteSpace E := by`. Use `UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_` and prove the remaining obligations.

Rewrite `hu` using `[cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]`. Take `⟨x, hx⟩` from `hcomp u fun d ε hε => by`. Establish `h` using `(hp.tendsto_nhds _ 0).1 hu d ε hε`. Take `⟨⟨N₁, N₂⟩, hN⟩` from `eventually_atTop.1 h`. Use `⟨max N₁ N₂, fun i hi j hj => ?_⟩` and prove the remaining obligations.

Use `hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)` as an intermediate fact. Simplify using `using this`. Use `⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩` and prove the remaining obligations. Conclude with `(hx d).eventually (gt_mem_nhds hε)`. Use `haveI : BarrelledSpace ℂ E := inferInstance`.

Establish `hlsc : LowerSemicontinuous q`. Rewrite using `[lowerSemicontinuous_iff_isClosed_preimage]`. Introduce `y`. Use `IsSeqClosed.isClosed fun u x hu hx => ?_` and prove the remaining obligations. Conclude with `hq u x (fun d => by`.

Use `((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)` as an intermediate fact. Simplify `this) y hu` using `[Function.comp_def]`. Establish `hc : Continuous q` using `Seminorm.continuous_of_lowerSemicontinuous q hlsc`. Take `⟨s, C, -, hle⟩` from `Seminorm.bound_of_continuous hp q hc`. Establish `hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x` using `fun d d' x h => by`.

Proceed by induction on `h with`. Consider the case `refl => exact le_rfl`. Consider the case `step _ ih => exact ih.trans (hmono _ x)`. Use `⟨s.sup id, C, fun x => (hle x).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]`.

Use `mul_le_mul_of_nonneg_left ?_ C.2` and prove the remaining obligations. Conclude with `Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)`.
-/
theorem exists_bound_of_complete {E : Type} [AddCommGroup E] [Module ℂ E] (p : ℕ → Seminorm ℂ E)
    (hmono : ∀ d x, p d x ≤ p (d + 1) x)
    (hcomp : ∀ u : ℕ → E, (∀ d, ∀ ε > 0, ∃ J, ∀ i ≥ J, ∀ j ≥ J, p d (u i - u j) < ε) →
      ∃ x, ∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0))
    (q : Seminorm ℂ E) (hq : ∀ (u : ℕ → E) (x : E), (∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0)) →
      ∀ y : ℝ, (∀ j, q (u j) ≤ y) → q x ≤ y) :
    ∃ (d : ℕ) (C : ℝ≥0), ∀ x, q x ≤ C * p d x := by
  letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology
  have hp : WithSeminorms p := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    obtain ⟨x, hx⟩ := hcomp u fun d ε hε => by
      have h := (hp.tendsto_nhds _ 0).1 hu d ε hε
      obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
      refine ⟨max N₁ N₂, fun i hi j hj => ?_⟩
      have := hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)
      simpa using this
    refine ⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩
    exact (hx d).eventually (gt_mem_nhds hε)
  haveI : BarrelledSpace ℂ E := inferInstance
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    refine IsSeqClosed.isClosed fun u x hu hx => ?_
    exact hq u x (fun d => by
      have := ((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)
      simpa [Function.comp_def] using this) y hu
  have hc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous q hlsc
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hp q hc
  have hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x := fun d d' x h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ x)
  refine ⟨s.sup id, C, fun x => (hle x).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ C.2
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)

end GlobalTheory.SobBaire

namespace GlobalTheory.SobBaire

open Filter Topology

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc`. Establish `hB` using `GlobalTheory.T.thetaFunctions_open_level_complete_sobolev D ψ hψ θ hθ S T μ 𝓕 hm U hU`. Set `E` to `thetaLevel ψ S T U`. Establish `hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤` using `fun d f => GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d`. Set `p : ℕ → Seminorm ℂ E` to `fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal) (fun f g => by`.

Rewrite using `[← ENNReal.toReal_add (hsf d f) (hsf d g)]`. Conclude with `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩) (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))`. Use the proof step `(fun c f => by show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _`. Rewrite using `[GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])`. Establish `hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal` using `fun _ _ => rfl`.

Set `q : Seminorm ℂ E` to `Seminorm.of (fun f => (N f).toReal) (fun f g => by`. Rewrite using `[← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]`. Conclude with `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))`. Use the proof step `(fun c f => by show (N (c • (f : WO S T → ℂ))).toReal = _`. Rewrite using `[hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])`.

Establish `hq : ∀ f : E, q f = (N f).toReal` using `fun _ => rfl`. Take `⟨d, C, hC⟩` from `exists_bound_of_complete p (fun d f => by`. Rewrite using `[hp, hp]`. Conclude with `ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))`. Use the proof step `(fun u hu => by`.

Take `⟨f, hf, hlim⟩` from `hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by`. Break down `eq_or_ne ε ⊤ with rfl | hεt` into its components or cases. Conclude with `⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩`. Take `⟨J, hJ⟩` from `hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)`. Use `⟨J, fun i hi j hj => ?_⟩` and prove the remaining obligations.

Use `hJ i hi j hj` as an intermediate fact. Rewrite `this` using `[hp]`. Conclude with `(ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this`. Use `⟨⟨f, hf⟩, fun d => ?_⟩` and prove the remaining obligations. Use `(ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)` as an intermediate fact.

Simplify `this)` using `[hp, Function.comp_def]`. Use `q (fun u x hux y hy => by`. Establish `hy0 : 0 ≤ y` using `(apply_nonneg q (u 0)).trans (hy 0)`. Establish `hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0)` using `fun d => by`. Establish `h1` using `hux d`.

Simplify using `only [hp] at h1`. Rewrite `h1` using `[← ENNReal.toReal_zero]`. Conclude with `(ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1`. Establish `h2` using `hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv`. Establish `h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y` using `Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by`.

Rewrite using `[← ENNReal.ofReal_toReal (hfin _ (u j).2)]`. Conclude with `ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))`. Rewrite using `[hq]`. Conclude with `ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))`. Use `⟨d, C, fun f hf => ?_⟩` and prove the remaining obligations.

Establish `h` using `hC ⟨f, hf⟩`. Rewrite `h` using `[hq, hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]`.
-/
theorem le_mul_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ thetaLevel ψ S T U, ∀ g ∈ thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f ∈ thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc
  have hB := GlobalTheory.T.thetaFunctions_open_level_complete_sobolev D ψ hψ θ hθ S T μ 𝓕 hm U hU
  let E := thetaLevel ψ S T U
  have hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤ := fun d f =>
    GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d
  let p : ℕ → Seminorm ℂ E := fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hsf d f) (hsf d g)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩)
        (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))
    (fun c f => by
      show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _
      rw [GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])
  have hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal := fun _ _ => rfl
  let q : Seminorm ℂ E := Seminorm.of (fun f => (N f).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))
    (fun c f => by
      show (N (c • (f : WO S T → ℂ))).toReal = _
      rw [hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])
  have hq : ∀ f : E, q f = (N f).toReal := fun _ => rfl
  obtain ⟨d, C, hC⟩ := exists_bound_of_complete p
    (fun d f => by
      rw [hp, hp]
      exact ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))
    (fun u hu => by
      obtain ⟨f, hf, hlim⟩ := hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by
        rcases eq_or_ne ε ⊤ with rfl | hεt
        · exact ⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩
        obtain ⟨J, hJ⟩ := hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
        refine ⟨J, fun i hi j hj => ?_⟩
        have := hJ i hi j hj
        rw [hp] at this
        exact (ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this
      refine ⟨⟨f, hf⟩, fun d => ?_⟩
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)
      simpa [hp, Function.comp_def] using this)
    q (fun u x hux y hy => by
      have hy0 : 0 ≤ y := (apply_nonneg q (u 0)).trans (hy 0)
      have hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0) := fun d => by
        have h1 := hux d
        simp only [hp] at h1
        rw [← ENNReal.toReal_zero] at h1
        exact (ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1
      have h2 := hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv
      have h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y :=
        Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by
          rw [← ENNReal.ofReal_toReal (hfin _ (u j).2)]
          exact ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))
      rw [hq]
      exact ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))
  refine ⟨d, C, fun f hf => ?_⟩
  have h := hC ⟨f, hf⟩
  rw [hq, hp] at h
  calc N f = ENNReal.ofReal (N f).toReal := (ENNReal.ofReal_toReal (hfin f hf)).symm
    _ ≤ ENNReal.ofReal (C * (sobO ψ θ μ 𝓕 d f).toReal) := ENNReal.ofReal_le_ofReal h
    _ = C * sobO ψ θ μ 𝓕 d f := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]

end GlobalTheory.SobBaire
