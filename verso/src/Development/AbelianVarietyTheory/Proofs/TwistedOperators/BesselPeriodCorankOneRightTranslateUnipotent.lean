import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusUnip

variable {D : D7}

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B`. Take `⟨j1, j2, j3, j4⟩` from `GlobalTheory.Mem.TrueRecord.top_NFlag B he`. Take `⟨u1, u2, u3⟩` from `hN`. Use `haveI : DiscreteTopology (NFlagQ B e) := by`. Use `DiscreteTopology.of_continuous_injective (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B)) ?_ ?_` and prove the remaining obligations.

Conclude with `Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _`. Introduce `a b hab`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) hab))`. Take `⟨K, hK, hcov⟩` from `(GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1`. Establish `hcov' : ∀ x : NFlag B e, ∃ s ∈ NFlagQ B e, s * x ∈ K` using `fun x => by`.

Take `⟨γ, hγ, k, hk, e⟩` from `hcov x`. Conclude with `⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩`. Establish `hr : ∀ a : NFlag B e, ν.map (· * a) = ν` using `fun a => Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice ν (NFlagQ B e) hK hcov' a`. Establish `hmp : MeasurePreserving (· * y) ν ν` using `⟨measurable_mul_const y, hr y⟩`. Establish `hmp' : MeasurePreserving (· * y⁻¹) ν ν` using `⟨measurable_mul_const y⁻¹, hr y⁻¹⟩`.

Rewrite using `[← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) f 𝓝, Set.image_mul_right]`. Establish `hF : IsFundamentalDomain (NFlagQ B e) ((· * y⁻¹) ⁻¹' 𝓝) ν` using `u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]`. Conclude with `(u2.setIntegral_eq hF fun γ x => hf γ γ.2 x).symm`.
-/
theorem setIntegral_mul_right {B : HSp D} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e)
    {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)} (hN : GlobalTheory.Per.IsUnitN B e ν 𝓝) (f : NFlag B e → ℂ)
    (hf : ∀ γ ∈ NFlagQ B e, ∀ n, f (γ * n) = f n) (y : NFlag B e) :
    ∫ n in 𝓝, f (n * y) ∂ν = ∫ n in 𝓝, f n ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B he
  obtain ⟨u1, u2, u3⟩ := hN
  haveI : DiscreteTopology (NFlagQ B e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcov' : ∀ x : NFlag B e, ∃ s ∈ NFlagQ B e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : NFlag B e, ν.map (· * a) = ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice ν (NFlagQ B e) hK hcov' a
  have hmp : MeasurePreserving (· * y) ν ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) ν ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) f 𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B e) ((· * y⁻¹) ⁻¹' 𝓝) ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hf γ γ.2 x).symm

/- English proof (translation)
Introduce `D T L sc G W M hM φ F hF u hu`. Establish `hn : ∀ n, ‖besChar W.ψ G.besTop n‖ = 1` using `fun n => by`. Unfold `besChar`. Use `split_ifs with h`. Take `⟨a, b, -, -, e⟩` from `h.choose_spec`.

Rewrite using `[e]`. Conclude with `W.ψ_std.1.2.1 _`. Conclude with `norm_one`. Establish `hu1 : besChar W.ψ G.besTop u * star (besChar W.ψ G.besTop u) = 1`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]`.

Evaluate the numerical expressions. Establish `inner : ∀ h, ∫ n in M.fdN, besInt W φ (rTr _ u F) h n ∂M.νN = besChar W.ψ G.besTop u * ∫ n in M.fdN, besInt W φ F h n ∂M.νN` using `fun h => by`. Establish `hs : EmbRel _ _ (G.rowDec 0 (by have` using `D.R.two_le_m; omega)).ι (embTop G h) h := (embRel_iff _ h _).2 rfl`. Take `⟨hy, hyc⟩` from `GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop (embTop G h) h hs u hu`. Set `y : NFlag (G.V (.grid D.R.m 0)) G.besTop.e` to `⟨_, hy⟩`.

Establish `hinv : ∀ γ ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n, besInt W φ F h (γ * n) = besInt W φ F h n` using `fun γ hγ n => by`. Establish `hγQ : (γ : GA D (G.V (.grid D.R.m 0))) ∈ GQ (G.V (.grid D.R.m 0))` using `Subgroup.mem_subgroupOf.1 hγ`. Simplify using `only [besInt, Subgroup.coe_mul]`. Rewrite using `[GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ.2 n.2, GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ.2 hγQ, one_mul, mul_assoc (γ : GA D (G.V (.grid D.R.m 0))) (n : GA D (G.V (.grid D.R.m 0))) (embTop G h), hF.2 _ hγQ]`. Establish `hpt : ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e, besInt W φ (rTr _ u F) h n = besChar W.ψ G.besTop u * besInt W φ F h (n * y)` using `fun n => by`.

Simplify using `only [besInt, rTr, Subgroup.coe_mul, y]`. Rewrite using `[GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ n.2 hy, hyc, star_mul]`. Establish `e1 : (n : GA D (G.V (.grid D.R.m 0))) * (embTop G h * u * (embTop G h)⁻¹) * embTop G h = (n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u` using `by group`. Rewrite using `[e1]`. Take the linear combination `(-(φ h * F ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u) * star (besChar W.ψ G.besTop (n : GA D (G.V (.grid D.R.m 0)))))) * hu1`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_const_mul, setIntegral_mul_right G.besTop.e_iso hM.unip _ hinv y]`. Unfold `Bplus`. Repeatedly rewrite using `[inner]`. Conclude with `integral_const_mul _ _`.
-/
theorem bplus_rTr_unip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  intro D T L sc G W M hM φ F hF u hu
  have hn : ∀ n, ‖besChar W.ψ G.besTop n‖ = 1 := fun n => by
    unfold besChar
    split_ifs with h
    · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
      rw [e]
      exact W.ψ_std.1.2.1 _
    · exact norm_one
  have hu1 : besChar W.ψ G.besTop u * star (besChar W.ψ G.besTop u) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have inner : ∀ h, ∫ n in M.fdN, besInt W φ (rTr _ u F) h n ∂M.νN =
      besChar W.ψ G.besTop u * ∫ n in M.fdN, besInt W φ F h n ∂M.νN := fun h => by
    have hs : EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h := (embRel_iff _ h _).2 rfl
    obtain ⟨hy, hyc⟩ := GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop (embTop G h) h hs u hu
    let y : NFlag (G.V (.grid D.R.m 0)) G.besTop.e := ⟨_, hy⟩
    have hinv : ∀ γ ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n,
        besInt W φ F h (γ * n) = besInt W φ F h n := fun γ hγ n => by
      have hγQ : (γ : GA D (G.V (.grid D.R.m 0))) ∈ GQ (G.V (.grid D.R.m 0)) := Subgroup.mem_subgroupOf.1 hγ
      simp only [besInt, Subgroup.coe_mul]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ.2 n.2,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ.2 hγQ, one_mul, mul_assoc (γ : GA D (G.V (.grid D.R.m 0))) (n : GA D (G.V (.grid D.R.m 0))) (embTop G h),
        hF.2 _ hγQ]
    have hpt : ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e, besInt W φ (rTr _ u F) h n =
        besChar W.ψ G.besTop u * besInt W φ F h (n * y) := fun n => by
      simp only [besInt, rTr, Subgroup.coe_mul, y]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ n.2 hy, hyc, star_mul]
      have e1 : (n : GA D (G.V (.grid D.R.m 0))) * (embTop G h * u * (embTop G h)⁻¹) * embTop G h =
          (n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u := by group
      rw [e1]
      linear_combination (-(φ h * F ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u) *
        star (besChar W.ψ G.besTop (n : GA D (G.V (.grid D.R.m 0)))))) * hu1
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_mul_right G.besTop.e_iso hM.unip _ hinv y]
  unfold Bplus
  simp_rw [inner]
  exact integral_const_mul _ _

end GlobalTheory.BplusUnip
