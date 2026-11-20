import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInvStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatchStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SuppLevO

variable {D : D7}

/- English proof (translation)
Rewrite using `[← GlobalTheory.AdelicU.projFinLoc_projFin]`. Establish `: GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram h = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `congrArg Units.val hh`.

Rewrite using `[this, map_one]`.
-/
theorem proj_eq_one_of_finHom (V : HSp D) (h : GA D V) (hh : h ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v h = 1 := by
  rw [← GlobalTheory.AdelicU.projFinLoc_projFin]
  have : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram h = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Units.val hh
  rw [this, map_one]

/- English proof (translation)
Establish `h` using `proj_eq_one_of_finHom V _ (GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC V g) v`. Rewrite `h` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h`.
-/
theorem proj_finPartG (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (GlobalTheory.LevelNbhd.finPartG V g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
  have h := proj_eq_one_of_finHom V _ (GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC V g) v
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h

/- English proof (translation)
Use `show (Formalism.UG.bc _) (finHom V _) = (Formalism.UG.bc _) (finHom V g)`. Rewrite using `[GlobalTheory.LevelNbhd.finHom_finPartG]`.
-/
theorem finE_finPartG (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.LevelNbhd.finPartG V g) = Lev.finE V g := by
  show (Formalism.UG.bc _) (finHom V _) = (Formalism.UG.bc _) (finHom V g)
  rw [GlobalTheory.LevelNbhd.finHom_finPartG]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `i j`. Establish `hX : toEAf D e • ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)) = (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)`. Use extensionality with `a b`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul]`. Rewrite using `[h a b]`.

Establish `: toEAf D e • frMapO S T βS βT x = frMapO S T βS βT x`. Unfold `frMapO`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, hX]`. Conclude with `congrFun (congrFun this i) j`.
-/
theorem half_supp (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (x : WO S T)
    (h : IsHalf e x) : ∀ i j, toEAf D e * frMapO S T βS βT x i j = frMapO S T βS βT x i j := by
  intro i j
  have hX : toEAf D e • ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)) =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul]
    rw [h a b]
  have : toEAf D e • frMapO S T βS βT x = frMapO S T βS βT x := by
    unfold frMapO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hX]
  exact congrFun (congrFun this i) j

/- English proof (translation)
Use `split_ifs at hx with hc`. Establish `hg` using `left_ne_zero_of_mul hx`. Unfold `omegaG at hg`. Use `split_ifs at hg with hG`. Take `⟨-, a, ha1, ha2, ha3⟩` from `hG`.

Use `⟨hc.1, hc.2, fun PP hP => ?_, a, ha1, ha2, ha3⟩` and prove the remaining obligations. Rewrite using `[← ha1 ⟨PP, hP⟩]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (a ⟨PP, hP⟩).isUnit`. Conclude with `absurd rfl hg`. Conclude with `absurd rfl hx`.
-/
theorem datum_spec (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T)
    (hx : (if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) *
      omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) ≠ 0) :
    IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
    (∀ PP ∈ L.Pg, IsUnit (topL S.rank (redM PP (frMapO S T βS βT x))).det) ∧
    ∃ a : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1),
      (∀ PP : ↥L.Pg, ((a PP : GL (Fin S.rank) (kP PP.1)) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)) =
        topL S.rank (redM PP.1 (frMapO S T βS βT x))) ∧
      (∀ PP : ↥L.Pg, a PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (a PP)) ∈ L.P.H := by
  split_ifs at hx with hc
  · have hg := left_ne_zero_of_mul hx
    unfold omegaG at hg
    split_ifs at hg with hG
    · obtain ⟨-, a, ha1, ha2, ha3⟩ := hG
      refine ⟨hc.1, hc.2, fun PP hP => ?_, a, ha1, ha2, ha3⟩
      rw [← ha1 ⟨PP, hP⟩]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (a ⟨PP, hP⟩).isUnit
    · exact absurd rfl hg
  · exact absurd rfl hx

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D S T ΛS βS βT L χ ξ e hsd hfr hrk hQ hZe g hg x hx hx'`. Use `beta_reduce at hx hx'`. Rewrite `hZe` using `[Finset.union_empty]`. Take `⟨hh, hI, hU, a, ha1, ha2, ha3⟩` from `datum_spec S T βS βT L χ ξ e x hx`. Take `⟨-, hI', hU', b, hb1, hb2, hb3⟩` from `datum_spec S T βS βT L χ ξ e _ hx'`.

Establish `hu'` using `GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x`. Rewrite `hI'`, `hU'`, `hb1` using `[hu']`. Establish `hsupp` using `half_supp S T βS βT e x hh`. Take `⟨h1, h2, hred⟩` from `GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions T.rank S.rank hrk L.Pg e hZe _ (βS⁻¹ * Lev.finE S g * βS) hI hI' hsupp hU hU'`. Establish `hUA` using `GlobalTheory.LevSplit.finE_mem_UA S g`.

Take `⟨h3, h4⟩` from `GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hsd hfr _ hUA _ rfl e h1 h2`. Take `⟨hεε, hεc⟩` from `GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed L.Pg e hZe`. Take `⟨k, hk, hmt⟩` from `GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e + cA D e) (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc`. Establish `hfk` using `GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS _ k (e + cA D e) hmt`. Rewrite `hfk` using `[finE_finPartG]`.

Take `⟨hSt, hR⟩` from `GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS _ _ L.Pg e hZe h1 h2 h3 h4 hfk`. Establish `hcomp : ∀ PP ∈ L.Pg, GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) k = GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g` using `fun PP hP => by`. Rewrite using `[← proj_finPartG S g]`. Conclude with `GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e hZe PP hP) hmt`. Establish `hkloc` using `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr k).1 hSt`.

Establish `hgSt : Lev.finE S g ∈ St βS`. Use `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr g).2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : ∃ PP ∈ L.Pg, PP.under (𝓞 D.host.F) = v`. Take `⟨PP, hP, rfl⟩` from `hv`. Rewrite using `[← hcomp PP hP]`.

Conclude with `hkloc _`. Use `push_neg at hv`. Conclude with `hg v hv`. Establish `hredeq : ∀ PP ∈ L.Pg, redFn βS PP (Lev.finE S g) = redFn βS PP (Lev.finE S k)` using `fun PP hP => by`. Establish `hm : Lev.finE S (g * k⁻¹) ∈ St βS`.

Rewrite using `[map_mul, map_inv]`. Conclude with `Subgroup.mul_mem _ hgSt (Subgroup.inv_mem _ hSt)`. Establish `h1' : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) (g * k⁻¹) = 1`. Rewrite using `[map_mul, map_inv, hcomp PP hP, mul_inv_cancel]`. Establish `hr` using `GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS (g * k⁻¹) PP hm h1'`.

Establish `hgk : Lev.finE S g = Lev.finE S (g * k⁻¹) * Lev.finE S k`. Rewrite using `[map_mul, map_inv, inv_mul_cancel_right]`. Rewrite using `[hgk, redFn_mul hm hSt, hr, one_mul]`. Use `GlobalTheory.T.mem_level_of_type_place_reductions S βS L _ hQ hUA hgSt a b ha2 hb2 ha3 hb3 fun PP => ?_` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, hredeq PP.1 PP.2, hR PP.1 PP.2, ha1, hb1]`. Conclude with `hred PP.1 PP.2`.
-/
theorem finE_mem_lev : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → L.Q = ∅ → IsIdemSum e (L.Pg ∪ ∅) → ∀ g : GA D S, (∀ v, (∀ PP ∈ L.Pg, PP.under (𝓞 D.host.F) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) → ∀ x, (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → Lev.finE S g ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L := by
  intro D S T ΛS βS βT L χ ξ e hsd hfr hrk hQ hZe g hg x hx hx'
  beta_reduce at hx hx'
  rw [Finset.union_empty] at hZe
  obtain ⟨hh, hI, hU, a, ha1, ha2, ha3⟩ := datum_spec S T βS βT L χ ξ e x hx
  obtain ⟨-, hI', hU', b, hb1, hb2, hb3⟩ := datum_spec S T βS βT L χ ξ e _ hx'
  have hu' := GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x
  rw [hu'] at hI' hU' hb1
  have hsupp := half_supp S T βS βT e x hh
  obtain ⟨h1, h2, hred⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions T.rank S.rank hrk L.Pg e hZe _ (βS⁻¹ * Lev.finE S g * βS) hI hI' hsupp hU hU'
  have hUA := GlobalTheory.LevSplit.finE_mem_UA S g
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed L.Pg e hZe
  obtain ⟨k, hk, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS _ k (e + cA D e) hmt
  rw [finE_finPartG] at hfk
  obtain ⟨hSt, hR⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS _ _ L.Pg e hZe h1 h2 h3 h4 hfk

  have hcomp : ∀ PP ∈ L.Pg, GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g := fun PP hP => by
    rw [← proj_finPartG S g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e hZe PP hP) hmt

  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr k).1 hSt
  have hgSt : Lev.finE S g ∈ St βS := by
    refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ L.Pg, PP.under (𝓞 D.host.F) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv

  have hredeq : ∀ PP ∈ L.Pg, redFn βS PP (Lev.finE S g) = redFn βS PP (Lev.finE S k) := fun PP hP => by
    have hm : Lev.finE S (g * k⁻¹) ∈ St βS := by
      rw [map_mul, map_inv]; exact Subgroup.mul_mem _ hgSt (Subgroup.inv_mem _ hSt)
    have h1' : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) (g * k⁻¹) = 1 := by
      rw [map_mul, map_inv, hcomp PP hP, mul_inv_cancel]
    have hr := GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS (g * k⁻¹) PP hm h1'
    have hgk : Lev.finE S g = Lev.finE S (g * k⁻¹) * Lev.finE S k := by
      rw [map_mul, map_inv, inv_mul_cancel_right]
    rw [hgk, redFn_mul hm hSt, hr, one_mul]
  refine GlobalTheory.T.mem_level_of_type_place_reductions S βS L _ hQ hUA hgSt a b ha2 hb2 ha3 hb3 fun PP => ?_
  apply Units.ext
  rw [Units.val_mul, hredeq PP.1 PP.2, hR PP.1 PP.2, ha1, hb1]
  exact hred PP.1 PP.2

end GlobalTheory.SuppLevO
