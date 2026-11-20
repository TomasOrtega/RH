import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `i j`. Set `A' : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨A i j, hA i j⟩`. Establish `eA : A.adjugate = O.subtype.mapMatrix A'.adjugate`. Rewrite using `[show A = O.subtype.mapMatrix A' from rfl]`. Conclude with `(RingHom.map_adjugate O.subtype A').symm`.

Rewrite using `[eA]`. Conclude with `(A'.adjugate i j).2`.
-/
private theorem UpperTheory.adjugate_mem_subring_of_mem {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, A i j ∈ O) : ∀ i j, A.adjugate i j ∈ O := by
  intro i j
  let A' : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hA i j⟩
  have eA : A.adjugate = O.subtype.mapMatrix A'.adjugate := by
    rw [show A = O.subtype.mapMatrix A' from rfl]
    exact (RingHom.map_adjugate O.subtype A').symm
  rw [eA]
  exact (A'.adjugate i j).2

/- English proof (translation)
Introduce `i j`. Establish `h0 : yi * ε * A.det = ε`. Substitute `hy` using the available equality. Take the linear combination `ε * hyy + (yi - yi * A.det) * hε`. Establish `h1 : ε • M = (yi * ε) • (A.adjugate * (A * M))`.

Rewrite using `[← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, h0]`. Rewrite using `[h1, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]`. Conclude with `mul_mem (mul_mem hyi hεO) (Subring.sum_mem _ fun l _ => mul_mem (UpperTheory.adjugate_mem_subring_of_mem O A hA i l) (hB l j))`.
-/
private theorem UpperTheory.idempotent_smul_integral {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (A M : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, (A * M) i j ∈ O) (ε y yi : R) (hε : ε * ε = ε) (hεO : ε ∈ O) (hyi : yi ∈ O)
    (hy : y = 1 - ε + ε * A.det) (hyy : y * yi = 1) : ∀ i j, (ε • M) i j ∈ O := by
  intro i j
  have h0 : yi * ε * A.det = ε := by
    subst hy
    linear_combination ε * hyy + (yi - yi * A.det) * hε
  have h1 : ε • M = (yi * ε) • (A.adjugate * (A * M)) := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, h0]
  rw [h1, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  exact mul_mem (mul_mem hyi hεO)
    (Subring.sum_mem _ fun l _ => mul_mem (UpperTheory.adjugate_mem_subring_of_mem O A hA i l) (hB l j))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [topL, Matrix.mul_apply]`. Distinguish the cases in `hi : i.1 < b`. Simplify using `[hi]`. Simplify using `[hi]`.
-/
private theorem UpperTheory.upperRows_mul_right {D : D7} {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Lev.EAf D))
    (κ : Matrix (Fin a) (Fin a) (Lev.EAf D)) : topL a (N * κ) = topL a N * κ := by
  ext i j
  simp only [topL, Matrix.mul_apply]
  by_cases hi : i.1 < b
  · simp [hi]
  · simp [hi]

/- English proof (translation)
Introduce `i j`. Simplify using `only [topL]`. Use `split_ifs`. Conclude with `hN _ _`. Conclude with `zero_mem _`.
-/
private theorem UpperTheory.topL_integral {D : D7} {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Lev.EAf D))
    (hN : IsIntM N) : IsIntM (topL a N) := by
  intro i j
  simp only [topL]
  split_ifs
  · exact hN _ _
  · exact zero_mem _

/- English proof (translation)
Establish `hε : toEAf D e * toEAf D e = toEAf D e` using `by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]`. Establish `hE` using `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he`. Establish `hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Conclude with `UpperTheory.idempotent_smul_integral _ A M hA hB _ _ _ hε hE hy.2.2 hy.2.1 hyy`.
-/
private theorem UpperTheory.idempotent_unit_det_integral {D : D7} {e : AE D} {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Z) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) (Lev.EAf D)) (hA : IsIntM A) (hB : IsIntM (A * M)) (y : (AE D)ˣ)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e A y) : IsIntM (toEAf D e • M) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact UpperTheory.idempotent_smul_integral _ A M hA hB _ _ _ hε hE hy.2.2 hy.2.1 hyy

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst at hx`. Use `split_ifs at hx with hc`. Use `⟨hc.2.1, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar at hx`. Use `split_ifs at hx with hG`.

Conclude with `hG`. Conclude with `absurd rfl hx`. Conclude with `absurd rfl hx`.
-/
private theorem UpperTheory.standard_section_integral_unit {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (x : WO S T)
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0) :
    IsIntM (frMapO S T βS βT x) ∧ ∃ y, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL S.rank (frMapO S T βS βT x)) y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst at hx
  split_ifs at hx with hc
  · refine ⟨hc.2.1, ?_⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar at hx
    split_ifs at hx with hG
    · exact hG
    · exact absurd rfl hx
  · exact absurd rfl hx

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hA` using `UpperTheory.topL_integral N hI`. Establish `hB` using `UpperTheory.topL_integral _ hI'`. Prove the components needed by the constructor for the conclusion. Use `UpperTheory.idempotent_unit_det_integral he _ _ hB ?_ y' hy'` and prove the remaining obligations. Rewrite using `[UpperTheory.upperRows_mul_right, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Conclude with `hA`. Use `UpperTheory.idempotent_unit_det_integral he _ _ hA ?_ y hy` and prove the remaining obligations. Rewrite using `[← UpperTheory.upperRows_mul_right]`. Conclude with `hB`.
-/
private theorem UpperTheory.integral_unit_det_both {D : D7} {e : AE D} {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Z) {m n : ℕ}
    (N : Matrix (Fin m) (Fin n) (Lev.EAf D)) (γ : GL (Fin n) (Lev.EAf D)) (hI : IsIntM N)
    (hI' : IsIntM (HMul.hMul N (γ⁻¹ : GL (Fin n) (Lev.EAf D)).val)) (y y' : (AE D)ˣ)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL n N) y)
    (hy' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL n (HMul.hMul N (γ⁻¹ : GL (Fin n) (Lev.EAf D)).val)) y') :
    IsIntM (toEAf D e • γ.val) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (Lev.EAf D)).val) := by
  have hA := UpperTheory.topL_integral N hI
  have hB := UpperTheory.topL_integral _ hI'
  constructor
  · refine UpperTheory.idempotent_unit_det_integral he _ _ hB ?_ y' hy'
    rw [UpperTheory.upperRows_mul_right, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact hA
  · refine UpperTheory.idempotent_unit_det_integral he _ _ hA ?_ y hy
    rw [← UpperTheory.upperRows_mul_right]
    exact hB

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D S T ΛS βS βT ν e Z I hsd hfr hrk hZe g hg x hx hx'`. Take `⟨hI, y, hy⟩` from `UpperTheory.standard_section_integral_unit S T βS βT ν e I x hx`. Take `⟨hI', y', hy'⟩` from `UpperTheory.standard_section_integral_unit S T βS βT ν e I _ hx'`. Establish `hu'` using `GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x`. Rewrite `hI'`, `hy'` using `[hu']`.

Take `⟨h1, h2⟩` from `UpperTheory.integral_unit_det_both hZe _ (βS⁻¹ * Lev.finE S g * βS) hI hI' y y' hy hy'`. Establish `hUA` using `GlobalTheory.LevSplit.finE_mem_UA S g`. Take `⟨h3, h4⟩` from `GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hsd hfr _ hUA _ rfl e h1 h2`. Take `⟨hεε, hεc⟩` from `GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe`. Take `⟨k, hk, hmt⟩` from `GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e + cA D e) (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc`.

Establish `hfk` using `GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS _ k (e + cA D e) hmt`. Rewrite `hfk` using `[GlobalTheory.SuppLevO.finE_finPartG]`. Take `⟨hSt, -⟩` from `GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS _ _ Z e hZe h1 h2 h3 h4 hfk`. Establish `hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) k = GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g` using `fun PP hP => by`. Rewrite using `[← GlobalTheory.SuppLevO.proj_finPartG S g]`.

Conclude with `GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt`. Establish `hkloc` using `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr k).1 hSt`. Use `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr g).2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : ∃ PP ∈ Z, PP.under (𝓞 D.host.F) = v`. Take `⟨PP, hP, rfl⟩` from `hv`.

Rewrite using `[← hcomp PP hP]`. Conclude with `hkloc _`. Use `push_neg at hv`. Conclude with `hg v hv`.
-/
theorem UpperTheory.finiteComponent_mem_stabilizer_of_standardSection_ne_zero :
    ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e Z → ∀ g : GA D S,
      (∀ v, (∀ PP ∈ Z, PP.under (𝓞 D.host.F) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) →
      ∀ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT (actO S T g 1 x) ≠ 0 →
        Lev.finE S g ∈ Formalism.L2.DIV.St βS := by
  intro D S T ΛS βS βT ν e Z I hsd hfr hrk hZe g hg x hx hx'
  obtain ⟨hI, y, hy⟩ := UpperTheory.standard_section_integral_unit S T βS βT ν e I x hx
  obtain ⟨hI', y', hy'⟩ := UpperTheory.standard_section_integral_unit S T βS βT ν e I _ hx'
  have hu' := GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x
  rw [hu'] at hI' hy'
  obtain ⟨h1, h2⟩ := UpperTheory.integral_unit_det_both hZe _ (βS⁻¹ * Lev.finE S g * βS) hI hI' y y' hy hy'
  have hUA := GlobalTheory.LevSplit.finE_mem_UA S g
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, hk, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG S g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr k).1 hSt
  refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hfr g).2 fun v => ?_
  by_cases hv : ∃ PP ∈ Z, PP.under (𝓞 D.host.F) = v
  · obtain ⟨PP, hP, rfl⟩ := hv
    rw [← hcomp PP hP]
    exact hkloc _
  · push_neg at hv
    exact hg v hv
