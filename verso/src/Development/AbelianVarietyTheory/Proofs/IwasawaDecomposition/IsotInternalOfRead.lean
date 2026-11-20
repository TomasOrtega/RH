import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypeParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystems
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuples
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLiftLabelEqFinrankFace3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaRatEqLam

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric.L0

/- English proof (translation)
Introduce `_ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'`. Use `set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ`. Establish `hK` using `GlobalTheory.Mem.KerSpan.L0.orth_ker_thetaP D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t`. Use `set K := (LinearMap.ker θ)ᗮ with hKdef`. Establish `hS` using `GlobalTheory.Mem.R3.PartSpan.L0.mem_span_part D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW`.

Establish `hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ`. Introduce `z`. Use `K.sub_starProjection_mem_orthogonal z` as an intermediate fact. Rewrite `this` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ` using `fun z => K.sub_starProjection_mem_orthogonal z`.

Establish `hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K, ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ …`. Introduce `a ha q hq`. Rewrite `hq` using `[hK]`. Proceed by induction on `hq using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `GlobalTheory.Mem.R3.LamMetric.L0.inner_theta_rat_eq_lam D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha`. Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => rw [map_add, inner_add_right, inner_add_right, h1, h2, mul_add]`. Consider the case `smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x', ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = …`. Introduce `a ha x'`. Establish `huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K` using `by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩`. Establish `e1 : θ x' = θ (K.starProjection x')`.

Use `hkerK x'` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this`. Establish `e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ`. Establish `h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0` using `Submodule.inner_right_of_mem_orthogonal huK (hKperp x')`.

Rewrite `h0` using `[inner_sub_right, sub_eq_zero]`. Conclude with `h0`. Rewrite using `[e1, e2]`. Conclude with `hgoodK a ha _ (K.starProjection_apply_mem x')`. Use `clear hx hW`.

Proceed by induction on `hS using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Conclude with `hgood a ha x'`. Consider the case `zero => simp`.

Consider the case `add y z _ _ h1 h2 => rw [map_add, inner_add_left, inner_add_left, h1, h2, mul_add]`. Consider the case `smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_theta_eq_lam : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  have hK := GlobalTheory.Mem.KerSpan.L0.orth_ker_thetaP D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  set K := (LinearMap.ker θ)ᗮ with hKdef
  have hS := GlobalTheory.Mem.R3.PartSpan.L0.mem_span_part D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW

  have hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ := by
    intro z
    have := K.sub_starProjection_mem_orthogonal z
    rwa [Submodule.orthogonal_orthogonal] at this
  have hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ := fun z => K.sub_starProjection_mem_orthogonal z

  have hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K,
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), q⟫_ℂ := by
    intro a ha q hq
    rw [hK] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact GlobalTheory.Mem.R3.LamMetric.L0.inner_theta_rat_eq_lam D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add, inner_add_right, inner_add_right, h1, h2, mul_add]
    | smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]; ring
  have hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x',
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ := by
    intro a ha x'
    have huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K := by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩
    have e1 : θ x' = θ (K.starProjection x') := by
      have := hkerK x'
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ := by
      have h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal huK (hKperp x')
      rw [inner_sub_right, sub_eq_zero] at h0; exact h0
    rw [e1, e2]
    exact hgoodK a ha _ (K.starProjection_apply_mem x')
  clear hx hW
  induction hS using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hgood a ha x'
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add, inner_add_left, inner_add_left, h1, h2, mul_add]
  | smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]; ring

end GlobalTheory.Mem.R3.LamMetric.L0

namespace GlobalTheory.Mem.R3.LabProof.L0

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `hW hDS hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ`. Take `⟨c, hE, hWp⟩` from `GlobalTheory.Mem.R3.LabEig.L0.eig_parts hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost σ`. Establish `hcar` using `GlobalTheory.Mem.R3.LabCarry.L0.carried hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost`. Take `⟨b, hb⟩` from `principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)`. Take `⟨U, hU, hU0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`.

Take `⟨x, hx, hxU⟩` from `hE b U hU`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hxU` using `[map_zero]`. Conclude with `hU0 hxU.symm`.

Take `⟨p, hp⟩` from `hcar c b x hx0 hx (by rw [hxU]; exact hU.1)`. Establish `hinjW : ∀ i, Function.Injective (R.HW i (sg0 D A3.A)).e` using `fun i => (hPins.char.base.models.HW i _).1`. Use `⟨p, fun i => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `h1` using `(Y.tied.lift.isot i σ y).1 hy`.

Rewrite `h1` using `[Y.prtWE]`. Take `⟨U', hU', hU'e⟩` from `h1`. Take `⟨w, hw, hwU⟩` from `hWp i U' hU'`. Rewrite `hU'e` using `[Y.mjRead]`. Establish `h2 : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) = (R.HW i (sg0 D A3.A)).e w`.

Rewrite using `[hwU]`. Conclude with `(PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hU'e.symm`. Establish `h3 : Y.mj.eW i y ∈ R.Wc' i c` using `(hinjW i h2) ▸ hw`. Conclude with `le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp le_rfl h3`. Establish `h1` using `Y.tied.base.ft k`.

Rewrite `h1` using `[hk, Y.prtE0]`. Take `⟨U', hU', hU'e⟩` from `h1`. Take `⟨w, hw, hwU⟩` from `hE false U' hU'`. Use `⟨w, le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← hU'e, hwU]`.

Both sides reduce to the same expression.
-/
theorem hasLab_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  intro hW hDS hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨c, hE, hWp⟩ := GlobalTheory.Mem.R3.LabEig.L0.eig_parts hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost σ
  have hcar := GlobalTheory.Mem.R3.LabCarry.L0.carried hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := hE b U hU
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxU
    exact hU0 hxU.symm
  obtain ⟨p, hp⟩ := hcar c b x hx0 hx (by rw [hxU]; exact hU.1)
  have hinjW : ∀ i, Function.Injective (R.HW i (sg0 D A3.A)).e := fun i => (hPins.char.base.models.HW i _).1
  refine ⟨p, fun i => ?_, fun k hk => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := (Y.tied.lift.isot i σ y).1 hy
    rw [Y.prtWE] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hWp i U' hU'
    rw [Y.mjRead] at hU'e
    have h2 : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) = (R.HW i (sg0 D A3.A)).e w := by
      rw [hwU]
      exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hU'e.symm
    have h3 : Y.mj.eW i y ∈ R.Wc' i c := (hinjW i h2) ▸ hw
    exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp le_rfl h3
  · have h1 := Y.tied.base.ft k
    rw [hk, Y.prtE0] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hE false U' hU'
    refine ⟨w, le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl hw, ?_⟩
    rw [← hU'e, hwU]
    rfl

end GlobalTheory.Mem.R3.LabProof.L0

namespace GlobalTheory.Mem.R3.LamLab.L0

/- English proof (translation)
Introduce `h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne`. Use `Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_` and prove the remaining obligations. Use `set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ`. Take `⟨x, rfl⟩` from `GlobalTheory.Mem.LiftOnto.L0.thetaMap_surjective h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y`. Use `set K := (LinearMap.ker θ)ᗮ`.

Establish `hx0 : x - K.starProjection x ∈ LinearMap.ker θ`. Use `K.sub_starProjection_mem_orthogonal x` as an intermediate fact. Rewrite `this` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `he : θ (K.starProjection x) = θ x`. Rewrite `hx0` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`.

Conclude with `hx0.symm`. Establish `hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p`. Rewrite using `[he]`. Conclude with `hL.1 i ⟨θ x, hy, rfl⟩`. Establish `key` using `GlobalTheory.Mem.R3.LamMetric.L0.inner_theta_eq_lam h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x) (K.starProjection_apply_mem x) hW`.

Use `adj_eig θ (R.lam3 i t p A3.A.v0) _ key` as an intermediate fact. Rewrite `this` using `[he]`. Conclude with `this`.
-/
theorem eigenvalue_eq_of_label : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne
  refine Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  obtain ⟨x, rfl⟩ := GlobalTheory.Mem.LiftOnto.L0.thetaMap_surjective h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
  set K := (LinearMap.ker θ)ᗮ
  have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
    have := K.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at this
  have he : θ (K.starProjection x) = θ x := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
  have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
    rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
  have key := GlobalTheory.Mem.R3.LamMetric.L0.inner_theta_eq_lam h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
    (K.starProjection_apply_mem x) hW
  have := adj_eig θ (R.lam3 i t p A3.A.v0) _ key
  rw [he] at this
  exact this

end GlobalTheory.Mem.R3.LamLab.L0

namespace GlobalTheory.Mem.R3.L0

open Classical in

def Lam3 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y) : Prop :=
  ∃ cOf : D.what₂.FT → A3.fam3.base3.Ix,
    (∀ (i : Fin D.R.m) (c : A3.fam3.base3.Ix),
      iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) ∧
      (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
        Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i c : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) ∧
    (∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.FT),
      (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
      D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t (cOf σ) A3.fam3.base3.v0) ∧
    (∀ c : A3.fam3.base3.Ix,
      ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep c))

end GlobalTheory.Mem.R3.L0

namespace GlobalTheory.Mem.R3.L0

/- English proof (translation)
Introduce `h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hIR`. Establish `lab` using `GlobalTheory.Mem.R3.LabProof.L0.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost`. Set `cOf : D.what₂.FT → A3.fam3.base3.Ix` to `fun σ => (lab σ).choose`. Establish `hc : ∀ σ, HasLab Y σ (cOf σ)` using `fun σ => (lab σ).choose_spec`. Establish `rat` using `GlobalTheory.Mem.R3.RatSpan.L0.span_jW_wp h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost`.

Establish `ind` using `GlobalTheory.Mem.R3.IsotIndep.L0.isot_iSupIndep h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost`. Establish `dim` using `GlobalTheory.Mem.R3.L0.finrank_liftLabel_eq_finrank_face3 h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost`. Establish `cnt` using `GlobalTheory.Mem.R3.LabCount.L0.cnt h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost cOf hc`. Establish `lam` using `GlobalTheory.Mem.R3.LamLab.L0.eigenvalue_eq_of_label h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost`. Use `⟨cOf, fun i c => ?_, fun i t σ ht hne => lam σ (cOf σ) i t (hc σ) ht hne, fun c => cnt c⟩` and prove the remaining obligations.

Establish `hind : iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1)` using `(ind i).comp Subtype.val_injective`. Use `⟨hind, ?_⟩` and prove the remaining obligations. Rewrite using `[rat i c]`. Establish `hle : (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) ≤ (R.Wp3 i c).comap (Y.mj.eW i)`. Use `iSup_le fun σ => ?_` and prove the remaining obligations.

Use `(hc σ.1).1 i` as an intermediate fact. Rewrite `this` using `[σ.2]`. Conclude with `Submodule.map_le_iff_le_comap.1 this`. Use `Submodule.eq_of_le_of_finrank_eq hle ?_` and prove the remaining obligations. Rewrite using `[dim i c, ← cnt c, Formalism.IndefR.Cx.finrank_iSup_eq_sum _ hind]`.

Rewrite using `[Finset.sum_subtype (Finset.univ.filter (fun σ => cOf σ = c)) (p := fun σ => cOf σ = c) (by simp)]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Conclude with `hIR ((i : ℕ) + 1) (by omega) (by omega) σ.1`.
-/
theorem finiteTypes_of_full_heckeAlgebra_eigensystems : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Lam3 Z := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hIR
  have lab := GlobalTheory.Mem.R3.LabProof.L0.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  let cOf : D.what₂.FT → A3.fam3.base3.Ix := fun σ => (lab σ).choose
  have hc : ∀ σ, HasLab Y σ (cOf σ) := fun σ => (lab σ).choose_spec
  have rat := GlobalTheory.Mem.R3.RatSpan.L0.span_jW_wp h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have ind := GlobalTheory.Mem.R3.IsotIndep.L0.isot_iSupIndep h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have dim := GlobalTheory.Mem.R3.L0.finrank_liftLabel_eq_finrank_face3 h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have cnt := GlobalTheory.Mem.R3.LabCount.L0.cnt h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost cOf hc
  have lam := GlobalTheory.Mem.R3.LamLab.L0.eigenvalue_eq_of_label h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  refine ⟨cOf, fun i c => ?_, fun i t σ ht hne => lam σ (cOf σ) i t (hc σ) ht hne, fun c => cnt c⟩
  have hind : iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) :=
    (ind i).comp Subtype.val_injective
  refine ⟨hind, ?_⟩
  rw [rat i c]
  have hle : (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) ≤ (R.Wp3 i c).comap (Y.mj.eW i) := by
    refine iSup_le fun σ => ?_
    have := (hc σ.1).1 i
    rw [σ.2] at this
    exact Submodule.map_le_iff_le_comap.1 this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [dim i c, ← cnt c, Formalism.IndefR.Cx.finrank_iSup_eq_sum _ hind]
  rw [Finset.sum_subtype (Finset.univ.filter (fun σ => cOf σ = c)) (p := fun σ => cOf σ = c) (by simp)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact hIR ((i : ℕ) + 1) (by omega) (by omega) σ.1

end GlobalTheory.Mem.R3.L0

namespace GlobalTheory.IsotSum.L0

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `_ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i`. Establish `hR` using `complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim`. Establish `hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL, (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y))`. Introduce `y`. Rewrite using `[Z.jW_read]`.

Use `(GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i y).trans ?_` and prove the remaining obligations. Use `congr 1`. Establish `hnP : 0 < RealDat.nP F.lv2 false` using `RealDat.nP_pos (F := F.lv2) false`. Establish `hinj : Function.Injective (Y.mj.eW i)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `d hd`. Establish `h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0` using `by rw [← Y.mj.eW_norm i d, hd]; simp`. Establish `h2 : ‖d‖ ^ 2 = 0`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd h hnP.ne'`.

Conclude with `h`. Conclude with `norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)`. Establish `hw` using `(R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i`. Establish `hUT : ∀ p, Submodule.span ℂ ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) = (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)`. Introduce `p`.

Apply `Submodule.eq_of_le_of_finrank_le` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨hy, LinearMap.mem_range_self _ _⟩`. Rewrite using `[← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W hR.partsW i p]`.

Conclude with `(finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw (Submodule.span ℂ ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))) ((R.toCx3 F).WpK false i p) (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.f …`. Set `outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H` to `{ toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i …`. Use `set S : Submodule ℂ (D.what₂.Mj ((i : ℕ) + 1)) := ⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) with hS`. Establish `h5 : ∀ p, (Submodule.span ℂ ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))).map outL ≤ S.map (Y.mj.eW i)`. Introduce `p`.

Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Use `Submodule.mem_map.2 ⟨Z.jW i y, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(le_iSup (fun p => Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) p) (Submodule.subset_span ⟨y, hy, rfl⟩)`. Use `show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))`.

Conclude with `(congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A)`. Rewrite using `[hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]`.

Conclude with `LinearMap.mem_range_self _ _`. Establish `hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤ Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) (LinearMap.range ((R.toCx3 F).w0C false i))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `GlobalTheory.TwParts.mk_bC_mem_range R F i k`.

Establish `h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ LinearMap.range ((R.toCx3 F).w0C false i)` using `hle hWS`. Rewrite `h1` using `[← (hR.partsW i).2]`. Establish `h4 : Y.mj.eW i x ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL` using `Submodule.mem_map_of_mem (f := outL) h1`. Rewrite `h4` using `[Submodule.map_iSup]`. Establish `h6 : (⨆ p, ((R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL) ≤ S.map (Y.mj.eW i)` using `iSup_le fun p => (hUT p) ▸ h5 p`.

Take `⟨x', hx', hxx⟩` from `h6 h4`. Rewrite using `[← hinj hxx]`. Conclude with `hx'`.
-/
theorem span_all : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m), (⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) = ⊤ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    refine (GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i y).trans ?_
    congr 1
  have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
    have h2 : ‖d‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnP.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i

  have hUT : ∀ p, Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) =
      (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
    intro p
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨hy, LinearMap.mem_range_self _ _⟩
    · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
        hR.liftHyp0.h3W hR.partsW i p]
      exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw (Submodule.span ℂ
        ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))) ((R.toCx3 F).WpK false i p)
        (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
  let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
    { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
      map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
      map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
  set S : Submodule ℂ (D.what₂.Mj ((i : ℕ) + 1)) :=
    ⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) with hS

  have h5 : ∀ p, (Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))).map outL ≤
      S.map (Y.mj.eW i) := by
    intro p
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine Submodule.mem_map.2 ⟨Z.jW i y, ?_, ?_⟩
    · exact (le_iSup (fun p => Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) p)
        (Submodule.subset_span ⟨y, hy, rfl⟩)
    · show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
  rw [eq_top_iff]
  intro x _
  have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
    exact LinearMap.mem_range_self _ _
  have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
      Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H)
        (LinearMap.range ((R.toCx3 F).w0C false i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ LinearMap.range ((R.toCx3 F).w0C false i) := hle hWS
  rw [← (hR.partsW i).2] at h1
  have h4 : Y.mj.eW i x ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL :=
    Submodule.mem_map_of_mem (f := outL) h1
  rw [Submodule.map_iSup] at h4
  have h6 : (⨆ p, ((R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL) ≤ S.map (Y.mj.eW i) :=
    iSup_le fun p => (hUT p) ▸ h5 p
  obtain ⟨x', hx', hxx⟩ := h6 h4
  rw [← hinj hxx]
  exact hx'

end GlobalTheory.IsotSum.L0

namespace GlobalTheory.IsotSum.L0

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hRk`. Take `⟨cOf, h1, -, -⟩` from `GlobalTheory.Mem.R3.L0.finiteTypes_of_full_heckeAlgebra_eigensystems hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost hRk`. Use `show Rows.IsotInternal D.what₂`. Introduce `j hj1 hjm`. Take `⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1` from `⟨⟨j - 1, by omega⟩, by simp; omega⟩`.

Apply `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` to reduce the goal to its premises. Conclude with `GlobalTheory.Mem.R3.IsotIndep.L0.isot_iSupIndep hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i`. Rewrite using `[eq_top_iff, ← span_all hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i]`. Use `iSup_le fun c => ?_` and prove the remaining obligations. Rewrite using `[← (h1 i c).2]`.

Conclude with `iSup_le fun σ => le_iSup (fun σ => D.what₂.isot ((i : ℕ) + 1) σ) σ.1`.
-/
theorem isotInternal_of_read : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hRk
  obtain ⟨cOf, h1, -, -⟩ := GlobalTheory.Mem.R3.L0.finiteTypes_of_full_heckeAlgebra_eigensystems hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost hRk
  show Rows.IsotInternal D.what₂
  intro j hj1 hjm
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact GlobalTheory.Mem.R3.IsotIndep.L0.isot_iSupIndep hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i
  · rw [eq_top_iff, ← span_all hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i]
    refine iSup_le fun c => ?_
    rw [← (h1 i c).2]
    exact iSup_le fun σ => le_iSup (fun σ => D.what₂.isot ((i : ℕ) + 1) σ) σ.1

end GlobalTheory.IsotSum.L0

namespace GlobalTheory.NRows.LamUsedProof.L0

/- English proof (translation)
Introduce `h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD μ hU0 i σ`. Establish `hU : Used0 D μ` using `hU0`. Take `⟨t, rfl⟩ : ∃ t, Y.tup t = μ` from `⟨_, Y.tupTie μ hU⟩`. Use `set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ`. Distinguish the cases in `hne : D.what₂.isot ((i : ℕ) + 1) σ = ⊥`.

Use `⟨fun f hf => ?_, fun h => absurd hne h⟩` and prove the remaining obligations. Rewrite `hf` using `[hne, Submodule.mem_bot]`. Substitute `hf` using the available equality. Simplify using the standard rewrite rules. Take `⟨p, hL⟩` from `GlobalTheory.Mem.R3.LabProof.L0.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD σ`.

Use `set c : ℝ := R.lam3 i t p A3.A.v0 with hc`. Establish `hpre : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, ∃ x ∈ (LinearMap.ker θ)ᗮ, θ x = y ∧ ∀ x', ⟪θ x, θ x'⟫_ℂ = (c : ℂ) * ⟪x, x'⟫_ℂ`. Introduce `y hy`. Take `⟨x, rfl⟩` from `GlobalTheory.Mem.LiftOnto.L0.thetaMap_surjective h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y`. Use `set K := (LinearMap.ker θ)ᗮ`.

Establish `hx0 : x - K.starProjection x ∈ LinearMap.ker θ`. Use `K.sub_starProjection_mem_orthogonal x` as an intermediate fact. Rewrite `this` using `[Submodule.orthogonal_orthogonal]`. Then use the resulting hypothesis. Establish `he : θ (K.starProjection x) = θ x`. Rewrite `hx0` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`.

Conclude with `hx0.symm`. Establish `hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p`. Rewrite using `[he]`. Conclude with `hL.1 i ⟨θ x, hy, rfl⟩`. Conclude with `⟨K.starProjection x, K.starProjection_apply_mem x, he, GlobalTheory.Mem.R3.LamMetric.L0.inner_theta_eq_lam h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x) (K.starProjection_apply_mem x) hW⟩`.

Establish `heig : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.thetaT (Y.tup t) ((i : ℕ) + 1) y) = ((c : ℝ) : ℂ) • y`. Introduce `y hy`. Take `⟨x, -, rfl, hx⟩` from `hpre y hy`. Establish `ha : LinearMap.adjoint θ (θ x) = (c : ℂ) • x`. Use `ext_inner_right ℂ fun x' => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.adjoint_inner_left, hx, inner_smul_left, Complex.conj_ofReal]`. Use `show θ (LinearMap.adjoint θ (θ x)) = (c : ℂ) • θ x`. Rewrite using `[ha, map_smul]`. Establish `hlam : D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = c` using `Y.tied.lift.lamP (Y.tup t) hU i σ c hne heig`. Use `⟨fun f hf => by rw [hlam]; exact heig f hf, fun _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hlam]`. Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Take `⟨x, -, rfl, hx⟩` from `hpre y hy`. Establish `h` using `hx x`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`.

Establish `hyn : 0 < ‖θ x‖` using `norm_pos_iff.2 hy0`. Establish `h' : ‖θ x‖ ^ 2 = c * ‖x‖ ^ 2`. Apply the tactic sequence `have h2 : ((‖θ x‖ ^ 2 : ℝ) : ℂ) = ((c * ‖x‖ ^ 2 : ℝ) : ℂ) := by first | (push_cast; exact h) | (push_cast; simpa using h) | (simp only [RCLike.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_mul] at h ⊢; exact h) | (rw [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_pow]; …`. Conclude with `Complex.ofReal_injective h2`. Assume the negation of the conclusion as `hcn`.

Use `push_neg at hcn`. Use polynomial arithmetic with `[sq_nonneg ‖x‖, sq_pos_of_pos hyn]`.
-/
theorem main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD μ hU0 i σ
  have hU : Used0 D μ := hU0
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hU⟩
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  by_cases hne : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
  · refine ⟨fun f hf => ?_, fun h => absurd hne h⟩
    rw [hne, Submodule.mem_bot] at hf
    subst hf
    simp
  obtain ⟨p, hL⟩ := GlobalTheory.Mem.R3.LabProof.L0.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD σ
  set c : ℝ := R.lam3 i t p A3.A.v0 with hc

  have hpre : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, ∃ x ∈ (LinearMap.ker θ)ᗮ, θ x = y ∧
      ∀ x', ⟪θ x, θ x'⟫_ℂ = (c : ℂ) * ⟪x, x'⟫_ℂ := by
    intro y hy
    obtain ⟨x, rfl⟩ := GlobalTheory.Mem.LiftOnto.L0.thetaMap_surjective h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
    set K := (LinearMap.ker θ)ᗮ
    have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
      have := K.sub_starProjection_mem_orthogonal x
      rwa [Submodule.orthogonal_orthogonal] at this
    have he : θ (K.starProjection x) = θ x := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
    have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
      rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
    exact ⟨K.starProjection x, K.starProjection_apply_mem x, he,
      GlobalTheory.Mem.R3.LamMetric.L0.inner_theta_eq_lam h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
        (K.starProjection_apply_mem x) hW⟩

  have heig : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ,
      D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.thetaT (Y.tup t) ((i : ℕ) + 1) y) = ((c : ℝ) : ℂ) • y := by
    intro y hy
    obtain ⟨x, -, rfl, hx⟩ := hpre y hy
    have ha : LinearMap.adjoint θ (θ x) = (c : ℂ) • x := by
      refine ext_inner_right ℂ fun x' => ?_
      rw [LinearMap.adjoint_inner_left, hx, inner_smul_left, Complex.conj_ofReal]
    show θ (LinearMap.adjoint θ (θ x)) = (c : ℂ) • θ x
    rw [ha, map_smul]
  have hlam : D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = c := Y.tied.lift.lamP (Y.tup t) hU i σ c hne heig
  refine ⟨fun f hf => by rw [hlam]; exact heig f hf, fun _ => ?_⟩
  rw [hlam]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨x, -, rfl, hx⟩ := hpre y hy
  have h := hx x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hyn : 0 < ‖θ x‖ := norm_pos_iff.2 hy0
  have h' : ‖θ x‖ ^ 2 = c * ‖x‖ ^ 2 := by
    have h2 : ((‖θ x‖ ^ 2 : ℝ) : ℂ) = ((c * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      first | (push_cast; exact h) | (push_cast; simpa using h) | (simp only [RCLike.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_mul] at h ⊢; exact h) | (rw [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_pow]; exact h)
    exact Complex.ofReal_injective h2
  by_contra hcn
  push_neg at hcn
  nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hyn]

end GlobalTheory.NRows.LamUsedProof.L0

end
