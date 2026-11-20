import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefRowMod

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx j`. Establish `hcore` using `(GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1`. Establish `hmod` using `hcore.models`. Establish `hθ` using `hmod.inf`. Establish `hν` using `hmod.νW j`.

Establish `hHaar : (R.νW j).IsHaarMeasure` using `hν.1.1`. Establish `hFD` using `hν.2`. Establish `hSig : (Wc D j).SigOK` using `D.sp.W_sig _`. Establish `hSA : SchurAll D` using `fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2`. Establish `hHA : HCAll D` using `fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1`.

Establish `hStd : GlobalTheory.Mem.R3.StdFrame Y.hF (Y.PW j)` using `Y.stdPsi.2 j`. Establish `hcc` using `GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r`. Take `⟨hlin, hherm, hpos⟩` from `GlobalTheory.FinTypesRows.minf_sesq (M := R.MW j (sg0 D A3.A)) (θ := R.θ) (R.νW j) (R.fdW j) (Y.PW j) hSA hSig hθ hHaar hFD`. Establish `hT` using `Y.tied.lift`. Establish `hLev` using `GlobalTheory.FinTypesRows.levOK_levS (Y.PW j) hStd (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))`.

Use `set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) ρ) : ℚ) : ℝ)) * (RealDat.nP F.lv2 false)⁻¹ with hcdef`. Establish `hc : 0 < c` using `mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D A3.A) ρ) (inv_pos.2 (RealDat.nP_pos false))`. Establish `hSm` using `GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (R.MW j (sg0 D A3.A))`. Establish `hex : ∀ x ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∀ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∃ b, Mult.IsMultIP (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y b`. Introduce `x hx y hy`.

Take `⟨N, -, hx', hy'⟩` from `GlobalTheory.FinTypesRows.exists_common (Y.PW j) hx hy`. Conclude with `hSA _ hSig _ R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'`. Set `φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (R.MW j (sg0 D A3.A))` to `(PiTensorProduct.lift : Mult.MMap (R.MW j (sg0 D A3.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ (Submodule.subtype ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc j)) ∘ₗ (Y.IL.jMj j).toLinearMap`. Establish `hφ : ∀ y, PiTensorProduct.lift (φ y) = (Y.IL.jMj j y).1`. Introduce `y`.

Conclude with `LinearEquiv.apply_symm_apply _ _`. Establish `hgood : ∀ y, φ y ∈ Mult.goodPart R.θ (R.MW j (sg0 D A3.A)) (levS _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf j (sg0 D A3.A))`. Introduce `y`. Take `⟨a, ha, hay⟩` from `(Y.IL.jMj j y).2`. Establish `: φ y = a` using `by show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a`.

Rewrite using `[← hay]`. Conclude with `LinearEquiv.symm_apply_apply _ _`. Rewrite using `[this]`. Conclude with `ha`. Establish `hmem : ∀ y, φ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A))` using `fun y => principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))`.

Use `⟨{ A := Mult.MMap (R.MW j (sg0 D A3.A)) ρ := principalLevelFrame.actM (Y.PW j) (R.MW j (sg0 D A3.A)) C := principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)) B := fun x y => (c : ℂ) * Mult.ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y lin := fun x hx y hy z hz c' => by` and prove the remaining obligations. Rewrite using `[hlin x hx y hy z hz c']`. Expand and normalize the polynomial expressions, which then agree. Use `herm := fun x hx y hy => by`. Rewrite using `[map_mul, Complex.conj_ofReal, ← hherm x hx y hy]`.

Use `pos := fun x hx hx0 => by`. Rewrite using `[Complex.re_ofReal_mul]`. Conclude with `mul_pos hc (hpos x hx hx0)`. Use `stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (Y.PW j) hcc h hx`. Use `inv := fun h x hx y hy => by`.

Rewrite using `[GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ R.θ (R.MW j (sg0 D A3.A)) D.R.r (Y.PW j) (R.νW j) (R.fdW j) hSA hSig hθ hHaar hFD h x hx y hy]`. Use `smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (Y.PW j) hx`. Use `adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (Y.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (Y.PW j) hStd) N hN`. Use `φ := φ`. Use `φ_mem := hmem`.

Use `φ_inner := fun x y => by beta_reduce`. Rewrite using `[hT.mj j x y]`. Express the relevant statement in the definitionally equal form `(∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) τ) : ℚ) : ℂ)) * Mult.ipM (R.MW j (sg0 D A3.A)) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.νW j) (R.fdW j) (φ x) (φ y) = _`. Rewrite using `[GlobalTheory.RowModCanon.ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _ (hex _ (hmem x) _ (hmem y)), hcdef]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `isot := fun σ y => by`. Rewrite using `[hT.isot j σ y, Y.prtWE j σ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hay⟩`.

Establish `e : φ y = a` using `by show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a`. Rewrite using `[← hay]`. Conclude with `LinearEquiv.symm_apply_apply _ _`. Rewrite using `[e]`. Conclude with `(Submodule.mem_inf.1 ha).2`.

Introduce `h`. Conclude with `⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc,`. Use the proof step `Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl, fun y => hφ y⟩`.
-/
theorem main : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G]
    (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0),
    GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt →
    ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx j
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hmod := hcore.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame Y.hF (Y.PW j) := Y.stdPsi.2 j
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MW j (sg0 D A3.A)) (θ := R.θ) (R.νW j) (R.fdW j)
    (Y.PW j) hSA hSig hθ hHaar hFD
  have hT := Y.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (Y.PW j) hStd (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) ρ) : ℚ) : ℝ)) * (RealDat.nP F.lv2 false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D A3.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (R.MW j (sg0 D A3.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∀ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)),
      ∃ b, Mult.IsMultIP (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (Y.PW j) hx hy
    exact hSA _ hSig _ R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (R.MW j (sg0 D A3.A)) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW j (sg0 D A3.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc j)) ∘ₗ (Y.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (Y.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart R.θ (R.MW j (sg0 D A3.A)) (levS _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf j (sg0 D A3.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (Y.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (R.MW j (sg0 D A3.A))
            ρ := principalLevelFrame.actM (Y.PW j) (R.MW j (sg0 D A3.A))
            C := principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A))
            B := fun x y => (c : ℂ) * Mult.ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (Y.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ R.θ (R.MW j (sg0 D A3.A)) D.R.r (Y.PW j) (R.νW j) (R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (Y.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (Y.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (Y.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (R.MW j (sg0 D A3.A)) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.νW j) (R.fdW j) (φ x) (φ y) = _
              rw [GlobalTheory.RowModCanon.ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _
                (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, Y.prtWE j σ]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc,
    Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl, fun y => hφ y⟩

end GlobalTheory.RefRowMod
