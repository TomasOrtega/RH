import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitIdx

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting in

/- English proof (translation)
Introduce `D S T v φ ε hε BS BT hS hT g`. Establish `hch` using `(GlobalTheory.SplitProjChart.chart_rdA D v φ ε hε).1`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.SplitHomLattice.mem_latO_iff_intM ε v (rdA φ) hε.1 hch S T BS BT hS hT`. Establish `hL : ∀ V : HSp D, ((frameLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) = L0c D V`. Introduce `V`.

Use extensionality with `x`. Use `show V.frame.equivFun.symm x ∈ V.L0 ↔ _`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Both sides reduce to the same expression. Use `set Hf := GlobalTheory.PlaceModel.half S T ε with hHf`.

Use `set P := (grpCo φ T BT g).1 with hP`. Set `Ψ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)` to `AddMonoidHom.mk' (fun u => c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1)) (fun x y => by`. Simplify using `only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add])`. Establish `hΨ : ∀ u, Ψ u = c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1)` using `fun _ => rfl`. Establish `hmemH : ∀ u ∈ Hf, (u ∈ halfLat S T ε ↔ Ψ u ∈ intMat D.host.F v T.rank S.rank)`.

Introduce `u hu`. Establish `hu' : IsHalf ε u` using `(GlobalTheory.PlaceModel.isHalf_iff S T).2 hu`. Rewrite using `[halfLat, AddSubgroup.mem_inf, hL S, hL T, hΨ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, -⟩ i j`.

Conclude with `GlobalTheory.SplitHecke.isInt_Ov.1 ((hc u hu').1 h i j)`. Introduce `h`. Conclude with `⟨(hc u hu').2 fun i j => GlobalTheory.SplitHecke.isInt_Ov.2 (h i j), hu⟩`. Establish `hmt1 : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1`. Rewrite using `[inv_one]`.

Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one]`. Both sides reduce to the same expression. Establish `hA : ∀ u, Ψ (actL S T g u) = P * Ψ u`. Introduce `u`.

Express the relevant statement in the definitionally equal form `Ψ (actO S T 1 g u) = _`. Rewrite using `[actO, hmt1, Matrix.mul_one, hΨ, hΨ, hP, grpCo, Matrix.mul_smul]`. Use `congr 1`. Rewrite using `[Matrix.map_mul]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc BT.1, Units.mul_inv, Matrix.one_mul]`. Both sides reduce to the same expression. Establish `hAHf : ∀ u ∈ Hf, actL S T g u ∈ Hf`. Introduce `u hu`. Establish `hu'` using `(GlobalTheory.PlaceModel.isHalf_iff S T).2 hu`.

Use `(GlobalTheory.PlaceModel.isHalf_iff S T).1 fun i j => ?_` and prove the remaining obligations. Use `show ε * actO S T 1 g u i j = actO S T 1 g u i j`. Rewrite using `[actO, hmt1, Matrix.mul_one, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `(mul_left_comm ε _ _).trans (congrArg (Formalism.L2.Theta.mt T g i k * ·) (hu' k j))`.

Set `f : Hf →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)` to `Ψ.comp Hf.subtype`. Establish `hbij` using `GlobalTheory.PlaceCoord.bijOn_map (S := S) (T := T) hch hε.1.1 hε.2.2`. Establish `hf_inj : Function.Injective f`. Introduce `x y hxy`. Establish `hxy' : Ψ x = Ψ y` using `hxy`.

Rewrite `hxy'` using `[hΨ, hΨ]`. Establish `h1 : (BT⁻¹).1 * (x : WO S T).map (rdA φ) * BS.1 = (BT⁻¹).1 * (y : WO S T).map (rdA φ) * BS.1` using `smul_right_injective (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) hc0 hxy'`. Establish `h2` using `congrArg (fun M => BT.1 * M * (BS⁻¹).1) h1`. Simplify using `only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2`. Simplify using `only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2`.

Conclude with `Subtype.ext (hbij.injOn ((GlobalTheory.PlaceModel.isHalf_iff S T).2 x.2) ((GlobalTheory.PlaceModel.isHalf_iff S T).2 y.2) h2)`. Establish `hf_surj : Function.Surjective f`. Introduce `y`. Take `⟨t, ht, ht'⟩` from `GlobalTheory.PlaceCoord.exists_half hch hε.1.1 hε.2.2 (c⁻¹ • (BT.1 * y * (BS⁻¹).1))`. Use `⟨⟨t, (GlobalTheory.PlaceModel.isHalf_iff S T).1 ht⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Ψ t = y`. Rewrite using `[hΨ, ht', Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]`. Simplify using `only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Establish `hH : halfLat S T ε ≤ Hf` using `inf_le_right`.

Establish `hK : (halfLat S T ε).map (actL S T g) ≤ Hf`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `hAHf u (hH hu)`. Establish `e1 : ((halfLat S T ε).addSubgroupOf Hf).map f = intMat D.host.F v T.rank S.rank`. Use extensionality with `y`.

Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(hmemH w w.2).1 (AddSubgroup.mem_addSubgroupOf.1 hw)`. Introduce `hy`.

Take `⟨w, hw⟩` from `hf_surj y`. Use `⟨w, AddSubgroup.mem_addSubgroupOf.2 ((hmemH w w.2).2 ?_), hw⟩` and prove the remaining obligations. Conclude with `hw ▸ hy`. Establish `e2 : (((halfLat S T ε).map (actL S T g)).addSubgroupOf Hf).map f = (intMat D.host.F v T.rank S.rank).map (mulL P)`. Use extensionality with `y`.

Rewrite using `[AddSubgroup.mem_map, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨u, hu, hw⟩` from `AddSubgroup.mem_map.1 (AddSubgroup.mem_addSubgroupOf.1 hw)`. Use `⟨Ψ u, (hmemH u (hH hu)).1 hu, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `P * Ψ u = Ψ (w : WO S T)`. Rewrite using `[← hw, hA]`. Introduce and unpack `⟨z, hz, rfl⟩`. Take `⟨w, hw⟩` from `hf_surj z`. Establish `hz' : Ψ w ∈ intMat D.host.F v T.rank S.rank` using `hw ▸ hz`.

Use `⟨⟨actL S T g w, hAHf w w.2⟩, AddSubgroup.mem_addSubgroupOf.2 ⟨w, (hmemH w w.2).2 hz', rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ψ (actL S T g w) = mulL P z`. Rewrite using `[hA w, ← hw]`. Both sides reduce to the same expression. Rewrite using `[← AddSubgroup.relIndex_addSubgroupOf hK, ← AddSubgroup.relIndex_map_map_of_injective _ _ hf_inj, e1, e2]`.
-/
theorem relIndex_half_act : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (ε : AE D), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS → GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT → ∀ g : GA D T, (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) = (GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).relIndex ((GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).map (GlobalTheory.SplitIdx.mulL (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT g).1)) := by
  intro D S T v φ ε hε BS BT hS hT g
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ ε hε).1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SplitHomLattice.mem_latO_iff_intM ε v (rdA φ) hε.1 hch S T BS BT hS hT
  have hL : ∀ V : HSp D, ((frameLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) = L0c D V := by
    intro V
    ext x
    show V.frame.equivFun.symm x ∈ V.L0 ↔ _
    rw [Module.Basis.equivFun_symm_apply]
    rfl
  set Hf := GlobalTheory.PlaceModel.half S T ε with hHf
  set P := (grpCo φ T BT g).1 with hP
  let Ψ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    AddMonoidHom.mk' (fun u => c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1)) (fun x y => by
      simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add])
  have hΨ : ∀ u, Ψ u = c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1) := fun _ => rfl
  have hmemH : ∀ u ∈ Hf, (u ∈ halfLat S T ε ↔ Ψ u ∈ intMat D.host.F v T.rank S.rank) := by
    intro u hu
    have hu' : IsHalf ε u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    rw [halfLat, AddSubgroup.mem_inf, hL S, hL T, hΨ]
    constructor
    · rintro ⟨h, -⟩ i j
      exact GlobalTheory.SplitHecke.isInt_Ov.1 ((hc u hu').1 h i j)
    · intro h
      exact ⟨(hc u hu').2 fun i j => GlobalTheory.SplitHecke.isInt_Ov.2 (h i j), hu⟩
  have hmt1 : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hA : ∀ u, Ψ (actL S T g u) = P * Ψ u := by
    intro u
    change Ψ (actO S T 1 g u) = _
    rw [actO, hmt1, Matrix.mul_one, hΨ, hΨ, hP, grpCo, Matrix.mul_smul]
    congr 1
    rw [Matrix.map_mul]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc BT.1, Units.mul_inv, Matrix.one_mul]
    rfl
  have hAHf : ∀ u ∈ Hf, actL S T g u ∈ Hf := by
    intro u hu
    have hu' := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    refine (GlobalTheory.PlaceModel.isHalf_iff S T).1 fun i j => ?_
    show ε * actO S T 1 g u i j = actO S T 1 g u i j
    rw [actO, hmt1, Matrix.mul_one, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (mul_left_comm ε _ _).trans (congrArg (Formalism.L2.Theta.mt T g i k * ·) (hu' k j))
  let f : Hf →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := Ψ.comp Hf.subtype
  have hbij := GlobalTheory.PlaceCoord.bijOn_map (S := S) (T := T) hch hε.1.1 hε.2.2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : Ψ x = Ψ y := hxy
    rw [hΨ, hΨ] at hxy'
    have h1 : (BT⁻¹).1 * (x : WO S T).map (rdA φ) * BS.1 = (BT⁻¹).1 * (y : WO S T).map (rdA φ) * BS.1 :=
      smul_right_injective (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) hc0 hxy'
    have h2 := congrArg (fun M => BT.1 * M * (BS⁻¹).1) h1
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
    exact Subtype.ext (hbij.injOn ((GlobalTheory.PlaceModel.isHalf_iff S T).2 x.2) ((GlobalTheory.PlaceModel.isHalf_iff S T).2 y.2) h2)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨t, ht, ht'⟩ := GlobalTheory.PlaceCoord.exists_half hch hε.1.1 hε.2.2 (c⁻¹ • (BT.1 * y * (BS⁻¹).1))
    refine ⟨⟨t, (GlobalTheory.PlaceModel.isHalf_iff S T).1 ht⟩, ?_⟩
    change Ψ t = y
    rw [hΨ, ht', Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hH : halfLat S T ε ≤ Hf := inf_le_right
  have hK : (halfLat S T ε).map (actL S T g) ≤ Hf := by
    rintro _ ⟨u, hu, rfl⟩
    exact hAHf u (hH hu)
  have e1 : ((halfLat S T ε).addSubgroupOf Hf).map f = intMat D.host.F v T.rank S.rank := by
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmemH w w.2).1 (AddSubgroup.mem_addSubgroupOf.1 hw)
    · intro hy
      obtain ⟨w, hw⟩ := hf_surj y
      refine ⟨w, AddSubgroup.mem_addSubgroupOf.2 ((hmemH w w.2).2 ?_), hw⟩
      exact hw ▸ hy
  have e2 : (((halfLat S T ε).map (actL S T g)).addSubgroupOf Hf).map f =
      (intMat D.host.F v T.rank S.rank).map (mulL P) := by
    ext y
    rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, hw⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_addSubgroupOf.1 hw)
      refine ⟨Ψ u, (hmemH u (hH hu)).1 hu, ?_⟩
      change P * Ψ u = Ψ (w : WO S T)
      rw [← hw, hA]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := hf_surj z
      have hz' : Ψ w ∈ intMat D.host.F v T.rank S.rank := hw ▸ hz
      refine ⟨⟨actL S T g w, hAHf w w.2⟩, AddSubgroup.mem_addSubgroupOf.2 ⟨w, (hmemH w w.2).2 hz', rfl⟩, ?_⟩
      change Ψ (actL S T g w) = mulL P z
      rw [hA w, ← hw]
      rfl
  rw [← AddSubgroup.relIndex_addSubgroupOf hK, ← AddSubgroup.relIndex_map_map_of_injective _ _ hf_inj, e1, e2]

end GlobalTheory.SplitIdx

end
