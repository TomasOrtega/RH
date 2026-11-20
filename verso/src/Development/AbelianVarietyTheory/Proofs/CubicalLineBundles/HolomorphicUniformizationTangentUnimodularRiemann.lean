import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.AnyUnif

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Set `c : ℂ → Λ` to `fun t => ⟨t • z, h _ (by rw [map_smul, hz, smul_zero])⟩`. Establish `hc : Continuous c` using `Continuous.subtype_mk (by fun_prop) _`. Establish `e : c 1 = c 0` using `(IsLocallyConstant.iff_continuous c).2 hc |>.apply_eq_of_preconnectedSpace 1 0`.

Simplify `congrArg Subtype.val e` using `[c]`.
-/
theorem injective_of_ker_le_discrete {g g' : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ z, F z = 0 → z ∈ Λ) : Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  let c : ℂ → Λ := fun t => ⟨t • z, h _ (by rw [map_smul, hz, smul_zero])⟩
  have hc : Continuous c := Continuous.subtype_mk (by fun_prop) _
  have e : c 1 = c 0 := (IsLocallyConstant.iff_continuous c).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa [c] using congrArg Subtype.val e

/- English proof (translation)
Take `⟨w, hw⟩ : LBIso (L.pull (𝟙 X)) L` from `LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) (chartPullId L) (PolBaseChange.lbIso_refl hL)`. Conclude with `⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩`.
-/
theorem lbIso_pow_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) :
    LBIso (lbPow (L.pull (𝟙 X)) n) (lbPow L n) := by
  obtain ⟨w, hw⟩ : LBIso (L.pull (𝟙 X)) L :=
    LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) (chartPullId L) (PolBaseChange.lbIso_refl hL)
  exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩

/- English proof (translation)
Introduce `hU P u`. Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨u', Hm', χ', Ef', hA', -, h1, h2, -, -, hE, hB, -⟩` from `hU P rig hrig`. Take `⟨F, hF₀, -⟩` from `HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L P.g P.g u u' h1 h2 (𝟙 P.A) inferInstance`. Establish `hF : ∀ z, u'.ex (F z) = u.ex z` using `fun z => (hF₀ z).trans (Category.comp_id _)`.

Establish `hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ` using `fun z => by rw [← u'.ker, hF, u.ker]`. Use `haveI := u.discrete`. Establish `hinj` using `injective_of_ker_le_discrete u.Λ F fun z hz => (hΛ z).1 (hz ▸ u'.Λ.zero_mem)`. Set `e` to `LinearEquiv.ofInjectiveEndo F hinj`. Establish `he : ∀ z, e z = F z` using `fun _ => rfl`.

Establish `hd : ∀ w v, IsTangent v → (u.IsDiff w v ↔ u'.IsDiff (e w) v)` using `fun w v hv => by`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify `HomLinear.isDiff_comp u u' (𝟙 P.A) F hF₀ hv h` using `[he]`. Introduce `h`.

Simplify using `using HomLinear.isDiff_comp u' u (𝟙 P.A) e.symm.toLinearMap (fun z => by rw [Category.comp_id, ← hF, ← he]; simp) hv h`. Use `⟨fun v hv => ?_, fun w => ?_, fun Hm χ hA => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hu⟩` from `h1 v hv`. Use `⟨e.symm w, (hd _ v hv).2 (by simpa using hw), fun w' hw' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hu _ ((hd _ v hv).1 hw'), e.symm_apply_apply]`.

Take `⟨v, ⟨hv, hw⟩, hu⟩` from `h2 (e w)`. Conclude with `⟨v, ⟨hv, (hd w v hv).2 hw⟩, fun v' hv' => hu v' ⟨hv'.1, (hd w v' hv'.1).1 hv'.2⟩⟩`. Establish `hH` using `hermForm_pull_eq_of_lbIso_pow P.A P.A P.L P.L P.isLB P.isLB P.g P.g u u' Hm χ Hm' χ' hA hA' (𝟙 P.A) F hF₀ 1 1 (lbIso_pow_pull_id P.isLB 1)`. Simplify using `only [Nat.cast_one, _root_.one_mul] at hH`. Set `l : u.Λ ≃ₗ[ℤ] u'.Λ` to `{ toFun := fun a => ⟨e a, (hΛ a).2 a.2⟩ invFun := fun b => ⟨e.symm b, (hΛ _).1 (by rw [← he, e.apply_symm_apply]; exact b.2)⟩ map_add' := fun a b => Subtype.ext (map_add e _ _) map_smul' := fun n a => Subtype.ext (map_zsmul e n _) left_inv := fun a => Subtype.ext (e.symm_apply_ap …`.

Use `⟨Ef'.comp l.toLinearMap l.toLinearMap, fun a b => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hH]`. Conclude with `hE (l a) (l b)`. Conclude with `l.dualMap.bijective.comp (hB.comp l.bijective)`.
-/
theorem tangent_and_unimodular : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g),
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
      ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
        Function.Bijective Ef := by
  intro hU P u
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u', Hm', χ', Ef', hA', -, h1, h2, -, -, hE, hB, -⟩ := hU P rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L P.g P.g u u' h1 h2
    (𝟙 P.A) inferInstance
  have hF : ∀ z, u'.ex (F z) = u.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by rw [← u'.ker, hF, u.ker]
  haveI := u.discrete
  have hinj := injective_of_ker_le_discrete u.Λ F fun z hz => (hΛ z).1 (hz ▸ u'.Λ.zero_mem)
  let e := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun _ => rfl
  have hd : ∀ w v, IsTangent v → (u.IsDiff w v ↔ u'.IsDiff (e w) v) := fun w v hv => by
    constructor
    · intro h
      simpa [he] using HomLinear.isDiff_comp u u' (𝟙 P.A) F hF₀ hv h
    · intro h
      simpa using HomLinear.isDiff_comp u' u (𝟙 P.A) e.symm.toLinearMap
        (fun z => by rw [Category.comp_id, ← hF, ← he]; simp) hv h
  refine ⟨fun v hv => ?_, fun w => ?_, fun Hm χ hA => ?_⟩
  · obtain ⟨w, hw, hu⟩ := h1 v hv
    refine ⟨e.symm w, (hd _ v hv).2 (by simpa using hw), fun w' hw' => ?_⟩
    rw [← hu _ ((hd _ v hv).1 hw'), e.symm_apply_apply]
  · obtain ⟨v, ⟨hv, hw⟩, hu⟩ := h2 (e w)
    exact ⟨v, ⟨hv, (hd w v hv).2 hw⟩, fun v' hv' => hu v' ⟨hv'.1, (hd w v' hv'.1).1 hv'.2⟩⟩
  · have hH := hermForm_pull_eq_of_lbIso_pow P.A P.A P.L P.L P.isLB P.isLB P.g P.g u u' Hm χ Hm' χ' hA hA'
      (𝟙 P.A) F hF₀ 1 1 (lbIso_pow_pull_id P.isLB 1)
    simp only [Nat.cast_one, _root_.one_mul] at hH
    let l : u.Λ ≃ₗ[ℤ] u'.Λ :=
      { toFun := fun a => ⟨e a, (hΛ a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (hΛ _).1 (by rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e _ _)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n _)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply _)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply _) }
    refine ⟨Ef'.comp l.toLinearMap l.toLinearMap, fun a b => ?_, ?_⟩
    · rw [← hH]
      exact hE (l a) (l b)
    · exact l.dualMap.bijective.comp (hB.comp l.bijective)

end GlobalTheory.AnyUnif
