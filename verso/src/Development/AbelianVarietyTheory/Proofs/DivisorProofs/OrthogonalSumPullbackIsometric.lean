import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open GlobalTheory.Points
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.VMetric

/- English proof (translation)
Introduce `k _ X Y p q E₁ E₂ r s h₁ h₂ π hπ`. Use `Limits.preservesBinaryBiproduct_of_preservesBinaryCoproduct (Scheme.Modules.pullback π) (X := E₁) (Y := E₂)` as an intermediate fact. Use `⟨((Scheme.Modules.pullback π).mapBiprod E₁ E₂).symm, ?_⟩` and prove the remaining obligations. Use `(isIsometry_iff _).2 (VMetric.ext (funext fun σ => PullPull.eq_map_of_frames _ fun z => ?_))` and prove the remaining obligations. Take `⟨c, hc⟩ : ∃ c : Chart (E₁ ⊞ E₂) (r + s), PtsOver.map π hπ _ z ∈ ptsIn p σ c.U` from `⟨_, (h₁.orthSum h₂).isVB.mem_pick _⟩`.

Use `⟨(Chart.pull c (h₁.orthSum h₂).isVB π).map ((Scheme.Modules.pullback π).mapBiprod E₁ E₂), hc, ?_⟩` and prove the remaining obligations. Establish `hz : z ∈ ptsIn q σ (π ⁻¹ᵁ c.U)` using `hc`. Establish `e₀ (a : Fin (r + s)) : (((Chart.pull c (h₁.orthSum h₂).isVB π).map ((Scheme.Modules.pullback π).mapBiprod E₁ E₂)).map ((Scheme.Modules.pullback π).mapBiprod E₁ E₂).symm).e a = pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a)` using `congr(($(((Scheme.Modules.pullback π).mapBiprod E₁ E₂).hom_inv_id)).app (π ⁻¹ᵁ c.U) (pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a)))`. Establish `f₁ : ((Scheme.Modules.pullback π).mapBiprod E₁ E₂).hom ≫ Limits.biprod.fst = (Scheme.Modules.pullback π).map Limits.biprod.fst` using `(congrArg (· ≫ _) (Functor.mapBiprod_hom _ _ _)).trans (Limits.biprod.lift_fst _ _)`. Establish `f₂ : ((Scheme.Modules.pullback π).mapBiprod E₁ E₂).hom ≫ Limits.biprod.snd = (Scheme.Modules.pullback π).map Limits.biprod.snd` using `(congrArg (· ≫ _) (Functor.mapBiprod_hom _ _ _)).trans (Limits.biprod.lift_snd _ _)`.

Establish `e₁ (a : Fin (r + s)) : (Limits.biprod.fst : (Scheme.Modules.pullback π).obj E₁ ⊞ (Scheme.Modules.pullback π).obj E₂ ⟶ (Scheme.Modules.pullback π).obj E₁).app (π ⁻¹ᵁ c.U) (((Chart.pull c (h₁.orthSum h₂).isVB π).map ((Scheme.Modules.pullback π).mapBiprod E₁ E₂)).e a) = pullbackSect …` using `Eq.trans congr(($f₁).app (π ⁻¹ᵁ c.U) (pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a))) (QCoh.pullback_map_app_pullbackSections π _ le_rfl _)`. Establish `e₂ (a : Fin (r + s)) : (Limits.biprod.snd : (Scheme.Modules.pullback π).obj E₁ ⊞ (Scheme.Modules.pullback π).obj E₂ ⟶ (Scheme.Modules.pullback π).obj E₂).app (π ⁻¹ᵁ c.U) (((Chart.pull c (h₁.orthSum h₂).isVB π).map ((Scheme.Modules.pullback π).mapBiprod E₁ E₂)).e a) = pullbackSect …` using `Eq.trans congr(($f₂).app (π ⁻¹ᵁ c.U) (pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a))) (QCoh.pullback_map_app_pullbackSections π _ le_rfl _)`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Use `(Met.form_frame _ _ (by exact hz) a b).symm.trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (Met.form_frame _ _ (by exact hz) a b)` and prove the remaining obligations.

Use `(congrArg₂ (fun s t => (((h₁.orthSum h₂).pull π hπ).met σ).form s t z) (e₀ a) (e₀ b)).trans ?_` and prove the remaining obligations. Use `(((h₁.orthSum h₂).met σ).form_pull π hπ _ _ le_rfl hz).trans ?_` and prove the remaining obligations. Use `(isOrthSum_orthSum h₁ h₂ σ c.U _ _ _ hc).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (isOrthSum_orthSum (h₁.pull π hπ) (h₂.pull π hπ) σ _ _ _ z hz).symm` and prove the remaining obligations. Use `congrArg₂ (· + ·) ?_ ?_` and prove the remaining obligations.

Conclude with `((h₁.met σ).form_pull π hπ _ _ le_rfl hz).symm.trans (congrArg₂ (fun s t => ((h₁.pull π hπ).met σ).form s t z) (e₁ a) (e₁ b)).symm`. Conclude with `((h₂.met σ).form_pull π hπ _ _ le_rfl hz).symm.trans (congrArg₂ (fun s t => ((h₂.pull π hπ).met σ).form s t z) (e₂ a) (e₂ b)).symm`.
-/
theorem isIsometry_pull_orthSum : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (E₁ E₂ : X.Modules) (r s : ℕ) (h₁ : VMetric p E₁ r) (h₂ : VMetric p E₂ s) (π : Y ⟶ X) (hπ : π ≫ p = q), ∃ φ : ((Scheme.Modules.pullback π).obj E₁ ⊞ (Scheme.Modules.pullback π).obj E₂) ≅ (Scheme.Modules.pullback π).obj (E₁ ⊞ E₂), ((h₁.pull π hπ).orthSum (h₂.pull π hπ)).IsIsometry ((h₁.orthSum h₂).pull π hπ) φ := by
  intro k _ X Y p q E₁ E₂ r s h₁ h₂ π hπ
  have := Limits.preservesBinaryBiproduct_of_preservesBinaryCoproduct (Scheme.Modules.pullback π)
    (X := E₁) (Y := E₂)
  refine ⟨((Scheme.Modules.pullback π).mapBiprod E₁ E₂).symm, ?_⟩
  refine (isIsometry_iff _).2 (VMetric.ext (funext fun σ => PullPull.eq_map_of_frames _ fun z => ?_))
  obtain ⟨c, hc⟩ : ∃ c : Chart (E₁ ⊞ E₂) (r + s), PtsOver.map π hπ _ z ∈ ptsIn p σ c.U :=
    ⟨_, (h₁.orthSum h₂).isVB.mem_pick _⟩
  refine ⟨(Chart.pull c (h₁.orthSum h₂).isVB π).map ((Scheme.Modules.pullback π).mapBiprod E₁ E₂), hc, ?_⟩
  have hz : z ∈ ptsIn q σ (π ⁻¹ᵁ c.U) := hc
  have e₀ (a : Fin (r + s)) : (((Chart.pull c (h₁.orthSum h₂).isVB π).map
      ((Scheme.Modules.pullback π).mapBiprod E₁ E₂)).map
      ((Scheme.Modules.pullback π).mapBiprod E₁ E₂).symm).e a =
      pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a) :=
    congr(($(((Scheme.Modules.pullback π).mapBiprod E₁ E₂).hom_inv_id)).app (π ⁻¹ᵁ c.U)
      (pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a)))
  have f₁ : ((Scheme.Modules.pullback π).mapBiprod E₁ E₂).hom ≫ Limits.biprod.fst =
      (Scheme.Modules.pullback π).map Limits.biprod.fst :=
    (congrArg (· ≫ _) (Functor.mapBiprod_hom _ _ _)).trans (Limits.biprod.lift_fst _ _)
  have f₂ : ((Scheme.Modules.pullback π).mapBiprod E₁ E₂).hom ≫ Limits.biprod.snd =
      (Scheme.Modules.pullback π).map Limits.biprod.snd :=
    (congrArg (· ≫ _) (Functor.mapBiprod_hom _ _ _)).trans (Limits.biprod.lift_snd _ _)
  have e₁ (a : Fin (r + s)) : (Limits.biprod.fst : (Scheme.Modules.pullback π).obj E₁ ⊞
      (Scheme.Modules.pullback π).obj E₂ ⟶ (Scheme.Modules.pullback π).obj E₁).app (π ⁻¹ᵁ c.U)
      (((Chart.pull c (h₁.orthSum h₂).isVB π).map
        ((Scheme.Modules.pullback π).mapBiprod E₁ E₂)).e a) =
      pullbackSections π E₁ le_rfl ((Limits.biprod.fst : E₁ ⊞ E₂ ⟶ E₁).app c.U (c.e a)) :=
    Eq.trans congr(($f₁).app (π ⁻¹ᵁ c.U) (pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a)))
      (QCoh.pullback_map_app_pullbackSections π _ le_rfl _)
  have e₂ (a : Fin (r + s)) : (Limits.biprod.snd : (Scheme.Modules.pullback π).obj E₁ ⊞
      (Scheme.Modules.pullback π).obj E₂ ⟶ (Scheme.Modules.pullback π).obj E₂).app (π ⁻¹ᵁ c.U)
      (((Chart.pull c (h₁.orthSum h₂).isVB π).map
        ((Scheme.Modules.pullback π).mapBiprod E₁ E₂)).e a) =
      pullbackSections π E₂ le_rfl ((Limits.biprod.snd : E₁ ⊞ E₂ ⟶ E₂).app c.U (c.e a)) :=
    Eq.trans congr(($f₂).app (π ⁻¹ᵁ c.U) (pullbackSections π (E₁ ⊞ E₂) le_rfl (c.e a)))
      (QCoh.pullback_map_app_pullbackSections π _ le_rfl _)
  refine Matrix.ext fun a b => ?_
  refine (Met.form_frame _ _ (by exact hz) a b).symm.trans ?_
  refine Eq.trans ?_ (Met.form_frame _ _ (by exact hz) a b)
  refine (congrArg₂ (fun s t => (((h₁.orthSum h₂).pull π hπ).met σ).form s t z)
    (e₀ a) (e₀ b)).trans ?_
  refine (((h₁.orthSum h₂).met σ).form_pull π hπ _ _ le_rfl hz).trans ?_
  refine (isOrthSum_orthSum h₁ h₂ σ c.U _ _ _ hc).trans ?_
  refine Eq.trans ?_ (isOrthSum_orthSum (h₁.pull π hπ) (h₂.pull π hπ) σ _ _ _ z hz).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · exact ((h₁.met σ).form_pull π hπ _ _ le_rfl hz).symm.trans
      (congrArg₂ (fun s t => ((h₁.pull π hπ).met σ).form s t z) (e₁ a) (e₁ b)).symm
  · exact ((h₂.met σ).form_pull π hπ _ _ le_rfl hz).symm.trans
      (congrArg₂ (fun s t => ((h₂.pull π hπ).met σ).form s t z) (e₂ a) (e₂ b)).symm

end GlobalTheory.VMetric
