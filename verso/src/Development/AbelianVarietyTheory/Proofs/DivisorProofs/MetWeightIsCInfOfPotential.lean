import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt

namespace MetricWeightSmoothness
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MetWeightSmooth

/- English proof (translation)
Take `⟨U, hy, a, e⟩` from `h.regAt.exists_fnOf`. Establish `hW : y ∈ ptsIn Y.str σ U` using `mem_ptsIn.2 hy`. Use `⟨U, Unit, inferInstance, fun _ => a, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0}, hW, isOpen_ne_fun (continuous_apply _) continuous_const, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ev Y.str σ U a y ≠ 0`. Use `ratVal_ne_zero h` as an intermediate fact.

Rewrite `this` using `[← e, ratVal_fnOf hW]`. Then use the resulting hypothesis. Use `ContDiffOn.log ?_ fun v hv => pow_ne_zero 2 (norm_ne_zero_iff.2 hv)` and prove the remaining obligations. Conclude with `((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn`. Use `filter_upwards [(isOpen_ptsIn U).mem_nhds hW] with z hz`. Rewrite using `[← e, ratVal_fnOf hz]`.
-/
theorem cInfAt_log_normSq_ratVal {F : Type} [Field F] {σ : F →+* ℂ} {Y : Var F} {g : Y.Fn} {y : Pts Y σ}
    (h : UnitAt (under y) g) : CInfAt (fun z : Pts Y σ => Real.log (‖ratVal g z‖ ^ 2)) y := by
  obtain ⟨U, hy, a, e⟩ := h.regAt.exists_fnOf
  have hW : y ∈ ptsIn Y.str σ U := mem_ptsIn.2 hy
  refine ⟨U, Unit, inferInstance, fun _ => a, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0},
    hW, isOpen_ne_fun (continuous_apply _) continuous_const, ?_, ?_, ?_⟩
  · show ev Y.str σ U a y ≠ 0
    have := ratVal_ne_zero h
    rwa [← e, ratVal_fnOf hW] at this
  · refine ContDiffOn.log ?_ fun v hv => pow_ne_zero 2 (norm_ne_zero_iff.2 hv)
    exact ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn
  · filter_upwards [(isOpen_ptsIn U).mem_nhds hW] with z hz
    rw [← e, ratVal_fnOf hz]

/- English proof (translation)
Establish `hS : IsOpen (h.symm ⁻¹' U)` using `hU.preimage h.symm.continuous`. Establish `hs : (tAtlas A h).SmoothOn (h.symm ⁻¹' U) (fun z => φ (h.symm z))` using `fun j => by`. Establish `e₁ : (fun z => φ (h.symm z)) ∘ ((tAtlas A h).chart j).symm = φ ∘ (A.chart j).symm`. Use function extensionality and compare the values at `fun v => by simp [tAtlas_symm]`. Establish `e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹' (h.symm ⁻¹' U) = (A.chart j).target ∩ (A.chart j).symm ⁻¹' U`.

Use extensionality with `v`. Simplify using `[tAtlas_symm, tAtlas_target]`. Rewrite using `[e₁, e₂]`. Conclude with `hφ j`. Conclude with `(cInfAt_iff_smoothOn hA.anRead hS).2 ((hA.smoothOn_iff hA.anRead hS).1 hs) y hy`.
-/
theorem cInfAt_of_smoothOn_tAtlas {F : Type} [Field F] {σ : F →+* ℂ} {Y : Var F} {e : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas e X} {h : X ≃ₜ Pts Y σ} (hA : IsAlgAtlas (tAtlas A h)) {U : Set X} (hU : IsOpen U) {φ : X → ℝ}
    (hφ : A.SmoothOn U φ) {y : Pts Y σ} (hy : h.symm y ∈ U) : CInfAt (fun z => φ (h.symm z)) y := by
  have hS : IsOpen (h.symm ⁻¹' U) := hU.preimage h.symm.continuous
  have hs : (tAtlas A h).SmoothOn (h.symm ⁻¹' U) (fun z => φ (h.symm z)) := fun j => by
    have e₁ : (fun z => φ (h.symm z)) ∘ ((tAtlas A h).chart j).symm = φ ∘ (A.chart j).symm :=
      funext fun v => by simp [tAtlas_symm]
    have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹' (h.symm ⁻¹' U) =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
      ext v
      simp [tAtlas_symm, tAtlas_target]
    rw [e₁, e₂]
    exact hφ j
  exact (cInfAt_iff_smoothOn hA.anRead hS).2 ((hA.smoothOn_iff hA.anRead hS).1 hs) y hy

/- English proof (translation)
Introduce `F _ _ C Y e M I Δ m hm Q hQ σ`. Take `⟨a, rfl⟩` from `I.ε.surjective σ`. Introduce `c y hy`. Take `⟨x, rfl⟩` from `(I.pt a).surjective y`. Establish `hxU : (I.pt a).symm (I.pt a x) ∈ (Q a).U x` using `by simpa using (Q a).mem_U x`.

Take `⟨f, hf⟩` from `(hQ a).1 x`. Establish `key : ∀ z : Pts Y (I.ε a), (I.pt a).symm z ∈ (Q a).U x → z ∈ ptsIn Y.str (I.ε a) ((toLB Δ).U c) → UnitAt (under z) (f * (c.1.2 : Y.Fn)) ∧ (metWeight Δ (m _) (hm _)).φ c z = 2 * (Q a).φ x ((I.pt a).symm z) + Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2)`. Introduce `z hz hzc`. Establish `hzc' : under z ∈ c.1.1` using `mem_ptsIn.1 hzc`. Take `⟨h₁, h₂, h₃⟩` from `hf _ hz`.

Rewrite `h₁`, `h₂`, `h₃` using `[Homeomorph.apply_symm_apply]`. Establish `he : Δ.IsEqn (under z) c.1.2` using `c.2.2 _ hzc'`. Establish `hu` using `he.generatesAt_iff.1 h₁`. Establish `hgen` using `CartierDiv.isEqn_iff_generatesAt_inv.1 he`. Establish `hp` using `pn_pos_of_generatesAt (C := C) hgen (hm _ z)`.

Establish `hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2` using `pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2`. Establish `e₁ : (f * (c.1.2 : Y.Fn)) * (c.1.2 : Y.Fn)⁻¹ = f`. Rewrite using `[mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]`. Establish `e₂` using `C.pn_mul Y _ Δ (m _) _ _ z hu.regAt hgen.regularAt`. Rewrite `e₂` using `[e₁]`.

Use `⟨hu, ?_⟩` and prove the remaining obligations. Rewrite using `[metWeight_φ, h₃, lnN, e₂, Real.log_mul hr.ne' hp.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : IsOpen ((I.pt a).symm ⁻¹' (Q a).U x)` using `((Q a).isOpen_U x).preimage (I.pt a).symm.continuous`. Use `(((cInfAt_of_smoothOn_tAtlas (isAlgAtlas_tAtlas I a) ((Q a).isOpen_U x) ((hQ a).2.1 x) hxU).const_mul 2).add (cInfAt_log_normSq_ratVal (key _ hxU hy).1)).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hS.mem_nhds hxU, (isOpen_ptsIn _).mem_nhds hy] with z hz hzc`. Conclude with `(key z hz hzc).2`.
-/
theorem metWeight_isCInf : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y) (Q : ∀ a, LocPot (M.X a)), (∀ a, IsPot (I.pt a) (m (I.ε a)) (Q a) ∧ IsPotential (M.A a) (Q a)) → ∀ σ, (metWeight Δ (m σ) (hm σ)).IsCInf := by
  intro F _ _ C Y e M I Δ m hm Q hQ σ
  obtain ⟨a, rfl⟩ := I.ε.surjective σ
  intro c y hy
  obtain ⟨x, rfl⟩ := (I.pt a).surjective y
  have hxU : (I.pt a).symm (I.pt a x) ∈ (Q a).U x := by simpa using (Q a).mem_U x
  obtain ⟨f, hf⟩ := (hQ a).1 x
  have key : ∀ z : Pts Y (I.ε a), (I.pt a).symm z ∈ (Q a).U x → z ∈ ptsIn Y.str (I.ε a) ((toLB Δ).U c) →
      UnitAt (under z) (f * (c.1.2 : Y.Fn)) ∧ (metWeight Δ (m _) (hm _)).φ c z =
        2 * (Q a).φ x ((I.pt a).symm z) + Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2) := by
    intro z hz hzc
    have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
    obtain ⟨h₁, h₂, h₃⟩ := hf _ hz
    rw [Homeomorph.apply_symm_apply] at h₁ h₂ h₃
    have he : Δ.IsEqn (under z) c.1.2 := c.2.2 _ hzc'
    have hu := he.generatesAt_iff.1 h₁
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hp := pn_pos_of_generatesAt (C := C) hgen (hm _ z)
    have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    have e₁ : (f * (c.1.2 : Y.Fn)) * (c.1.2 : Y.Fn)⁻¹ = f := by
      rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
    have e₂ := C.pn_mul Y _ Δ (m _) _ _ z hu.regAt hgen.regularAt
    rw [e₁] at e₂
    refine ⟨hu, ?_⟩
    rw [metWeight_φ, h₃, lnN, e₂, Real.log_mul hr.ne' hp.ne']
    ring
  have hS : IsOpen ((I.pt a).symm ⁻¹' (Q a).U x) := ((Q a).isOpen_U x).preimage (I.pt a).symm.continuous
  refine (((cInfAt_of_smoothOn_tAtlas (isAlgAtlas_tAtlas I a) ((Q a).isOpen_U x) ((hQ a).2.1 x) hxU).const_mul 2).add
    (cInfAt_log_normSq_ratVal (key _ hxU hy).1)).congr ?_
  filter_upwards [hS.mem_nhds hxU, (isOpen_ptsIn _).mem_nhds hy] with z hz hzc
  exact (key z hz hzc).2

end GlobalTheory.CompanionTheory.MetWeightSmooth

end
end

end MetricWeightSmoothness
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
/- English proof (translation)
Apply the tactic sequence `first | exact @MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf | exact MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf | (intros; apply MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.me …`.
-/
theorem _root_.GlobalTheory.Adopt.metWeight_isCInf_of_potential : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y) (Q : ∀ a, LocPot (M.X a)), (∀ a, IsPot (I.pt a) (m (I.ε a)) (Q a) ∧ IsPotential (M.A a) (Q a)) → ∀ σ, (metWeight Δ (m σ) (hm σ)).IsCInf := by
  first | exact @MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf | exact MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf | (intros; apply MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf <;> assumption)

end
