import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

/- English proof (translation)
Set `M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ))` to `{ carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) ∧ (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) ∧ ∀ w, L b₀ w = l w} add_mem' := by`. Introduce and unpack `l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩`. Use `⟨fun b => L b + L' b, ?_, ?_, fun w => by simp [h3, h3']⟩` and prove the remaining obligations. Use `filter_upwards [h1, h1'] with b hb hb' using hb.add hb'`. Use `filter_upwards [h2, h2'] with b hb hb' using hb.add hb'`.

Use the proof step `zero_mem' := ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _, Eventually.of_forall fun _ => by simp, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c l ⟨L, h1, h2, h3⟩`. Use `⟨fun b => c • L b, ?_, ?_, fun w => by simp [h3]⟩` and prove the remaining obligations. Use `filter_upwards [h1] with b hb using hb.const_smul c`.

Use `filter_upwards [h2] with b hb using hb.const_smul c }`. Establish `hM : M = ⊤`. Establish `h0 : M.dualCoannihilator = ⊥`. Use `eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_` and prove the remaining obligations. Conclude with `(Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩`.

Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]`. Establish `hj : ∀ j : Fin g, LinearMap.proj j ∈ M` using `fun j => hM ▸ Submodule.mem_top`. Use `choose L h1 h2 h3 using hj`. Set `J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ))` to `fun b => ContinuousLinearMap.pi fun j => L j b`. Establish `hJ : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ J b` using `by filter_upwards [eventually_all.2 h1] with b hb`.

Conclude with `(ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b (differentiableAt_pi.2 hb)`. Establish `hJ0 : IsUnit (J b₀)`. Establish `: J b₀ = 1` using `by ext1 w`. Use function extensionality and compare the values at `j`. Conclude with `h3 j w`.

Rewrite using `[this]`. Conclude with `isUnit_one`. Establish `hU : ∀ᶠ b in 𝓝 b₀, IsUnit (J b)` using `hJ.self_of_nhds.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)`. Use `filter_upwards [hJ, hU, eventually_all.2 h2] with b hJb hUb hWb`. Establish `hW : DifferentiableAt ℂ (fun b => J b (W b)) b` using `differentiableAt_pi.2 hWb`.

Use `((hJb.inverse hUb).clm_apply hW).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hJb.continuousAt.eventually (Units.isOpen.mem_nhds hUb)] with b' hb'`. Use `congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b')) (Ring.inverse_mul_cancel _ hb')` as an intermediate fact. Conclude with `this.symm`.
-/
theorem eventually_differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ}
    (W : V → Fin g → ℂ) (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ),
      (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) → (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) →
        L b₀ w = 0) → w = 0) : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) ∧
        (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        refine ⟨fun b => L b + L' b, ?_, ?_, fun w => by simp [h3, h3']⟩
        · filter_upwards [h1, h1'] with b hb hb' using hb.add hb'
        · filter_upwards [h2, h2'] with b hb hb' using hb.add hb'
      zero_mem' := ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _,
        Eventually.of_forall fun _ => by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        refine ⟨fun b => c • L b, ?_, ?_, fun w => by simp [h3]⟩
        · filter_upwards [h1] with b hb using hb.const_smul c
        · filter_upwards [h2] with b hb using hb.const_smul c }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ J b := by
    filter_upwards [eventually_all.2 h1] with b hb
    exact (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b
      (differentiableAt_pi.2 hb)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hU : ∀ᶠ b in 𝓝 b₀, IsUnit (J b) :=
    hJ.self_of_nhds.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)
  filter_upwards [hJ, hU, eventually_all.2 h2] with b hJb hUb hWb
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b := differentiableAt_pi.2 hWb
  refine ((hJb.inverse hUb).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJb.continuousAt.eventually (Units.isOpen.mem_nhds hUb)] with b' hb'
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b')) (Ring.inverse_mul_cancel _ hb')
  exact this.symm

open GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame in

/- English proof (translation)
Establish `h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U`. Use `(top_le_preimage_iff _ U).1 h₀` as an intermediate fact. Rewrite `this` using `[← Category.assoc, ← Spec.map_comp]`. Then use the resulting hypothesis. Take `⟨r, a, hr, H⟩` from `exists_fraction ψ U f _ h₁`. Establish `hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst` using `fun b x => by simp [Chart.dualMapR]`.

Establish `hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd` using `fun b x => by simp [Chart.dualMapR]`. Establish `hr' : ev b₀ r.fst ≠ 0` using `(hf b₀ r) ▸ hr`. Establish `hne : ∀ᶠ b in 𝓝 b₀, ev b r.fst ≠ 0` using `(hev r.fst).self_of_nhds.continuousAt.eventually_ne hr'`. Use `⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev a.snd, hev a.fst, hev r.fst, hev r.snd, hne] with b h1 h2 h3 h4 h5`.

Conclude with `(h1.sub ((h2.mul (h3.inv h5)).mul h4)).mul (h3.inv h5)`. Use `filter_upwards [hne] with b hb`. Take `⟨h, e⟩` from `H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `e1` using `congrArg TrivSqZeroExt.fst e`.

Establish `e2` using `congrArg TrivSqZeroExt.snd e`. Rewrite `e1` using `[TrivSqZeroExt.fst_mul, hf, hf]`. Rewrite `e2` using `[DualNumber.snd_mul, hf, hs, hs]`. Rewrite using `[← e1, ← e2]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_hol_snd_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V)
    (hev : ∀ c, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b c) b)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ F b) ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  have hne : ∀ᶠ b in 𝓝 b₀, ev b r.fst ≠ 0 := (hev r.fst).self_of_nhds.continuousAt.eventually_ne hr'
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹, ?_, ?_⟩
  · filter_upwards [hev a.snd, hev a.fst, hev r.fst, hev r.snd, hne] with b h1 h2 h3 h4 h5
    exact (h1.sub ((h2.mul (h3.inv h5)).mul h4)).mul (h3.inv h5)
  filter_upwards [hne] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

/- English proof (translation)
Establish `h1` using `Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩`. Establish `hp : IsHolTo B p` using `TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)`. Establish `h2` using `TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)`. Establish `hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ)` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ`. Establish `hExp : IsExpAt Z.t (p b₀ ≫ Z.jQ ≫ genι Z) (pushEx Z Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl)` using `isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl (hP b₀)`.

Establish `hW' : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v)` using `by filter_upwards [hW] with b hb`. Rewrite using `[← HolFrameMatrix.dualMap_eq]` and apply the resulting hypothesis. Use `eventually_differentiableAt_of_forms W b₀ fun w hw => ?_` and prove the remaining obligations. Establish `hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)), ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O → fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0`. Introduce `O f hO`.

Use `hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0) ?_ ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun b : Fin n → ℂ => (b, (0 : Fin g → ℂ))) b₀` using `continuousAt_id.prodMk continuousAt_const filter_upwards [hc.preimage_mem_nhds ((hFt O f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hO⟩)] with b hb`. Conclude with `HolLieFrame.differentiableAt_fderiv (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb.1.1 O f hb.2`. Take `⟨Fn, hF, hF'⟩` from `exists_hol_snd_ev v ev b₀ hev O f ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [hW'.self_of_nhds.1]; exact hO)) filter_upwards [hF, (hF'.and hW').eventually_nhds] with b hFb hnear`. Use `hFb.congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hnear] with b' ⟨⟨h, e'⟩, hd⟩`. Conclude with `(hd.2 O h f).symm.trans e'`. Establish `d₁` using `LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'`. Establish `d₀` using `LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0 fun _ _ _ => map_zero _`. Take `⟨u, ⟨hut, hud⟩, -⟩` from `hExp.2.1 0`.

Establish `hu0` using `isDerivAt0_unique hud d₀`. Take `⟨w', -, hw''⟩` from `hExp.2.2 u hut`. Establish `a1 : w = w'` using `hw'' w (by rw [hu0]; exact d₁)`. Establish `a0 : (0 : Fin g → ℂ) = w'` using `hw'' 0 hud`. Conclude with `a1.trans a0.symm`.
-/
theorem eventually_differentiableAt_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) {n : ℕ}
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) {P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hP : ∀ b, IsPeriod (Fu.Di i) ty (P b)) (hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B)
    (hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ) {R : Type} [CommRing R] (v : Sp (DualNumber R) ⟶ Z.t.G.left)
    (ev : (Fin n → ℂ) → (R →+* ℂ)) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (hev : ∀ t, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b t) b) (W : (Fin n → ℂ) → Fin g → ℂ)
    (hW : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (ev b)) ≫ v)) :
    ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hExp : IsExpAt Z.t (p b₀ ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl) :=
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl (hP b₀)
  have hW' : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := by
    filter_upwards [hW] with b hb
    rwa [← HolFrameMatrix.dualMap_eq]
  refine eventually_differentiableAt_of_forms W b₀ fun w hw => ?_
  have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
      ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0) ?_ ?_
    · have hc : ContinuousAt (fun b : Fin n → ℂ => (b, (0 : Fin g → ℂ))) b₀ :=
        continuousAt_id.prodMk continuousAt_const
      filter_upwards [hc.preimage_mem_nhds ((hFt O f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hO⟩)] with b hb
      exact HolLieFrame.differentiableAt_fderiv
        (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb.1.1 O f hb.2
    · obtain ⟨Fn, hF, hF'⟩ := exists_hol_snd_ev v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [hW'.self_of_nhds.1]; exact hO))
      filter_upwards [hF, (hF'.and hW').eventually_nhds] with b hFb hnear
      refine hFb.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with b' ⟨⟨h, e'⟩, hd⟩
      exact (hd.2 O h f).symm.trans e'
  have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
    fun _ _ _ => map_zero _
  obtain ⟨u, ⟨hut, hud⟩, -⟩ := hExp.2.1 0
  have hu0 := isDerivAt0_unique hud d₀
  obtain ⟨w', -, hw''⟩ := hExp.2.2 u hut
  have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
  have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
  exact a1.trans a0.symm

end GlobalTheory.HolCoordEv
