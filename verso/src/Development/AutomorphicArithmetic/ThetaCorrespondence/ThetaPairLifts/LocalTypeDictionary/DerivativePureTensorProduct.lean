import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingRealModel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanThetaFamilyExistsSmooth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanProductRuleDerivative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingRealModelStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.PureProdRule
/- English proof (translation)
Introduce `hP D θ X a a' e Bs Γ Xc om om' hJ hθ hTr l hl f hf φ hφ hvac Ψ hΨ x`. Establish `hline : ∀ i : Fin l.length, ∃ γ ∈ Lines D.sp.cm.sig Γ.W, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)` using `fun i => GlobalTheory.KapXLine.exists_line D θ X (l.get i).1 (l.get i).2 hθ (hl _ (List.get_mem _ _)) e Γ.W hJ`. Use `choose γ hγ hγt using hline`. Establish `hT` using `fun i => _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth hP Γ.M Bs.ψ Xc.β (Xc.β / Xc.α) om hTr.base.cm hTr.base.std hTr.weil (γ i) (hγ i)`. Use `choose T hTa hTadd hT0 using hT`.

Establish `hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1` using `by filter_upwards [hvac, hTr.geo.hM.std] with v h1 h2`. Rewrite using `[h1, h2]`. Take `⟨r, hR, hpure⟩ : ∃ r : (Fin a × Fin (a + a') → AF D.host.F) → ℂ, (∀ g : SInf D.host.F (Fin a × Fin (a + a')), Rest (evI D.host.F) ⇑g r) ∧ ∀ g : SInf D.host.F (Fin a × Fin (a + a')), pure g φ = tens (evI D.host.F) ⇑g r` from `⟨_, fun g => GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd, fun g => rfl⟩`. Establish `hlist : ∀ (t : ℝ) (L : List (Fin l.length)) (g : SInf D.host.F (Fin a × Fin (a + a'))), (L.map fun i => om (1, γ i (Multiplicative.ofAdd t))).prod (tens (evI D.host.F) ⇑g r) = tens (evI D.host.F) ⇑((L.map fun i => T i t).prod g) r`. Introduce `t L`.

Proceed by induction on `L with`. Consider the case `nil => intro g`. Both sides reduce to the same expression. Consider the case `cons i L ih`. Introduce `g`.

Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply]`. Rewrite using `[ih g]`. Conclude with `hTa i t _ r (hR _)`. Set `κ : GA D X →* UA D.sp.cm.sig Γ.W.J` to `{ toFun := kapX X e hJ, map_one' := GlobalTheory.KapXLine.kapX_one X e hJ, map_mul' := GlobalTheory.KapXLine.kapX_mul X e hJ }`. Set `H : GA D X →* Module.End ℂ ((Fin a × Fin (a + a') → AF D.host.F) → ℂ)` to `(om.comp (MonoidHom.inr _ _)).comp κ`.

Establish `hH : ∀ g, H g = om (1, kapX X e hJ g)` using `fun g => rfl`. Establish `hprod : ∀ t : ℝ, om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) = tens (evI D.host.F) ⇑((List.ofFn fun i => T i t).prod f) r`. Introduce `t`. Rewrite using `[← hH, map_list_prod, List.map_map]`. Establish `e1 : l.map (H ∘ fun q => oneP θ X q.1 q.2 t) = (List.finRange l.length).map fun i => om (1, γ i (Multiplicative.ofAdd t))` using `by conv_lhs => rw [← List.ofFn_get l]`.

Rewrite using `[List.map_ofFn, List.ofFn_eq_map]`. Use `List.map_congr_left fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hH, hγt]`. Rewrite using `[e1, hpure, hlist, ← List.ofFn_eq_map]`. Establish `hone : ∀ (i : Fin l.length) (t : ℝ), om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) = tens (evI D.host.F) ⇑(T i t f) r`.

Introduce `i t`. Rewrite using `[← hγt, hpure]`. Conclude with `hTa i t f r (hR f)`. Establish `hd : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j)) * r x) (Ψ i x) 0`. Introduce `i`.

Establish `h` using `(hΨ i).2 x`. Use `h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show _ = om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) x`. Rewrite using `[hone]`. Both sides reduce to the same expression.

Establish `hgoal : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) x) = fun t => (List.ofFn fun i => T i t).prod f (fun j => evI D.host.F (x j)) * r x`. Use function extensionality and compare the values at `t`. Rewrite using `[hprod]`. Both sides reduce to the same expression. Rewrite using `[hgoal]`.

Distinguish the cases in `hr : r x = 0`. Establish `h0 : ∀ i, Ψ i x = 0` using `fun i => by`. Use `hd i` as an intermediate fact. Simplify using `only [hr, mul_zero] at this`. Conclude with `this.unique (hasDerivAt_const _ _)`.

Simplify using `only [hr, mul_zero, h0, Finset.sum_const_zero]`. Conclude with `hasDerivAt_const _ _`. Establish `hc : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j))) (Ψ i x / r x) 0` using `fun i => by`. Use `(hd i).mul_const (r x)⁻¹` as an intermediate fact. Use `(this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [mul_assoc, mul_inv_cancel₀ hr, mul_one]`. Rewrite using `[div_eq_mul_inv]`. Establish `hcore` using `_root_.GlobalTheory.T.archimedean_product_rule_derivative hP Γ.M Bs.ψ Xc.β (Xc.β / Xc.α) om hTr.base.cm hTr.base.std hTr.weil l.length γ hγ T hTa hTadd hT0 f (fun j => evI D.host.F (x j)) (fun i => Ψ i x / r x) hc`. Use `(hcore.mul_const (r x)).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ hr`.
-/
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0 := by
  classical
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hTr l hl f hf φ hφ hvac Ψ hΨ x
  have hline : ∀ i : Fin l.length, ∃ γ ∈ Lines D.sp.cm.sig Γ.W, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t) := fun i =>
    GlobalTheory.KapXLine.exists_line D θ X (l.get i).1 (l.get i).2 hθ (hl _ (List.get_mem _ _)) e Γ.W hJ
  choose γ hγ hγt using hline
  have hT := fun i => _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth hP Γ.M Bs.ψ Xc.β (Xc.β / Xc.α) om hTr.base.cm hTr.base.std hTr.weil (γ i) (hγ i)
  choose T hTa hTadd hT0 using hT
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 := by
    filter_upwards [hvac, hTr.geo.hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨r, hR, hpure⟩ : ∃ r : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ g : SInf D.host.F (Fin a × Fin (a + a')), Rest (evI D.host.F) ⇑g r) ∧
      ∀ g : SInf D.host.F (Fin a × Fin (a + a')), pure g φ = tens (evI D.host.F) ⇑g r :=
    ⟨_, fun g => GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd, fun g => rfl⟩
  have hlist : ∀ (t : ℝ) (L : List (Fin l.length)) (g : SInf D.host.F (Fin a × Fin (a + a'))),
      (L.map fun i => om (1, γ i (Multiplicative.ofAdd t))).prod (tens (evI D.host.F) ⇑g r) =
        tens (evI D.host.F) ⇑((L.map fun i => T i t).prod g) r := by
    intro t L
    induction L with
    | nil => intro g; rfl
    | cons i L ih =>
      intro g
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih g]
      exact hTa i t _ r (hR _)
  let κ : GA D X →* UA D.sp.cm.sig Γ.W.J :=
    { toFun := kapX X e hJ, map_one' := GlobalTheory.KapXLine.kapX_one X e hJ,
      map_mul' := GlobalTheory.KapXLine.kapX_mul X e hJ }
  let H : GA D X →* Module.End ℂ ((Fin a × Fin (a + a') → AF D.host.F) → ℂ) :=
    (om.comp (MonoidHom.inr _ _)).comp κ
  have hH : ∀ g, H g = om (1, kapX X e hJ g) := fun g => rfl
  have hprod : ∀ t : ℝ, om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) =
      tens (evI D.host.F) ⇑((List.ofFn fun i => T i t).prod f) r := by
    intro t
    rw [← hH, map_list_prod, List.map_map]
    have e1 : l.map (H ∘ fun q => oneP θ X q.1 q.2 t) =
        (List.finRange l.length).map fun i => om (1, γ i (Multiplicative.ofAdd t)) := by
      conv_lhs => rw [← List.ofFn_get l]
      rw [List.map_ofFn, List.ofFn_eq_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, hH, hγt]
    rw [e1, hpure, hlist, ← List.ofFn_eq_map]
  have hone : ∀ (i : Fin l.length) (t : ℝ), om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) =
      tens (evI D.host.F) ⇑(T i t f) r := by
    intro i t
    rw [← hγt, hpure]
    exact hTa i t f r (hR f)
  have hd : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j)) * r x) (Ψ i x) 0 := by
    intro i
    have h := (hΨ i).2 x
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show _ = om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) x
    rw [hone]
    rfl
  have hgoal : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) x) =
      fun t => (List.ofFn fun i => T i t).prod f (fun j => evI D.host.F (x j)) * r x := by
    funext t
    rw [hprod]
    rfl
  rw [hgoal]
  by_cases hr : r x = 0
  · have h0 : ∀ i, Ψ i x = 0 := fun i => by
      have := hd i
      simp only [hr, mul_zero] at this
      exact this.unique (hasDerivAt_const _ _)
    simp only [hr, mul_zero, h0, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  · have hc : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j))) (Ψ i x / r x) 0 := fun i => by
      have := (hd i).mul_const (r x)⁻¹
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
      · simp only [mul_assoc, mul_inv_cancel₀ hr, mul_one]
      · rw [div_eq_mul_inv]
    have hcore := _root_.GlobalTheory.T.archimedean_product_rule_derivative hP Γ.M Bs.ψ Xc.β (Xc.β / Xc.α) om hTr.base.cm hTr.base.std hTr.weil l.length γ hγ T hTa
      hTadd hT0 f (fun j => evI D.host.F (x j)) (fun i => Ψ i x / r x) hc
    refine (hcore.mul_const (r x)).congr_deriv ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ hr
end GlobalTheory.PureProdRule
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.PureProdRule.lift_splits_locally | exact _root_.GlobalTheory.PureProdRule.lift_splits_locally | (intros; apply _root_.GlobalTheory.PureProdRule.lift_splits_locally <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.derivative_pure_tensor_product : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0 := by
  first | exact @_root_.GlobalTheory.PureProdRule.lift_splits_locally | exact _root_.GlobalTheory.PureProdRule.lift_splits_locally | (intros; apply _root_.GlobalTheory.PureProdRule.lift_splits_locally <;> assumption)
end
