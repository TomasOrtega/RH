import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiProd

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`.

Repeatedly rewrite using `[MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero]`. Simplify using the standard rewrite rules. Use `_ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by`. Rewrite using `[← ih (fun i => f (Fin.succ i)) (fun i => hf _)]`. Conclude with `lintegral_prod_mul (hf 0).aemeasurable (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable`.

Use `_ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]`.
-/
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero]
          simp
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [← ih (fun i => f (Fin.succ i)) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/- English proof (translation)
Set `e` to `(Fintype.equivFin ι).symm`. Rewrite using `[← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`. Repeatedly rewrite using `[← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]`. Conclude with `lintegral_fin_nat_prod (fun i => f (e i)) (fun i => hf _)`.
-/
theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod (fun i => f (e i)) (fun i => hf _)

/- English proof (translation)
Use `haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i => SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (hfin i))`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi, lintegral_fintype_prod _ hf]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[withDensity_apply _ (hs i)]`.
-/
theorem pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fintype_prod _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

end PiProd

section WeilGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/- English proof (translation)
Establish `hF : Measurable fun p : G × G => f (p.1 * p.2)` using `hf.comp measurable_mul`. Establish `hg : Measurable fun x => ∫⁻ s, f (s * x) ∂μS` using `hF.lintegral_prod_left'`. Establish `hBinv : ∀ x, ∫⁻ s, B (s⁻¹ * x) ∂μS = 1`. Introduce `x`. Establish `h1 : ∫⁻ s, B (s * x) ∂(μS.map fun s => s⁻¹) = ∫⁻ s, B (s⁻¹ * x) ∂μS` using `lintegral_map (hBm.comp (measurable_mul_const x)) measurable_inv`.

Rewrite using `[← h1, hinv, hb1]`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hBm hg]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[Pi.mul_apply]`. Conclude with `(lintegral_const_mul _ (hf.comp (measurable_mul_const x))).symm`. Use `_ = ∫⁻ s, ∫⁻ x, B x * f (s * x) ∂μG ∂μS := lintegral_lintegral_swap ((hBm.comp measurable_fst).mul (hf.comp (measurable_snd.mul measurable_fst))).aemeasurable`. Use `_ = ∫⁻ s, ∫⁻ x, B (s⁻¹ * x) * f x ∂μG ∂μS := by`. Use `lintegral_congr fun s => ?_` and prove the remaining obligations.

Simplify `lintegral_mul_left_eq_self (μ := μG) (fun x => B (s⁻¹ * x) * f x) s` using `only [inv_mul_cancel_left]`. Use `_ = ∫⁻ x, ∫⁻ s, B (s⁻¹ * x) * f x ∂μS ∂μG := lintegral_lintegral_swap ((hBm.comp (measurable_fst.inv.mul measurable_snd)).mul (hf.comp measurable_snd)).aemeasurable`. Use `_ = ∫⁻ x, f x ∂μG := by`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[show ∫⁻ s, B (s⁻¹ * x) * f x ∂μS = (∫⁻ s, B (s⁻¹ * x) ∂μS) * f x from lintegral_mul_const _ (hBm.comp (measurable_inv.mul_const x)), hBinv, one_mul]`.
-/
theorem weil_of_bruhat (μG μS : Measure G) [SigmaFinite μG] [SFinite μS] [μG.IsMulLeftInvariant]
    (B : G → ℝ≥0∞) (hBm : Measurable B) (hinv : μS.map (fun s => s⁻¹) = μS)
    (hb1 : ∀ x, ∫⁻ s, B (s * x) ∂μS = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂(μG.withDensity B) := by
  have hF : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp measurable_mul
  have hg : Measurable fun x => ∫⁻ s, f (s * x) ∂μS := hF.lintegral_prod_left'
  have hBinv : ∀ x, ∫⁻ s, B (s⁻¹ * x) ∂μS = 1 := by
    intro x
    have h1 : ∫⁻ s, B (s * x) ∂(μS.map fun s => s⁻¹) = ∫⁻ s, B (s⁻¹ * x) ∂μS :=
      lintegral_map (hBm.comp (measurable_mul_const x)) measurable_inv
    rw [← h1, hinv, hb1]
  rw [lintegral_withDensity_eq_lintegral_mul _ hBm hg]
  symm
  calc _ = ∫⁻ x, ∫⁻ s, B x * f (s * x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply]
        exact (lintegral_const_mul _ (hf.comp (measurable_mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, B x * f (s * x) ∂μG ∂μS :=
        lintegral_lintegral_swap
          ((hBm.comp measurable_fst).mul (hf.comp (measurable_snd.mul measurable_fst))).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, B (s⁻¹ * x) * f x ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          lintegral_mul_left_eq_self (μ := μG) (fun x => B (s⁻¹ * x) * f x) s
    _ = ∫⁻ x, ∫⁻ s, B (s⁻¹ * x) * f x ∂μS ∂μG :=
        lintegral_lintegral_swap
          ((hBm.comp (measurable_fst.inv.mul measurable_snd)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, f x ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [show ∫⁻ s, B (s⁻¹ * x) * f x ∂μS = (∫⁻ s, B (s⁻¹ * x) ∂μS) * f x from
          lintegral_mul_const _ (hBm.comp (measurable_inv.mul_const x)), hBinv, one_mul]

end WeilGen

variable {D : D7}

def NV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | Formalism.L2.SG.HidaSetting.InN (X.B.I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat g)}

def StV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  StSet (NV X u v) (NV X u' v) (γ v)

def stCoordV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) : FreeE w → ℂ :=
  fun p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ v)⁻¹ * y * γ v) *ᵥ frm X u' D.host.rdE v p.1.2)

def muStabV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) : Measure (FreeE w → ℂ) :=
  Measure.pi fun _ => ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stCoord_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ y : X.B.I.Ginf) : stCoord X u' w γ y = fun v => stCoordV X u' w γ v (y v) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem muStab_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) :
    muStab X w = Measure.pi fun _ => muStabV X w := rfl

def LocPinAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧
    IsQuotLoc μRv (ν v) ∧ μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w

def LocPin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  LocPinAt X u u' w (νl w)

def LocUni (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w → ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
    IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧ μRv.map (fun s => s⁻¹) = μRv ∧
    μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w ∧
    ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧ (∀ x, b x ≠ ⊤) ∧ ∀ x, ∫⁻ s, b (s * x) ∂μRv = 1

def GlobProd (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∀ μRv : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ v, IsHaarLoc (StV X u u' (gamW X u u' w) v) (μRv v) ∧
        (μRv v).map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w) →
      μR = Measure.pi μRv

/- English proof (translation)
Establish `hI` using `stInv_of_rel X u u' hR`. Establish `key : ∀ w : Point D.host.E (D.R.rS + 1), ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)), OkPt X u u' w → LocPinAt X u u' w ν ∧ ∀ y : ∀ v, X.Vloc u' v, (haveI` using `FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)) (X.tensU u' y) = X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv (ν v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) ( …`. Introduce `w`. Distinguish the cases in `hw : OkPt X u u' w`. Take `⟨μR, hH, hQ, hM⟩` from `hN.2 w hw.1 haveI : SigmaFinite μR := hH.1 choose μRv hHv hIv hMv b hbm hbt hb1 using hLU w hw μR hH hM`.

Establish `hprod : μR = Measure.pi μRv` using `hGP w hw μR hH hM μRv fun v => ⟨hHv v, hMv v⟩`. Use `haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hHv v).1`. Establish `hσ : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v))` using `fun v => SigmaFinite.withDensity_of_ne_top' (hbt v)`. Establish `hBm : Measurable fun x : X.B.I.Ginf => ∏ v, b v (x v)` using `Finset.measurable_prod _ fun v _ => (hbm v).comp (measurable_pi_apply v)`. Establish `hb1G : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, b v ((s * x) v)) ∂μR = 1`.

Introduce `x`. Rewrite using `[hprod]`. Use `lintegral_fintype_prod (μ := μRv) (fun v t => b v (t * x v)) (fun v => (hbm v).comp (measurable_mul_const _))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Conclude with `Finset.prod_eq_one fun v _ => hb1 v (x v)`.

Establish `hinvG : μR.map (fun s => s⁻¹) = μR` using `by haveI : ∀ v, SigmaFinite ((μRv v).map (fun s => s⁻¹)) := fun v => by rw [hIv v]; infer_instance`. Rewrite using `[hprod]`. Use `Measure.pi_map_pi (μ := μRv) (f := fun _ s => s⁻¹) (fun v => measurable_inv.aemeasurable)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `v`. Conclude with `hIv v`. Establish `hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR (Measure.pi fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v))`. Introduce `f hf`. Rewrite using `[pi_withDensity _ b hbm hbt]`.

Conclude with `weil_of_bruhat (Formalism.L2.SG.ProjRows.muInf X.B.I) μR _ hBm hinvG hb1G f hf`. Use `⟨fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v), fun _ => ⟨fun v => ?_, fun y => ?_⟩⟩` and prove the remaining obligations. Use `⟨μRv v, hHv v, fun f hf => ?_, hMv v⟩` and prove the remaining obligations. Conclude with `weil_of_bruhat (Formalism.REAL.muG (X.B.I.ε v)) (μRv v) (b v) (hbm v) (hIv v) (hb1 v) f hf`. Conclude with `oo_eq_tens X u u' _ μR _ _ hH.2.2.1 _ hBm hb1G _ hσ hQ hp (hI w hw) y`.

Conclude with `⟨fun v => Formalism.REAL.muG (X.B.I.ε v), fun h => absurd h hw⟩`. Use `choose νl hνl using key`. Conclude with `⟨νl, fun w hw => (hνl w hw).1, fun w hw hG y => (hνl w ⟨hw, hG⟩).2 y⟩`.
-/
theorem ooQuot_pin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u')
    (hLU : LocUni X u u') (hGP : GlobProd X u u') :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl := by
  have hI := stInv_of_rel X u u' hR
  have key : ∀ w : Point D.host.E (D.R.rS + 1),
      ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)), OkPt X u u' w →
        LocPinAt X u u' w ν ∧ ∀ y : ∀ v, X.Vloc u' v,
          (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
            Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
              (X.tensU u' y) =
          X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (ν v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v)) := by
    intro w
    by_cases hw : OkPt X u u' w
    · obtain ⟨μR, hH, hQ, hM⟩ := hN.2 w hw.1
      haveI : SigmaFinite μR := hH.1
      choose μRv hHv hIv hMv b hbm hbt hb1 using hLU w hw μR hH hM
      have hprod : μR = Measure.pi μRv := hGP w hw μR hH hM μRv fun v => ⟨hHv v, hMv v⟩
      haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hHv v).1
      have hσ : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) :=
        fun v => SigmaFinite.withDensity_of_ne_top' (hbt v)
      have hBm : Measurable fun x : X.B.I.Ginf => ∏ v, b v (x v) :=
        Finset.measurable_prod _ fun v _ => (hbm v).comp (measurable_pi_apply v)
      have hb1G : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, b v ((s * x) v)) ∂μR = 1 := by
        intro x
        rw [hprod]
        have := lintegral_fintype_prod (μ := μRv) (fun v t => b v (t * x v))
          (fun v => (hbm v).comp (measurable_mul_const _))
        refine this.trans ?_
        exact Finset.prod_eq_one fun v _ => hb1 v (x v)
      have hinvG : μR.map (fun s => s⁻¹) = μR := by
        haveI : ∀ v, SigmaFinite ((μRv v).map (fun s => s⁻¹)) := fun v => by rw [hIv v]; infer_instance
        rw [hprod]
        have := Measure.pi_map_pi (μ := μRv) (f := fun _ s => s⁻¹) (fun v => measurable_inv.aemeasurable)
        refine this.trans ?_
        congr 1
        funext v
        exact hIv v
      have hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR
          (Measure.pi fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) := by
        intro f hf
        rw [pi_withDensity _ b hbm hbt]
        exact weil_of_bruhat (Formalism.L2.SG.ProjRows.muInf X.B.I) μR _ hBm hinvG hb1G f hf
      refine ⟨fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v), fun _ => ⟨fun v => ?_, fun y => ?_⟩⟩
      · refine ⟨μRv v, hHv v, fun f hf => ?_, hMv v⟩
        exact weil_of_bruhat (Formalism.REAL.muG (X.B.I.ε v)) (μRv v) (b v) (hbm v) (hIv v) (hb1 v) f hf
      · exact oo_eq_tens X u u' _ μR _ _ hH.2.2.1 _ hBm hb1G _ hσ hQ hp (hI w hw) y
    · exact ⟨fun v => Formalism.REAL.muG (X.B.I.ε v), fun h => absurd h hw⟩
  choose νl hνl using key
  exact ⟨νl, fun w hw => (hνl w hw).1, fun w hw hG y => (hνl w ⟨hw, hG⟩).2 y⟩

end Formalism.L2.SG.Pf.Carrier.JointQuot
