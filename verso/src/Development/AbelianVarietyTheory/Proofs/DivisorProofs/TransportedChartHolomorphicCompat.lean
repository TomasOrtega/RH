import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace GlobalTheory.Mean4O.CoverInt
variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem tChart_trans_eq (I : ManIs M Y) {a : Fin (M.n + 1)} (c c' : AlgChart Y.str (I.ε a) e) :
    tChart I c' ∘ (tChart I c).symm = c'.e ∘ c.e.symm := by
  funext v
  simp [tChart]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem ovl_tChart (I : ManIs M Y) {a : Fin (M.n + 1)} (c c' : AlgChart Y.str (I.ε a) e) :
    ReciprocityTheory.L2DbarEstimates.Y.ovl (fun c : AlgChart Y.str (I.ε a) e => tChart I c) c c' =
      c.e.target ∩ c.e.symm ⁻¹' c'.e.source := by
  ext v
  simp [ReciprocityTheory.L2DbarEstimates.Y.ovl, tChart]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tChart_holo_trans (I : ManIs M Y) {a : Fin (M.n + 1)} (c c' : AlgChart Y.str (I.ε a) e) :
    DifferentiableOn ℂ (tChart I c' ∘ (tChart I c).symm)
      (ReciprocityTheory.L2DbarEstimates.Y.ovl (fun c : AlgChart Y.str (I.ε a) e => tChart I c) c c') := by
  rw [tChart_trans_eq, ovl_tChart]
  exact c.holo_trans c'

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem transDet_tChart (I : ManIs M Y) {a : Fin (M.n + 1)} (c c' : AlgChart Y.str (I.ε a) e)
    (x : M.X a) : transDet (tChart I c) (tChart I c') x = transDet c.e c'.e (I.pt a x) := by
  rw [transDet, transDet, tChart_trans_eq, tChart_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem contDiffAt_pot (I : ManIs M Y) {a : Fin (M.n + 1)} {P : LocPot (M.X a)}
    (hP : IsPotential (M.A a) P) (c' : AlgChart Y.str (I.ε a) e) {x : M.X a}
    (hx : I.pt a x ∈ c'.e.source) :
    ContDiffAt ℝ 2 (fun v => P.φ x ((I.pt a).symm (c'.e.symm v))) (c'.e (I.pt a x)) := by
  obtain ⟨j, hj⟩ := (M.A a).cover x
  obtain ⟨c₀, hc₀⟩ := I.alg a j
  let f : Pts Y (I.ε a) → ℝ := P.φ x ∘ (I.pt a).symm
  let S : Set (Pts Y (I.ε a)) := (I.pt a).symm ⁻¹' P.U x ∩ c₀.e.source
  have hS : IsOpen S := ((P.isOpen_U x).preimage (I.pt a).symm.continuous).inter c₀.e.open_source
  have hj₀ : I.pt a x ∈ c₀.e.source := by
    rw [hc₀] at hj
    simpa using hj
  have h₁ : ContDiffOn ℝ ∞ (f ∘ c₀.finChart.symm)
      (c₀.finChart.target ∩ c₀.finChart.symm ⁻¹' ((I.pt a).symm ⁻¹' P.U x)) := by
    have := hP.1 x j
    rw [hc₀] at this
    exact this
  have h₀ : ContDiffOn ℝ ∞ (f ∘ c₀.e.symm) (c₀.e.target ∩ c₀.e.symm ⁻¹' S) :=
    ((c₀.contDiffOn_finChart_iff ∞ _ f).1 h₁).mono fun v hv => ⟨hv.1, hv.2.1⟩
  have hC : ∀ y ∈ S, CInfAt f y := fun y hy => cInfAt_of_chart hS c₀ h₀ hy.2 hy
  have h₂ := contDiffOn_chart hC c'
  have hm : c'.e (I.pt a x) ∈ c'.e.target ∩ c'.e.symm ⁻¹' S :=
    mem_over c'.e hx ⟨by simpa using P.mem_U x, hj₀⟩
  have h₃ : ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e (I.pt a x)) :=
    (h₂.contDiffAt ((isOpen_over c'.e hS).mem_nhds hm)).of_le (by norm_cast)
  exact h₃

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem potDens_trans (I : ManIs M Y) {a : Fin (M.n + 1)} {P : LocPot (M.X a)}
    (hP : IsPotential (M.A a) P) (c c' : AlgChart Y.str (I.ε a) e) {x : M.X a}
    (hx : x ∈ (tChart I c).source) (hx' : x ∈ (tChart I c').source) :
    potDens I P c x = ‖transDet (tChart I c) (tChart I c') x‖ ^ 2 * potDens I P c' x := by
  rw [mem_tChart_source] at hx hx'
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hx hx'
  have ev : (fun v => ((2 * P.φ x ((I.pt a).symm (c.e.symm v)) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e (I.pt a x))]
      (fun v => ((2 * P.φ x ((I.pt a).symm (c'.e.symm v)) : ℝ) : ℂ)) ∘ c'.e ∘ c.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      simp only [Function.comp_apply, c'.e.left_inv hv.2]
  have e₂ : (c'.e ∘ c.e.symm) (c.e (I.pt a x)) = c'.e (I.pt a x) :=
    congrArg c'.e (c.e.left_inv hx)
  have hd : ContDiffAt ℝ 2 (fun v => ((2 * P.φ x ((I.pt a).symm (c'.e.symm v)) : ℝ) : ℂ))
      ((c'.e ∘ c.e.symm) (c.e (I.pt a x))) := by
    rw [e₂]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_const.mul (contDiffAt_pot I hP c' hx'))
  rw [potDens, potDens, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ev,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (c.holo_trans c') hd, e₂, Complex.re_ofReal_mul,
    transDet_tChart, transDet]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem potDens_chartRule : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (P : LocPot (M.X a)), IsPotential (M.A a) P → (∀ c c' : AlgChart Y.str (I.ε a) e, DifferentiableOn ℂ (tChart I c' ∘ (tChart I c).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl (fun c : AlgChart Y.str (I.ε a) e => tChart I c) c c')) ∧ ∀ (c c' : AlgChart Y.str (I.ε a) e) (x : M.X a), x ∈ (tChart I c).source → x ∈ (tChart I c').source → potDens I P c x = ‖GlobalTheory.ChartGlue.transDet (tChart I c) (tChart I c') x‖ ^ 2 * potDens I P c' x := by
  intro F _ _ Y e M I a P hP
  exact ⟨fun c c' => tChart_holo_trans I c c', fun c c' x hx hx' => potDens_trans I hP c c' hx hx'⟩

end GlobalTheory.Mean4O.CoverInt
