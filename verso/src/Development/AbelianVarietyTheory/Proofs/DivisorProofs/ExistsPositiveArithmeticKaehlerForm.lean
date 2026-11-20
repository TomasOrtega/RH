import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianPosDefOfChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionChartInjectiveDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormConjSwapStatement
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.BaseKaehler
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points
open scoped ComplexConjugate

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `h1 : a'.castAdd n ∈ ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n)))` using `e ▸ by simp`. Establish `h2 : b'.natAdd n ∈ ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n)))` using `e ▸ by simp`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h1 h2`.

Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Use `a'.isLt` as an intermediate fact. Use `b'.isLt` as an intermediate fact. Apply the tactic sequence `constructor <;> apply Fin.ext <;> omega`.

Introduce and unpack `⟨rfl, rfl⟩`. Both sides reduce to the same expression.
-/
theorem pair_eq_iff {n : ℕ} (a b a' b' : Fin n) :
    ({a'.castAdd n, b'.natAdd n} : Finset (Fin (n + n))) = {a.castAdd n, b.natAdd n} ↔ a' = a ∧ b' = b := by
  constructor
  · intro e
    have h1 : a'.castAdd n ∈ ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))) := e ▸ by simp
    have h2 : b'.natAdd n ∈ ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))) := e ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h1 h2
    have := a.isLt; have := b.isLt; have := a'.isLt; have := b'.isLt
    constructor <;> apply Fin.ext <;> omega
  · rintro ⟨rfl, rfl⟩; rfl

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[GlobalTheory.ChernPull.coe_matForm]`. Simplify using `only [hermMat, of_apply, Matrix.smul_apply, smul_eq_mul, ← bas_pair, map_smul, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, pair_eq_iff, smul_eq_mul]`. Simplify using `only [mul_one, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, HermFrame.kappa]`. Establish `: (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_pos.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Simplify using `[Complex.I_sq]`. Rewrite using `[Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]`.

Simplify using the standard rewrite rules.
-/
theorem hermMat_matForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    hermMat (matForm n H : Alt n) = ((2 * Real.pi : ℝ)⁻¹ : ℂ) • H := by
  ext a b
  rw [GlobalTheory.ChernPull.coe_matForm]
  simp only [hermMat, of_apply, Matrix.smul_apply, smul_eq_mul, ← bas_pair, map_smul, map_sum,
    Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
    pair_eq_iff, smul_eq_mul]
  simp only [mul_one, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    HermFrame.kappa]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
  simp

/- English proof (translation)
Take `⟨⟨c, y⟩, hy⟩` from `x`. Take `⟨c0, h0⟩` from `AlgChart.exists_mem_source (p := PSpace.str k N) (σ := σ) (D := N) (PtsOver.map i hip (spMap σ) y)`. Use `set L := (ProjSpace.hermitianTwistingSheaf k N).pull i hip`. Establish `hp` using `mem_pick (L.φ σ).isLB y`. Express the relevant statement in the definitionally equal form `(hermMat (c1F h σ L ⟨(c, y), hy⟩ : Alt D)).PosDef`.

Rewrite using `[c1F_eq_matForm_hessL h L hy, hermMat_matForm]`. Simplify using `only [hessL]`. Rewrite using `[GlobalTheory.ChernPull.hess_pull i hip σ c c0 y hy h0 _ _ hp]`. Use `set P : Matrix (Fin D) (Fin N) ℂ := of fun j b => (fderiv ℂ (c0.e ∘ PtsOver.map i hip (spMap σ) ∘ c.e.symm) (c.e y) (GlobalTheory.GoodMetric.coordVec j)).ofLp b with hP`. Establish `hPH : (of fun a l => conj ((fderiv ℂ (c0.e ∘ PtsOver.map i hip (spMap σ) ∘ c.e.symm) (c.e y) (GlobalTheory.GoodMetric.coordVec l)).ofLp a)) = Pᴴ`.

Use extensionality with `a l`. Simplify using `[hP, conjTranspose_apply]`. Rewrite using `[hPH]`. Establish `hK` using `GlobalTheory.T.fubiniStudy_hessian_posDef_of_chart k N σ c0 _ h0 _ (mem_of_mem_linComb (m := fun _ => PtsOver.map i hip (spMap σ) y) (fun _ => rfl) hp PUnit.unit)`. Establish `hF` using `GlobalTheory.T.closed_immersion_chart_injective_derivative k X (PSpace k N) p (PSpace.str k N) D N i hi hip σ c c0 y hy h0`.

Use `PosDef.smul (hK.mul_mul_conjTranspose_same ?_) (by` and prove the remaining obligations. Use `Real.pi_pos` as an intermediate fact. Rewrite using `[← Complex.ofReal_inv]`. Conclude with `Complex.zero_lt_real.2 (by positivity))`. Introduce `u v huv`.

Establish `key : ∀ u : Fin D → ℂ, u ᵥ* P = (fderiv ℂ (c0.e ∘ PtsOver.map i hip (spMap σ) ∘ c.e.symm) (c.e y) (∑ j, u j • GlobalTheory.GoodMetric.coordVec j)).ofLp`. Introduce `u`. Use extensionality with `b`. Simplify using `[vecMul, dotProduct, hP, map_sum, map_smul]`. Express the relevant statement in the definitionally equal form `u ᵥ* P = v ᵥ* P at huv`.

Rewrite `huv` using `[key, key]`. Use `hF (WithLp.ofLp_injective _ huv)` as an intermediate fact. Use function extensionality and compare the values at `j`. Use `congrArg (fun w : V D => w.ofLp j) this` as an intermediate fact. Simplify `this` using `[GlobalTheory.GoodMetric.coordVec, Finset.sum_apply, Pi.single_apply]`.
-/
theorem hermMat_c1F_posDef {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D)
    {N : ℕ} (i : X ⟶ PSpace k N) (hi : IsClosedImmersion i) (hip : i ≫ PSpace.str k N = p) (σ : k →+* ℂ)
    (x : (h.atlas σ).Pt) : (hermMat (fld _ (c1F h σ ((ProjSpace.hermitianTwistingSheaf k N).pull i hip)) x)).PosDef := by
  obtain ⟨⟨c, y⟩, hy⟩ := x
  obtain ⟨c0, h0⟩ := AlgChart.exists_mem_source (p := PSpace.str k N) (σ := σ) (D := N) (PtsOver.map i hip (spMap σ) y)
  set L := (ProjSpace.hermitianTwistingSheaf k N).pull i hip
  have hp := mem_pick (L.φ σ).isLB y
  change (hermMat (c1F h σ L ⟨(c, y), hy⟩ : Alt D)).PosDef
  rw [c1F_eq_matForm_hessL h L hy, hermMat_matForm]
  simp only [hessL]
  rw [GlobalTheory.ChernPull.hess_pull i hip σ c c0 y hy h0 _ _ hp]
  set P : Matrix (Fin D) (Fin N) ℂ := of fun j b =>
    (fderiv ℂ (c0.e ∘ PtsOver.map i hip (spMap σ) ∘ c.e.symm) (c.e y) (GlobalTheory.GoodMetric.coordVec j)).ofLp b with hP
  have hPH : (of fun a l => conj ((fderiv ℂ (c0.e ∘ PtsOver.map i hip (spMap σ) ∘ c.e.symm) (c.e y)
      (GlobalTheory.GoodMetric.coordVec l)).ofLp a)) = Pᴴ := by
    ext a l; simp [hP, conjTranspose_apply]
  rw [hPH]
  have hK := GlobalTheory.T.fubiniStudy_hessian_posDef_of_chart k N σ c0 _ h0 _ (mem_of_mem_linComb (m := fun _ => PtsOver.map i hip (spMap σ) y) (fun _ => rfl) hp PUnit.unit)
  have hF := GlobalTheory.T.closed_immersion_chart_injective_derivative k X (PSpace k N) p (PSpace.str k N) D N i hi hip σ c c0 y hy h0
  refine PosDef.smul (hK.mul_mul_conjTranspose_same ?_) (by
    have := Real.pi_pos
    rw [← Complex.ofReal_inv]
    exact Complex.zero_lt_real.2 (by positivity))
  intro u v huv
  have key : ∀ u : Fin D → ℂ, u ᵥ* P = (fderiv ℂ (c0.e ∘ PtsOver.map i hip (spMap σ) ∘ c.e.symm) (c.e y)
      (∑ j, u j • GlobalTheory.GoodMetric.coordVec j)).ofLp := by
    intro u; ext b
    simp [vecMul, dotProduct, hP, map_sum, map_smul]
  change u ᵥ* P = v ᵥ* P at huv
  rw [key, key] at huv
  have := hF (WithLp.ofLp_injective _ huv)
  funext j
  have := congrArg (fun w : V D => w.ofLp j) this
  simpa [GlobalTheory.GoodMetric.coordVec, Finset.sum_apply, Pi.single_apply] using this

/- English proof (translation)
Introduce `k _ S p D h`. Use `haveI : IsIntegral S := h.isIntegral`. Take `⟨N, i, hi, hip⟩` from `h.isProjOver`. Use `set L : HermLB p := (ProjSpace.hermitianTwistingSheaf k N).pull i hip`. Establish `hc` using `fun σ => GlobalTheory.T.firstChern_real_closed k S p D h σ L`.

Use `⟨fun σ => fld _ (c1F h σ L), ⟨fun σ => (hc σ).1, fun σ σ' x x' e hx => GlobalTheory.T.chern_form_conj_swap k S p D h L σ σ' x x' e hx⟩, fun σ => ⟨(hc σ).2.1, (hc σ).2.2, fun x => hermMat_c1F_posDef h i hi hip σ x⟩⟩` and prove the remaining obligations.
-/
theorem exists_kaehler : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D),
    ∃ κ : h.Fld, h.IsArForm 1 κ ∧ ∀ σ, (h.atlas σ).del (κ σ) = 0 ∧ (h.atlas σ).dbar (κ σ) = 0 ∧
      ∀ x, (hermMat (κ σ x)).PosDef := by
  intro k _ S p D h
  haveI : IsIntegral S := h.isIntegral
  obtain ⟨N, i, hi, hip⟩ := h.isProjOver
  set L : HermLB p := (ProjSpace.hermitianTwistingSheaf k N).pull i hip
  have hc := fun σ => GlobalTheory.T.firstChern_real_closed k S p D h σ L
  refine ⟨fun σ => fld _ (c1F h σ L), ⟨fun σ => (hc σ).1, fun σ σ' x x' e hx => GlobalTheory.T.chern_form_conj_swap k S p D h L σ σ' x x' e hx⟩,
    fun σ => ⟨(hc σ).2.1, (hc σ).2.2, fun x => hermMat_c1F_posDef h i hi hip σ x⟩⟩
end GlobalTheory.BaseKaehler
