import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section
namespace GlobalTheory.FibDensMass

section Curry
variable {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type}
  [∀ i j, MeasurableSpace (Y i j)]

/- English proof (translation)
Use `⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩` and prove the remaining obligations. Use `symm`. Use `Measure.pi_eq_generateFrom (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s}) (fun i => generateFrom_pi) (fun i => isPiSystem_pi) (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_` and prove the remaining obligations. Use `choose S hS hSs using hs`. Establish `hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) = Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2`.

Use extensionality with `f`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]`. Both sides reduce to the same expression. Rewrite using `[Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by`. Rewrite using `[← hSs i]`.

Conclude with `MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,`. Use the proof step `Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hSs i, Measure.pi_pi]`.
-/
theorem measurePreserving_curry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  refine ⟨(MeasurableEquiv.piCurry Y).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.univ.pi '' Set.univ.pi fun j => {s : Set (Y i j) | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun j => (μ i j).toFiniteSpanningSetsIn) fun s hs => ?_
  choose S hS hSs using hs
  have hpre : (MeasurableEquiv.piCurry Y) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun p : (i : ι) × κ i => S p.1 p.2 := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hSs, MeasurableEquiv.piCurry_apply, Sigma.forall]
    rfl
  rw [Measure.map_apply (MeasurableEquiv.piCurry Y).measurable (MeasurableSet.univ_pi fun i => by
      rw [← hSs i]; exact MeasurableSet.univ_pi fun j => hS i j (Set.mem_univ j)), hpre, Measure.pi_pi,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hSs i, Measure.pi_pi]

end Curry

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]`. Use `lintegral_congr fun a => ?_` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_succ]`. Both sides reduce to the same expression. Conclude with `Finset.aemeasurable_fun_prod _ fun i _ => (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)`.
-/
theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

/- English proof (translation)
Set `e` to `(Fintype.equivFin ι).symm`. Rewrite using `[← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`. Repeatedly rewrite using `[← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]`. Conclude with `lintegral_fin_prod fun i => hf _`.
-/
theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod fun i => hf _

/- English proof (translation)
Establish `hAt : Aᵀ.PosDef` using `hA.transpose`. Establish `hd : 0 < A.det.re` using `(GlobalTheory.FlagFibre.FlagInt.re_facts hA).1`. Establish `hc` using `GlobalTheory.TrueCx.flagConst_pos s`. Establish `hk : 0 ≤ GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1)` using `by positivity`. Repeatedly rewrite using `[ENNReal.ofReal_mul hk]`.

Rewrite using `[lintegral_const_mul _ (GlobalTheory.FlagFibre.measurable_dens _).ennreal_ofReal, GlobalTheory.FlagFibre.FlagInt.lintegral_dens s Aᵀ hAt, Matrix.det_transpose, ← ENNReal.ofReal_mul hk]`. Rewrite using `[← ENNReal.ofReal_one]`. Use `congr 1`. Establish `: A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ)) = 1`. Rewrite using `[← zpow_add₀ hd.ne']`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem block_mass (s : ℕ) (A : Matrix (Fin s) (Fin s) ℂ) (hA : A.PosDef) :
    ∫⁻ w : Low s → ℂ, ENNReal.ofReal (GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens Aᵀ w) = 1 := by
  have hAt : Aᵀ.PosDef := hA.transpose
  have hd : 0 < A.det.re := (GlobalTheory.FlagFibre.FlagInt.re_facts hA).1
  have hc := GlobalTheory.TrueCx.flagConst_pos s
  have hk : 0 ≤ GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) := by positivity
  simp_rw [ENNReal.ofReal_mul hk]
  rw [lintegral_const_mul _ (GlobalTheory.FlagFibre.measurable_dens _).ennreal_ofReal,
    GlobalTheory.FlagFibre.FlagInt.lintegral_dens s Aᵀ hAt, Matrix.det_transpose, ← ENNReal.ofReal_mul hk]
  rw [← ENNReal.ofReal_one]
  congr 1
  have : A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ)) = 1 := by
    rw [← zpow_add₀ hd.ne']; simp
  calc GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) * (A.det.re ^ (1 - (s : ℤ)) / GlobalTheory.TrueCx.flagConst s)
        = (A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ))) * (GlobalTheory.TrueCx.flagConst s / GlobalTheory.TrueCx.flagConst s) := by ring
    _ = 1 := by rw [this, div_self hc.ne', one_mul]

end GlobalTheory.FibDensMass

open GlobalTheory.FibDensMass in
/- English proof (translation)
Introduce `ι _ m G hG`. Establish `hnn : ∀ τ (w : Low (m τ) → ℂ), 0 ≤ GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ w` using `fun τ w => mul_nonneg (mul_nonneg (GlobalTheory.TrueCx.flagConst_pos _).le (zpow_nonneg (GlobalTheory.FlagFibre.FlagInt.re_facts (hG τ)).1.le _)) (GlobalTheory.FlagFibre.dens_nonneg _ _)`. Use `⟨fun y => Finset.prod_nonneg fun τ _ => hnn τ _, ?_⟩` and prove the remaining obligations. Establish `hmp` using `measurePreserving_curry (Y := fun (τ : ι) (_ : Low (m τ)) => ℂ) (fun _ _ => (volume : Measure ℂ))`. Set `g : ∀ τ, (Low (m τ) → ℂ) → ℝ≥0∞` to `fun τ w => ENNReal.ofReal (GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ w)`.

Establish `hpt : ∀ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = ∏ τ, g τ (MeasurableEquiv.piCurry (fun (τ : ι) (_ : Low (m τ)) => ℂ) y τ)`. Introduce `y`. Simplify using `only [fibDens, g]`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg fun τ _ => hnn τ _]`. Both sides reduce to the same expression.

Repeatedly rewrite using `[hpt]`. Rewrite using `[show (volume : Measure (Cell m → ℂ)) = Measure.pi fun p : Cell m => (volume : Measure ℂ) from rfl, hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun z => ∏ τ, g τ (z τ))]`. Rewrite using `[lintegral_fintype_prod (μ := fun τ => Measure.pi fun _ : Low (m τ) => (volume : Measure ℂ)) fun τ => ((GlobalTheory.FlagFibre.measurable_dens _).const_mul _).ennreal_ofReal.aemeasurable]`. Conclude with `Finset.prod_eq_one fun τ _ => block_mass (m τ) (G τ) (hG τ)`.
-/
theorem GlobalTheory.FlagCell2.fibDens_mass : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (G : Mat m ℂ), (∀ τ, (G τ).PosDef) → (∀ y, 0 ≤ fibDens G y) ∧ ∫⁻ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = 1 := by
  intro ι _ m G hG
  have hnn : ∀ τ (w : Low (m τ) → ℂ), 0 ≤ GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens (G τ)ᵀ w := fun τ w =>
    mul_nonneg (mul_nonneg (GlobalTheory.TrueCx.flagConst_pos _).le
      (zpow_nonneg (GlobalTheory.FlagFibre.FlagInt.re_facts (hG τ)).1.le _)) (GlobalTheory.FlagFibre.dens_nonneg _ _)
  refine ⟨fun y => Finset.prod_nonneg fun τ _ => hnn τ _, ?_⟩
  have hmp := measurePreserving_curry (Y := fun (τ : ι) (_ : Low (m τ)) => ℂ) (fun _ _ => (volume : Measure ℂ))
  let g : ∀ τ, (Low (m τ) → ℂ) → ℝ≥0∞ := fun τ w => ENNReal.ofReal (GlobalTheory.TrueCx.flagConst (m τ) *
    (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ w)
  have hpt : ∀ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = ∏ τ, g τ (MeasurableEquiv.piCurry (fun (τ : ι) (_ : Low (m τ)) => ℂ) y τ) := by
    intro y
    simp only [fibDens, g]
    rw [ENNReal.ofReal_prod_of_nonneg fun τ _ => hnn τ _]
    rfl
  simp_rw [hpt]
  rw [show (volume : Measure (Cell m → ℂ)) = Measure.pi fun p : Cell m => (volume : Measure ℂ) from rfl,
    hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun z => ∏ τ, g τ (z τ))]
  rw [lintegral_fintype_prod (μ := fun τ => Measure.pi fun _ : Low (m τ) => (volume : Measure ℂ))
    fun τ => ((GlobalTheory.FlagFibre.measurable_dens _).const_mul _).ennreal_ofReal.aemeasurable]
  exact Finset.prod_eq_one fun τ _ => block_mass (m τ) (G τ) (hG τ)
