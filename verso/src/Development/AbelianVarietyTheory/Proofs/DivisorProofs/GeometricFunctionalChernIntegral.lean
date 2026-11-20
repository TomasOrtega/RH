import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensityStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.GeoInt

open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

/- English proof (translation)
Establish `B` using `(GlobalTheory.T.firstChern_form_properties k X p D hX σ).1`. Set `f : HermLB.IsomClass p →+ ((hX.atlas σ).Pt → Ev D)` to `AddMonoidHom.mk' (Quotient.lift (s := HermLB.isometrySetoid p) (fun L => c1F hX σ L) (fun L M h => (B L M).2.2.2.2.2 h)) (by`. Introduce `a b`. Proceed by induction on `a using Quotient.inductionOn with | h L => ?_`. Proceed by induction on `b using Quotient.inductionOn with | h M => ?_`.

Conclude with `(B L M).2.2.2.1)`. Establish `hf : ∀ M : HermLB p, f M.icls = c1F hX σ M` using `fun _ => rfl`. Rewrite using `[← hf, icls_comb, map_sum]`. Simplify using `only [map_zsmul, hf]`.
-/
theorem c1F_comb (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) :
    c1F hX σ (comb L n) = ∑ i, n i • c1F hX σ (L i) := by
  have B := (GlobalTheory.T.firstChern_form_properties k X p D hX σ).1
  let f : HermLB.IsomClass p →+ ((hX.atlas σ).Pt → Ev D) :=
    AddMonoidHom.mk' (Quotient.lift (s := HermLB.isometrySetoid p) (fun L => c1F hX σ L)
      (fun L M h => (B L M).2.2.2.2.2 h)) (by
        intro a b
        induction a using Quotient.inductionOn with | h L => ?_
        induction b using Quotient.inductionOn with | h M => ?_
        exact (B L M).2.2.2.1)
  have hf : ∀ M : HermLB p, f M.icls = c1F hX σ M := fun _ => rfl
  rw [← hf, icls_comb, map_sum]
  simp only [map_zsmul, hf]

/- English proof (translation)
The claim follows from `GlobalTheory.T.top_power_hermitian_form_density n H`.
-/
theorem dens_pow_sum (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    dens (((∑ a, ∑ b, H a b • sym (a, b) : Ev n) ^ n : Ev n) : Alt n) =
      (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := GlobalTheory.T.top_power_hermitian_form_density n H

/- English proof (translation)
Rewrite using `[GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]`. Use `congr 1`. Establish `hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) = ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ))`. Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg]`. Simplify using `only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

/- English proof (translation)
Establish `e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b)`. Simplify using `only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[e, dens_pow_sum, Matrix.det_smul, Fintype.card_fin]`. Establish `hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹)`. Rewrite using `[GlobalTheory.HermFrame.kappa]`.

Clear the denominators using the available nonvanishing facts. Establish `h2 : (Complex.I / 2) ^ n ≠ 0` using `pow_ne_zero _ (by simp)`. Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite using `[hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n = (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by`. Rewrite using `[mul_pow]`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Use the proof step `ring, Complex.re_ofReal_mul]`.
-/
theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, dens_pow_sum, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

/- English proof (translation)
Rewrite using `[c1F_comb]`. Simplify using `only [evalF, fld, lin, map_pow, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply]`. Use `congr 2`.
-/
theorem evalF_lin_pow (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ)
    (x : (hX.atlas σ).Pt) :
    evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D) x =
      ((c1F hX σ (comb L n) x ^ D : Ev D) : Alt D) := by
  rw [c1F_comb]
  simp only [evalF, fld, lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply]
  congr 2

/- English proof (translation)
Establish `e` using `(hX.atlas σ).loc_crd (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) (⟨(c, y), hy⟩ : (hX.atlas σ).Pt)`. Use `erw [e, evalF_lin_pow]`. Establish `hs` using `((comb L n).cInf σ).contDiffAt c hy (mem_pick ((comb L n).φ σ).isLB y)`. Use `erw [c1F, dens_ofValues_ddc_pow D _ _ hs]`. Both sides reduce to the same expression.
-/
theorem dens_loc_eq (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ)
    (c : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source) :
    (dens ((hX.atlas σ).loc (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) c (c.e y))).re =
      c.chernDens ((comb L n).φ σ) y := by
  have e := (hX.atlas σ).loc_crd (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D))
    (⟨(c, y), hy⟩ : (hX.atlas σ).Pt)
  erw [e, evalF_lin_pow]
  have hs := ((comb L n).cInf σ).contDiffAt c hy (mem_pick ((comb L n).φ σ).isLB y)
  erw [c1F, dens_ofValues_ddc_pow D _ _ hs]
  rfl

/- English proof (translation)
Unfold `HolAtlas.part Weight.chernPart ChartGlue.glueMeas`. Use `iSup_congr fun c => ?_` and prove the remaining obligations. Unfold `ChartGlue.chartMeas`. Use `congr 1`. Use `withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)` and prove the remaining obligations.

Establish `hy` using `c.e.map_target hv`. Simplify using `only [Function.comp_apply]`. Use `erw [dens_loc_eq hX σ L n c _ hy]`.
-/
theorem part_eq_chernPart (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ)
    (ε : ℤˣ) :
    (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε =
      ((comb L n).φ σ).chernPart D ε := by
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_eq hX σ L n c _ hy]

/- English proof (translation)
Simplify using `only [HolAtlas.integral, Weight.chernInt, part_eq_chernPart, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]`.
-/
theorem integral_eq_chernInt (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) :
    (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) =
      ((comb L n).φ σ).chernInt D Set.univ (fun _ => 1) := by
  simp only [HolAtlas.integral, Weight.chernInt, part_eq_chernPart, Measure.restrict_univ, integral_const,
    smul_eq_mul, mul_one]

/- English proof (translation)
Assume the negation of the conclusion as `hnot`. Take `⟨φ, hφF, hφ⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance`. Establish `hkill : ∀ n : ι → ℤ, φ (lin (fun i => (n i : ℝ)) ^ d) = 0`. Introduce `n`. Establish `hm : lin (fun i => (n i : ℝ)) ^ d ∈ Submodule.span ℝ (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d)` using `Submodule.subset_span ⟨n, rfl⟩`.

Establish `h2 : φ (lin (fun i => (n i : ℝ)) ^ d) ∈ (Submodule.span ℝ (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d)).map φ` using `Submodule.mem_map_of_mem hm`. Rewrite `h2` using `[hφ]`. Conclude with `(Submodule.mem_bot ℝ).mp h2`. Establish `hP : PowLinSpan.polOf φ d = 0`. Use `eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ d) (fun _ => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_` and prove the remaining obligations.

Introduce `x`. Rewrite using `[Finset.card_image_of_injective _ Nat.cast_injective]`. Simplify using `using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ d x)`. Introduce `v hv`. Establish `hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i`.

Introduce `i`. Take `⟨k, -, hk⟩` from `Finset.mem_image.mp (hv i)`. Conclude with `⟨k, hk⟩`. Use `choose k hk using hv'`. Rewrite using `[PowLinSpan.eval_polOf]`.

Establish `h` using `hkill (fun i => (k i : ℤ))`. Establish `he : (∑ x, C (v x) * X x : MvPolynomial ι ℝ) = lin (fun i => (((k i : ℤ)) : ℝ))`. Simplify using `only [lin, Int.cast_natCast, hk]`. Rewrite using `[he]`. Conclude with `h`.

Conclude with `hφF (PowLinSpan.homog_kill φ d hP F hF)`.
-/
theorem mem_span_pow_lin {ι : Type} [Fintype ι] (d : ℕ) (F : MvPolynomial ι ℝ) (hF : F.IsHomogeneous d) :
    F ∈ Submodule.span ℝ (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := by
  by_contra hnot
  obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ n : ι → ℤ, φ (lin (fun i => (n i : ℝ)) ^ d) = 0 := by
    intro n
    have hm : lin (fun i => (n i : ℝ)) ^ d ∈ Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := Submodule.subset_span ⟨n, rfl⟩
    have h2 : φ (lin (fun i => (n i : ℝ)) ^ d) ∈ (Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d)).map φ := Submodule.mem_map_of_mem hm
    rw [hφ] at h2
    exact (Submodule.mem_bot ℝ).mp h2
  have hP : PowLinSpan.polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ d)
      (fun _ => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective _ Nat.cast_injective]
      simpa using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ d x)
    · intro v hv
      have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
        intro i
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
        exact ⟨k, hk⟩
      choose k hk using hv'
      rw [PowLinSpan.eval_polOf]
      have h := hkill (fun i => (k i : ℤ))
      have he : (∑ x, C (v x) * X x : MvPolynomial ι ℝ) = lin (fun i => (((k i : ℤ)) : ℝ)) := by
        simp only [lin, Int.cast_natCast, hk]
      rw [he]
      exact h
  exact hφF (PowLinSpan.homog_kill φ d hP F hF)

section Linear

variable {M : Type} [TopologicalSpace M] {m : ℕ} (A : HolAtlas M m) {ι : Type} (w : ι → A.Pt → Ev m)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[evalF, fld]`.
-/
theorem evalF_add (G₁ G₂ : MvPolynomial ι ℝ) : evalF A w (G₁ + G₂) = evalF A w G₁ + evalF A w G₂ := by
  funext x
  simp [evalF, fld]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]`.
-/
theorem evalF_smul (t : ℝ) (G : MvPolynomial ι ℝ) : evalF A w (t • G) = (t : ℂ) • evalF A w G := by
  funext x
  simp [evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]

end Linear

/- English proof (translation)
Use `haveI := hX.toIsArithVar.compactSpace σ`. Use `haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver`. Use `haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver`. Establish `hform : ∀ G : MvPolynomial ι ℝ, (hX.atlas σ).IsForm (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G)` using `fun G => ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hX.atlas σ)).2.2.2.1 ι _ G (fun i => ((GlobalTheory.T.firstChern_form_properties k X p D hX σ).1 (L i) (L i)).1.1)).1`. Establish `P` using `GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous (CxPts p σ) D (hX.atlas σ)`.

Establish `hint : ∀ G : MvPolynomial ι ℝ, ∀ ε : ℤˣ, Integrable (fun _ => (1 : ℝ)) ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) ε)` using `fun G ε => by haveI := P.1 _ (hform G) ε`. Conclude with `integrable_const _`. Use `⟨fun G₁ G₂ => ?_, fun t G => ?_⟩` and prove the remaining obligations. Rewrite using `[← wInt_one, ← wInt_one, ← wInt_one, evalF_add]`. Conclude with `(P.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2`.

Rewrite using `[← wInt_one, ← wInt_one, evalF_smul]`. Conclude with `P.2.2.1 _ t _ (hform G)`.
-/
theorem integral_lin (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} (L : ι → HermLB p) :
    (∀ G₁ G₂ : MvPolynomial ι ℝ,
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (G₁ + G₂)) =
        (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G₁) +
          (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G₂)) ∧
    ∀ (t : ℝ) (G : MvPolynomial ι ℝ),
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (t • G)) =
        t * (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  haveI := hX.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have hform : ∀ G : MvPolynomial ι ℝ, (hX.atlas σ).IsForm (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) :=
    fun G => ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hX.atlas σ)).2.2.2.1 ι _ G
      (fun i => ((GlobalTheory.T.firstChern_form_properties k X p D hX σ).1 (L i) (L i)).1.1)).1
  have P := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous (CxPts p σ) D (hX.atlas σ)
  have hint : ∀ G : MvPolynomial ι ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) ε) :=
    fun G ε => by
      haveI := P.1 _ (hform G) ε
      exact integrable_const _
  refine ⟨fun G₁ G₂ => ?_, fun t G => ?_⟩
  · rw [← wInt_one, ← wInt_one, ← wInt_one, evalF_add]
    exact (P.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  · rw [← wInt_one, ← wInt_one, evalF_smul]
    exact P.2.2.1 _ t _ (hform G)

/- English proof (translation)
Introduce `k _ X _ p D hX ι _ L Ψ hΨ G hG`. Use `haveI := hX.toIsArithVar.finite_emb`. Establish `hspan` using `mem_span_pow_lin D G hG`. Use `clear hG`. Proceed by induction on `hspan using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨n, rfl⟩` from `hx`. Rewrite using `[hΨ.1 n]`. Unfold `gdeg chInt`. Conclude with `finsum_congr fun σ => (integral_eq_chernInt hX σ L n).symm`.

Consider the case `zero`. Rewrite using `[map_zero]`. Use `(finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm` and prove the remaining obligations. Use `(integral_lin hX σ L).2 0 0` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_mul]`.

Conclude with `this`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, hx, hy, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]`. Conclude with `finsum_congr fun σ => ((integral_lin hX σ L).1 x y).symm`. Consider the case `smul t x _ hx`.

Rewrite using `[map_smul, hx, smul_eq_mul, mul_finsum _ _]`. Conclude with `finsum_congr fun σ => ((integral_lin hX σ L).2 t x).symm`.
-/
theorem geoFun_eq_integral : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    IsGeoFun L D Ψ → ∀ G : MvPolynomial ι ℝ, G.IsHomogeneous D →
      Ψ G = ∑ᶠ σ : k →+* ℂ, (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  intro k _ X _ p D hX ι _ L Ψ hΨ G hG
  haveI := hX.toIsArithVar.finite_emb
  have hspan := mem_span_pow_lin D G hG
  clear hG
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    rw [hΨ.1 n]
    unfold gdeg chInt
    exact finsum_congr fun σ => (integral_eq_chernInt hX σ L n).symm
  | zero =>
    rw [map_zero]
    refine (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    have := (integral_lin hX σ L).2 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun σ => ((integral_lin hX σ L).1 x y).symm
  | smul t x _ hx =>
    rw [map_smul, hx, smul_eq_mul, mul_finsum _ _]
    exact finsum_congr fun σ => ((integral_lin hX σ L).2 t x).symm

end GlobalTheory.LineForm.GeoInt
