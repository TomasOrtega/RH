import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticOrbitOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOneStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib

/- English proof (translation)
Rewrite using `[mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_add]`. Normalize the expressions using the abelian group laws.
-/
theorem shear_mul {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s t : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca t) =
      1 + Matrix.single cb ca (s + t) := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hne,
    Matrix.single_add]
  abel

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hstep hca hcb k₀ hk₀ RW q h0 h1 f hf Un Gn ΦYn ΦWn l H bp hUn hD z hz hne`. Establish `hPos` using `GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hstep hca hcb RW.X q Un Gn ΦYn ΦWn l H bp hUn hD _ hz`. Take `⟨-, -, -, hbase, hG, hex, hq⟩` from `hD`. Establish `hπ` using `GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty`. Take `⟨hq0, hq1⟩` from `hq z hz`.

Generalize the expression as in `hw : Fin.tail (Fin.tail z) = w at hz hPos hq0 ⊢`. Take `⟨hbO, hH⟩` from `hbase w hz`. Establish `hcab : ca ≠ cb` using `fun e => by`. Establish `: (ca : ℕ) = cb` using `congrArg Fin.val e`. Use linear arithmetic over natural numbers and integers.

Establish `shear` using `fun s : ℂ => GlobalTheory.T.elementary_factor_properties N j a b ca cb s M.j_le hb hstep hca hcb`. Establish `hflag : ∀ (s : ℂ) (τ' : Ψ), IsBlockDiag j (flagAt H τ ca cb s w τ') ∧ (flagAt H τ ca cb s w τ').det ≠ 0`. Introduce `s τ'`. Unfold `flagAt`. Use `split_ifs with e`.

Use `⟨(hH τ).1.mul (shear s).1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, (shear s).2.1, mul_one]`. Conclude with `(hH τ).2`. Conclude with `hH τ'`. Take `⟨x₀, hx₀⟩` from `hπ.2 (q 0 (ΦWn z))`.

Take `⟨x₁, hx₁⟩` from `hπ.2 (q 1 (ΦWn z))`. Establish `t0 : Fin.tail (Fin.cons (z 0) w : Fin (d + 1) → ℂ) = w` using `Fin.tail_cons _ _`. Take `⟨z₀, o0, b0, ex0⟩` from `hex (Fin.cons (z 0) w) (by rw [t0]; exact hz) x₀ (hx₀.trans hq0)`. Take `⟨z₁, o1, b1, ex1⟩` from `hex (Fin.tail z) (by rw [hw]; exact hz) x₁ (hx₁.trans hq1)`. Rewrite `b0`, `ex0` using `[t0]`.

Rewrite `b1`, `ex1` using `[hw]`. Establish `c0 : (Fin.cons (z 0) w : Fin (d + 1) → ℂ) 0 = z 0` using `rfl`. Establish `c1 : (Fin.tail z : Fin (d + 1) → ℂ) 0 = z 1` using `rfl`. Rewrite `ex0` using `[c0]`. Rewrite `ex1` using `[c1]`.

Establish `L0 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (q 0 (ΦWn z)) = potAt BM l p (bp w) (flagAt H τ ca cb (z 0) w p.1)` using `fun p => by`. Rewrite using `[← hx₀]`. Conclude with `GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ z₀ (bp w) p _ hbO o0 b0 (ex0 p.1 p.2) (hflag _ _).1 (hflag _ _).2`. Establish `L1 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₁) + FA.S.ph (some p) (q 1 (ΦWn z)) = potAt BM l p (bp w) (flagAt H τ ca cb (z 1) w p.1)` using `fun p => by`. Rewrite using `[← hx₁]`.

Conclude with `GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₁ z₁ (bp w) p _ hbO o1 b1 (ex1 p.1 p.2) (hflag _ _).1 (hflag _ _).2`. Establish `S : ∀ s : ℂ, ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp w) (flagAt H τ ca cb s w p.1) = xiPot (Gn w) s - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))` using `fun s => GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp w)) (fun τ' => H τ' w) (fun p => upsLogAt BM l p (bp w)) s (Gn w) M.j_le hb hstep hca hcb (BM.G_pos l τ _ hbO).1 (BM.G_pos l τ _ hbO).2 (hH τ).1 (hH τ).2 (hG w hz)`. Establish `ht : z 1 - z 0 ≠ 0` using `sub_ne_zero.2 fun e => hne e.symm`. Establish `hz0 : ∀ i, M.ExactAt (BM.F l) (τ, i) z₀ (H τ w * (1 + Matrix.single cb ca (z 0)))` using `fun i => by`. Use `ex0 τ i` as an intermediate fact.

Rewrite `this` using `[flagAt, if_pos rfl]`. Then use the resulting hypothesis. Establish `hz1 : ∀ i, M.ExactAt (BM.F l) (τ, i) z₁ (H τ w * (1 + Matrix.single cb ca (z 0)) * (1 + Matrix.single cb ca (z 1 - z 0)))` using `fun i => by`. Use `ex1 τ i` as an intermediate fact. Rewrite `this` using `[flagAt, if_pos rfl, show z 1 = z 0 + (z 1 - z 0) by ring, ← shear_mul hcab, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₀))`.

Rewrite using `[CovMap.mCoordIdeal_eq_of_sameOrbit b0]`. Conclude with `BM.good l _ hbO.1`. Establish `hfx` using `hf (ΦWn z) z₀ z₁ (BM.F l) (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) (BM.isFrame l) hgood (orbit_trans (orbit_symm o0) (h0 _ x₀ hx₀)) (orbit_trans (orbit_symm o1) (h1 _ x₁ hx₁)) ((hH τ).1.mul (shear _).1) (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2) …`. Establish `hval : ∀ i, ¬ IsProperStep N j i → valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀) = upsVal BM l (τ, i) (bp w)`. Introduce `i _`.

Conclude with `(GlobalTheory.T.value_constant_on_orbit _ _ M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _)) (orbit_symm b0)).symm`. Establish `hfac : ∀ i, facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i = facOf N j a (H τ w) i` using `(shear (z 0)).2.2.1 (H τ w)`. Establish `hlog` using `GlobalTheory.T.log_norm_product_formula N (IsProperStep N j) (z 1 - z 0) (fun i => valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)) (fun i => facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i) (fun i => xiCoef τ a (τ, i)) ht (fun i hi => by`. Use `⟨?_, GlobalTheory.T.step_factor_ne_zero N j a i _ ((hH τ).1.mul (shear _).1) (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2)⟩` and prove the remaining obligations. Rewrite using `[hval i hi]`.

Conclude with `GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) (bp w) hbO.1 ((M.blk_none _).2 hi))`. Establish `hC : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ + Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) = ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then …`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Distinguish the cases in `hp : IsProperStep N j i`.

Establish `hn : M.blk (τ, i) ≠ none` using `fun e => (M.blk_none _).1 e hp`. Simplify using `[hp, upsLogAt, hn]`. Establish `hn : M.blk (τ, i) = none` using `(M.blk_none _).2 hp`. Simplify using `only [hp, if_false, upsLogAt, hn, if_true, hval i hp, hfac i]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsin` using `GlobalTheory.T.log_sine_formula (Gn w) (z 0) (z 1) hPos hne`. Establish `hL : normRhs M τ a (BM.F l) z₀ z₁ (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) - (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) = Real.log ‖z 1 - z 0‖ + ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperSt …`. Unfold `normRhs`. Rewrite using `[add_sub_cancel_right]`. Conclude with `hlog`.

Establish `T : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) + ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) = (xiPot (Gn w) (z 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if …`. Rewrite using `[← S (z 0), ← S (z 1), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `e0 : (FA.S.comap some).ph p (q 0 (ΦWn z)) = FA.S.ph (some p) (q 0 (ΦWn z))` using `rfl`. Establish `e1 : (FA.S.comap some).ph p (q 1 (ΦWn z)) = FA.S.ph (some p) (q 1 (ΦWn z))` using `rfl`.

Rewrite using `[e0, e1, ← L0 p, ← L1 p]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfx, hsin]`. Rewrite `hL` using `[hC]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logNorm_add_weights_eq_logSin : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hstep hca hcb k₀ hk₀ RW q h0 h1 f hf Un Gn ΦYn ΦWn l H bp hUn hD z hz hne
  have hPos := GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hstep hca hcb RW.X q Un Gn ΦYn ΦWn l H bp hUn hD _ hz
  obtain ⟨-, -, -, hbase, hG, hex, hq⟩ := hD
  have hπ := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨hq0, hq1⟩ := hq z hz
  generalize hw : Fin.tail (Fin.tail z) = w at hz hPos hq0 ⊢
  obtain ⟨hbO, hH⟩ := hbase w hz
  have hcab : ca ≠ cb := fun e => by
    have : (ca : ℕ) = cb := congrArg Fin.val e
    omega
  have shear := fun s : ℂ => GlobalTheory.T.elementary_factor_properties N j a b ca cb s M.j_le hb hstep hca hcb
  have hflag : ∀ (s : ℂ) (τ' : Ψ), IsBlockDiag j (flagAt H τ ca cb s w τ') ∧ (flagAt H τ ca cb s w τ').det ≠ 0 := by
    intro s τ'
    unfold flagAt
    split_ifs with e
    · refine ⟨(hH τ).1.mul (shear s).1, ?_⟩
      rw [Matrix.det_mul, (shear s).2.1, mul_one]
      exact (hH τ).2
    · exact hH τ'
  obtain ⟨x₀, hx₀⟩ := hπ.2 (q 0 (ΦWn z))
  obtain ⟨x₁, hx₁⟩ := hπ.2 (q 1 (ΦWn z))
  have t0 : Fin.tail (Fin.cons (z 0) w : Fin (d + 1) → ℂ) = w := Fin.tail_cons _ _
  obtain ⟨z₀, o0, b0, ex0⟩ := hex (Fin.cons (z 0) w) (by rw [t0]; exact hz) x₀ (hx₀.trans hq0)
  obtain ⟨z₁, o1, b1, ex1⟩ := hex (Fin.tail z) (by rw [hw]; exact hz) x₁ (hx₁.trans hq1)
  rw [t0] at b0 ex0
  rw [hw] at b1 ex1
  have c0 : (Fin.cons (z 0) w : Fin (d + 1) → ℂ) 0 = z 0 := rfl
  have c1 : (Fin.tail z : Fin (d + 1) → ℂ) 0 = z 1 := rfl
  rw [c0] at ex0
  rw [c1] at ex1

  have L0 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (q 0 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 0) w p.1) := fun p => by
    rw [← hx₀]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ z₀ (bp w) p _ hbO o0 b0 (ex0 p.1 p.2) (hflag _ _).1 (hflag _ _).2
  have L1 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₁) + FA.S.ph (some p) (q 1 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 1) w p.1) := fun p => by
    rw [← hx₁]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₁ z₁ (bp w) p _ hbO o1 b1 (ex1 p.1 p.2) (hflag _ _).1 (hflag _ _).2

  have S : ∀ s : ℂ, ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp w) (flagAt H τ ca cb s w p.1) =
      xiPot (Gn w) s - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := fun s =>
    GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp w)) (fun τ' => H τ' w)
      (fun p => upsLogAt BM l p (bp w)) s (Gn w) M.j_le hb hstep hca hcb (BM.G_pos l τ _ hbO).1
      (BM.G_pos l τ _ hbO).2 (hH τ).1 (hH τ).2 (hG w hz)

  have ht : z 1 - z 0 ≠ 0 := sub_ne_zero.2 fun e => hne e.symm
  have hz0 : ∀ i, M.ExactAt (BM.F l) (τ, i) z₀ (H τ w * (1 + Matrix.single cb ca (z 0))) := fun i => by
    have := ex0 τ i
    rwa [flagAt, if_pos rfl] at this
  have hz1 : ∀ i, M.ExactAt (BM.F l) (τ, i) z₁ (H τ w * (1 + Matrix.single cb ca (z 0)) *
      (1 + Matrix.single cb ca (z 1 - z 0))) := fun i => by
    have := ex1 τ i
    rwa [flagAt, if_pos rfl, show z 1 = z 0 + (z 1 - z 0) by ring, ← shear_mul hcab, ← Matrix.mul_assoc] at this
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₀)) := by
    rw [CovMap.mCoordIdeal_eq_of_sameOrbit b0]
    exact BM.good l _ hbO.1
  have hfx := hf (ΦWn z) z₀ z₁ (BM.F l) (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) (BM.isFrame l) hgood
    (orbit_trans (orbit_symm o0) (h0 _ x₀ hx₀)) (orbit_trans (orbit_symm o1) (h1 _ x₁ hx₁))
    ((hH τ).1.mul (shear _).1) (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2) ht hz0 hz1

  have hval : ∀ i, ¬ IsProperStep N j i → valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀) = upsVal BM l (τ, i) (bp w) := by
    intro i _
    exact (GlobalTheory.T.value_constant_on_orbit _ _ M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _)) (orbit_symm b0)).symm
  have hfac : ∀ i, facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i = facOf N j a (H τ w) i :=
    (shear (z 0)).2.2.1 (H τ w)
  have hlog := GlobalTheory.T.log_norm_product_formula N (IsProperStep N j) (z 1 - z 0)
    (fun i => valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀))
    (fun i => facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i) (fun i => xiCoef τ a (τ, i)) ht
    (fun i hi => by
      refine ⟨?_, GlobalTheory.T.step_factor_ne_zero N j a i _ ((hH τ).1.mul (shear _).1)
        (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2)⟩
      rw [hval i hi]
      exact GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) (bp w) hbO.1 ((M.blk_none _).2 hi))
  have hC : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    by_cases hp : IsProperStep N j i
    · have hn : M.blk (τ, i) ≠ none := fun e => (M.blk_none _).1 e hp
      simp [hp, upsLogAt, hn]
    · have hn : M.blk (τ, i) = none := (M.blk_none _).2 hp
      simp only [hp, if_false, upsLogAt, hn, if_true, hval i hp, hfac i]
      ring
  have hsin := GlobalTheory.T.log_sine_formula (Gn w) (z 0) (z 1) hPos hne
  have hL : normRhs M τ a (BM.F l) z₀ z₁ (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) -
      (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      Real.log ‖z 1 - z 0‖ + ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) := by
    unfold normRhs
    rw [add_sub_cancel_right]
    exact hlog
  have T : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) +
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      (xiPot (Gn w) (z 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) +
      (xiPot (Gn w) (z 1) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) := by
    rw [← S (z 0), ← S (z 1), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e0 : (FA.S.comap some).ph p (q 0 (ΦWn z)) = FA.S.ph (some p) (q 0 (ΦWn z)) := rfl
    have e1 : (FA.S.comap some).ph p (q 1 (ΦWn z)) = FA.S.ph (some p) (q 1 (ΦWn z)) := rfl
    rw [e0, e1, ← L0 p, ← L1 p]
    ring
  rw [hfx, hsin]
  rw [hC] at hL
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib
