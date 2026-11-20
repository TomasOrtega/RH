import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerPoint
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyDelta
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.per_int

/- English proof (translation)
The claim follows from `((potSmoothOn A th hth x k).mono fun _ hy => ⟨hy.1, hy.2.1⟩).add (((hph k).of_le (WithTop.coe_le_coe.2 le_top)).mono fun _ hy => ⟨hy.1, hy.2.2⟩)`.
-/
theorem c2on {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (th : LocPot X)
    (ph : X → ℝ) (hth : IsPotential A th) (hph : A.SmoothOn U ph) (x : X) (k : Fin A.n) :
    ContDiffOn ℝ 2 ((th + LocPot.ofFun ph).φ x ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U x ∩ U)) :=
  ((potSmoothOn A th hth x k).mono fun _ hy => ⟨hy.1, hy.2.1⟩).add
    (((hph k).of_le (WithTop.coe_le_coe.2 le_top)).mono fun _ hy => ⟨hy.1, hy.2.2⟩)

/- English proof (translation)
The claim follows from `(c2on A U th ph hth hph x k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm ((th.isOpen_U x).inter hU)).mem_nhds hy)`.
-/
theorem c2at {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (hU : IsOpen U)
    (th : LocPot X) (ph : X → ℝ) (hth : IsPotential A th) (hph : A.SmoothOn U ph) (x : X) (k : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (th.U x ∩ U)) :
    ContDiffAt ℝ 2 ((th + LocPot.ofFun ph).φ x ∘ (A.chart k).symm) y :=
  (c2on A U th ph hth hph x k).contDiffAt
    (((A.chart k).isOpen_inter_preimage_symm ((th.isOpen_U x).inter hU)).mem_nhds hy)

/- English proof (translation)
Use `set x₀ := (A.chart j).symm y₀ with hx₀`. Establish `hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (th i).U x₀) ∩ U))` using `(A.chart j).isOpen_inter_preimage_symm ((isOpen_iInter_of_finite fun i => (th i).isOpen_U _).inter hU)`. Establish `hyV : y₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (th i).U x₀) ∩ U)` using `⟨hy₀, Set.mem_iInter.2 fun i => (th i).mem_U _, hyU⟩`. Establish `heq : maDens (fun i => (th i + LocPot.ofFun (ph i)).φ x₀ ∘ (A.chart j).symm) =ᶠ[𝓝 y₀] locDens A (fun i => th i + LocPot.ofFun (ph i)) j` using `by filter_upwards [hVo.mem_nhds hyV] with y hy`. Use `symm`.

Unfold `locDens`. Apply `maDens_congr_hessC` to reduce the goal to its premises. Introduce `i`. Establish `hx` using `Set.mem_iInter.1 hy.2.1 i`. Take `⟨W, hWo, hyW, G, hG, hGeq⟩` from `(hth i).2 ((A.chart j).symm y) x₀ _ ⟨(th i).mem_U _, hx⟩`.

Establish `hn : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U x₀) ∈ 𝓝 y` using `((A.chart j).isOpen_inter_preimage_symm ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))).mem_nhds ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hx⟩`. Establish `h1 : (fun y' => (th i + LocPot.ofFun (ph i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y] fun w => ((th i + LocPot.ofFun (ph i)).φ x₀ ∘ (A.chart j).symm) w + ((G ∘ (A.chart j).symm) w).re` using `by filter_upwards [hn] with w hw`. Use `hGeq _ hw.2` as an intermediate fact. Use `show (th i).φ ((A.chart j).symm y) ((A.chart j).symm w) + ph i ((A.chart j).symm w) = (th i).φ x₀ ((A.chart j).symm w) + ph i ((A.chart j).symm w) + (G ((A.chart j).symm w)).re`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hessCGerm _ _ _ h1]`. Conclude with `ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _ (c2at A U hU _ _ (hth i) (hph i) x₀ j ⟨hy.1, hx, hy.2.2⟩) (hG j y ⟨hy.1, hyW⟩)`. Use `ContinuousAt.congr ?_ heq` and prove the remaining obligations. Use `(maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hyV)` and prove the remaining obligations. Conclude with `(c2on A U _ _ (hth i) (hph i) x₀ j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.1 i, hy.2.2⟩`.
-/
theorem dens_cont {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (hU : IsOpen U)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (hth : ∀ i, IsPotential A (th i))
    (hph : ∀ i, A.SmoothOn U (ph i)) (j : Fin A.n) (y₀ : Fin e → ℂ) (hy₀ : y₀ ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y₀ ∈ U) :
    ContinuousAt (locDens A (fun i => th i + LocPot.ofFun (ph i)) j) y₀ := by
  set x₀ := (A.chart j).symm y₀ with hx₀
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (th i).U x₀) ∩ U)) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_iInter_of_finite fun i => (th i).isOpen_U _).inter hU)
  have hyV : y₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (th i).U x₀) ∩ U) :=
    ⟨hy₀, Set.mem_iInter.2 fun i => (th i).mem_U _, hyU⟩
  have heq : maDens (fun i => (th i + LocPot.ofFun (ph i)).φ x₀ ∘ (A.chart j).symm) =ᶠ[𝓝 y₀]
      locDens A (fun i => th i + LocPot.ofFun (ph i)) j := by
    filter_upwards [hVo.mem_nhds hyV] with y hy
    symm
    unfold locDens
    apply maDens_congr_hessC
    intro i
    have hx := Set.mem_iInter.1 hy.2.1 i
    obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ := (hth i).2 ((A.chart j).symm y) x₀ _ ⟨(th i).mem_U _, hx⟩
    have hn : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U x₀) ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm
        ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))).mem_nhds ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hx⟩
    have h1 : (fun y' => (th i + LocPot.ofFun (ph i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
        fun w => ((th i + LocPot.ofFun (ph i)).φ x₀ ∘ (A.chart j).symm) w + ((G ∘ (A.chart j).symm) w).re := by
      filter_upwards [hn] with w hw
      have := hGeq _ hw.2
      show (th i).φ ((A.chart j).symm y) ((A.chart j).symm w) + ph i ((A.chart j).symm w) =
        (th i).φ x₀ ((A.chart j).symm w) + ph i ((A.chart j).symm w) + (G ((A.chart j).symm w)).re
      linarith
    rw [hessCGerm _ _ _ h1]
    exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
      (c2at A U hU _ _ (hth i) (hph i) x₀ j ⟨hy.1, hx, hy.2.2⟩) (hG j y ⟨hy.1, hyW⟩)
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hyV)
  exact (c2on A U _ _ (hth i) (hph i) x₀ j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.1 i, hy.2.2⟩

/- English proof (translation)
The claim follows from `(hf j).continuousOn.continuousAt (by simpa using (A.chart j).open_target.mem_nhds hy)`.
-/
theorem cont_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (f : X → ℝ) (hf : A.Smooth f)
    (j : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target) : ContinuousAt (f ∘ (A.chart j).symm) y :=
  (hf j).continuousOn.continuousAt (by simpa using (A.chart j).open_target.mem_nhds hy)

end PositivityTheory.Xgp.per_int

open PositivityTheory.Xgp.per_int in

/- English proof (translation)
Introduce `e X _ _ _ A Ψ _ _ N j U th ph hj he hU hN hth hph hun hI`. Set `pot : Ψ × Fin N → LocPot X` to `fun p => th p + LocPot.ofFun (ph p)`. Set `Pc : (Ψ × Fin N → ℝ) → ℝ` to `fun c => ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)`. Establish `hP1 : 0 < Pc fun _ => 1` using `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l hl => Finset.sum_pos (fun _ _ => one_pos) ⟨i, Finset.mem_Ico.2 ⟨le_rfl, Finset.mem_Ioi.1 hl⟩⟩`. Establish `hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (pot a) x` using `fun a x hx k hk => c2at A U hU _ _ (hth a) (hph a) x k ⟨(A.chart k).map_source hk, by simpa [(A.chart k).left_inv hk] using ⟨(th a).mem_U x, hx⟩⟩`.

Establish `hexp` using `fun c : Ψ × Fin N → ℝ => mInt_sumPot_expand e X A _ U pot (fun _ => c) (fun _ => 1) hN hC hI`. Establish `hpt : ∀ k, ∀ᵐ y, y ∈ (A.chart k).target → ∃ ν : ℝ, 0 ≤ ν ∧ ∀ c, locDens A (fun _ => sumPot c pot) k y = ν * Pc c` using `fun k => by filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN k)] with y hy hyt`. Establish `hyU : (A.chart k).symm y ∈ U`. Assume the negation of the conclusion as `h`. Conclude with `hy ⟨hyt, h⟩`.

Take `⟨V, g, hg⟩` from `hun.1 _ hyU`. Take `⟨ν, h0, -, h⟩` from `PositivityTheory.Xgp.t_per_point e X A Ψ N j hj pot _ V g hg he k ((A.chart k).map_target hyt)`. Rewrite `h` using `[(A.chart k).right_inv hyt]`. Conclude with `⟨ν, h0, h⟩`. Establish `hne : Nonempty (ChartPartition A)` using `existsPartition A`.

Establish `hprop : ∀ c, mInt A (fun _ => sumPot c pot) (fun _ => 1) = mInt A (fun _ => sumPot (fun _ => 1) pot) (fun _ => 1) / (Pc fun _ => 1) * Pc c` using `fun c => by`. Simplify using `only [mInt, dif_pos hne, integralWith]`. Rewrite using `[Finset.sum_div, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_div, ← integral_mul_const]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae (hpt k), ae_restrict_mem (A.chart k).open_target.measurableSet] with y hy hyt`. Take `⟨ν, -, h⟩` from `hy hyt`. Rewrite using `[h, h]`. Clear the denominators using the available nonvanishing facts.

Establish `hpos : 0 < mInt A (fun _ => sumPot (fun _ => 1) pot) (fun _ => 1)`. Simplify using `only [mInt, dif_pos hne, integralWith]`. Establish `hnn : ∀ k, 0 ≤ᵐ[volume.restrict (A.chart k).target] fun y => hne.some.χ k ((A.chart k).symm y) * 1 * locDens A (fun _ => sumPot (fun _ => 1) pot) k y` using `fun k => by filter_upwards [ae_restrict_of_ae (hpt k), ae_restrict_mem (A.chart k).open_target.measurableSet] with y hy hyt`. Take `⟨ν, h0, h⟩` from `hy hyt`. Use `hne.some.nonneg k ((A.chart k).symm y)` as an intermediate fact.

Rewrite using `[h]`. Check the signs of the components of the expression. Take `⟨x, hx, V, g, hg, him⟩` from `hun.2`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, hne.some.χ k x ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Use `hne.some.sum_eq_one x` as an intermediate fact. Simplify using `[h] at this`. Establish `hxk : x ∈ (A.chart k).source` using `hne.some.tsupport_subset k (subset_tsupport _ hk)`. Establish `hyt` using `(A.chart k).map_source hxk`.

Establish `hsx` using `(A.chart k).left_inv hxk`. Use `Finset.sum_pos' (fun k _ => integral_nonneg_of_ae (hnn k)) ⟨k, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `(setIntegral_pos_iff_support_of_nonneg_ae (hnn k) (integrableOn_weight A hne.some _ (fun _ => 1) (hexp fun _ => 1).1 k)).2 ?_` and prove the remaining obligations. Establish `hcd : ContinuousAt (locDens A (fun _ => sumPot (fun _ => 1) pot) k) (A.chart k x)`. Establish `h1 : ContinuousAt (fun y => ∑ w : Fin e → Ψ × Fin N, (∏ _i : Fin e, (1 : ℝ)) * locDens A (fun i => pot (w i)) k y) (A.chart k x)` using `tendsto_finset_sum _ fun w _ => continuousAt_const.mul (dens_cont A U hU _ _ (fun i => hth (w i)) (fun i => hph (w i)) k _ hyt (by rwa [hsx]))`.

Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [((A.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨hyt, show _ ∈ U by rwa [hsx]⟩] with y hy`. Conclude with `(locDens_sumPot_expand A pot (fun _ _ => 1) k hy.1 fun a => hC a _ hy.2).symm`. Establish `hcf : ContinuousAt (fun y => hne.some.χ k ((A.chart k).symm y) * 1 * locDens A (fun _ => sumPot (fun _ => 1) pot) k y) (A.chart k x)` using `((cont_chart A _ (hne.some.smooth k) k _ hyt).mul continuousAt_const).mul hcd`. Take `⟨ν, -, hν, h⟩` from `PositivityTheory.Xgp.t_per_point e X A Ψ N j hj pot x V g hg he k hxk`.

Establish `hv : hne.some.χ k ((A.chart k).symm (A.chart k x)) * 1 * locDens A (fun _ => sumPot (fun _ => 1) pot) k (A.chart k x) ≠ 0`. Rewrite using `[h, hsx]`. Conclude with `mul_ne_zero (mul_ne_zero hk one_ne_zero) (mul_pos (hν him) hP1).ne'`. Conclude with `Measure.measure_pos_of_mem_nhds _ (inter_mem (hcf.eventually_ne hv) ((A.chart k).open_target.mem_nhds hyt))`. Use `⟨_, div_pos hpos hP1, (PositivityTheory.Xgp.t_poly_delta Ψ N _ _ fun c => ?_).1⟩` and prove the remaining obligations.

Rewrite using `[← hprop c, (hexp c).2]`. Simplify using `only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]`. Conclude with `Finset.sum_congr rfl fun w _ => mul_comm _ _`.
-/
theorem PositivityTheory.Xgp.t_per_int : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N := by
  intro e X _ _ _ A Ψ _ _ N j U th ph hj he hU hN hth hph hun hI
  let pot : Ψ × Fin N → LocPot X := fun p => th p + LocPot.ofFun (ph p)
  let Pc : (Ψ × Fin N → ℝ) → ℝ := fun c => ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)
  have hP1 : 0 < Pc fun _ => 1 :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l hl =>
      Finset.sum_pos (fun _ _ => one_pos) ⟨i, Finset.mem_Ico.2 ⟨le_rfl, Finset.mem_Ioi.1 hl⟩⟩
  have hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (pot a) x := fun a x hx k hk =>
    c2at A U hU _ _ (hth a) (hph a) x k
      ⟨(A.chart k).map_source hk, by simpa [(A.chart k).left_inv hk] using ⟨(th a).mem_U x, hx⟩⟩
  have hexp := fun c : Ψ × Fin N → ℝ => mInt_sumPot_expand e X A _ U pot (fun _ => c) (fun _ => 1) hN hC hI
  have hpt : ∀ k, ∀ᵐ y, y ∈ (A.chart k).target → ∃ ν : ℝ, 0 ≤ ν ∧
      ∀ c, locDens A (fun _ => sumPot c pot) k y = ν * Pc c := fun k => by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN k)] with y hy hyt
    have hyU : (A.chart k).symm y ∈ U := by
      by_contra h
      exact hy ⟨hyt, h⟩
    obtain ⟨V, g, hg⟩ := hun.1 _ hyU
    obtain ⟨ν, h0, -, h⟩ := PositivityTheory.Xgp.t_per_point e X A Ψ N j hj pot _ V g hg he k ((A.chart k).map_target hyt)
    rw [(A.chart k).right_inv hyt] at h
    exact ⟨ν, h0, h⟩
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hprop : ∀ c, mInt A (fun _ => sumPot c pot) (fun _ => 1) =
      mInt A (fun _ => sumPot (fun _ => 1) pot) (fun _ => 1) / (Pc fun _ => 1) * Pc c := fun c => by
    simp only [mInt, dif_pos hne, integralWith]
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_div, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hpt k), ae_restrict_mem (A.chart k).open_target.measurableSet] with y hy hyt
    obtain ⟨ν, -, h⟩ := hy hyt
    rw [h, h]
    field_simp
  have hpos : 0 < mInt A (fun _ => sumPot (fun _ => 1) pot) (fun _ => 1) := by
    simp only [mInt, dif_pos hne, integralWith]
    have hnn : ∀ k, 0 ≤ᵐ[volume.restrict (A.chart k).target] fun y => hne.some.χ k ((A.chart k).symm y) * 1 *
        locDens A (fun _ => sumPot (fun _ => 1) pot) k y := fun k => by
      filter_upwards [ae_restrict_of_ae (hpt k), ae_restrict_mem (A.chart k).open_target.measurableSet] with y hy hyt
      obtain ⟨ν, h0, h⟩ := hy hyt
      have := hne.some.nonneg k ((A.chart k).symm y)
      rw [h]
      positivity
    obtain ⟨x, hx, V, g, hg, him⟩ := hun.2
    obtain ⟨k, hk⟩ : ∃ k, hne.some.χ k x ≠ 0 := by
      by_contra h
      push Not at h
      have := hne.some.sum_eq_one x
      simp [h] at this
    have hxk : x ∈ (A.chart k).source := hne.some.tsupport_subset k (subset_tsupport _ hk)
    have hyt := (A.chart k).map_source hxk
    have hsx := (A.chart k).left_inv hxk
    refine Finset.sum_pos' (fun k _ => integral_nonneg_of_ae (hnn k)) ⟨k, Finset.mem_univ _, ?_⟩
    refine (setIntegral_pos_iff_support_of_nonneg_ae (hnn k)
      (integrableOn_weight A hne.some _ (fun _ => 1) (hexp fun _ => 1).1 k)).2 ?_
    have hcd : ContinuousAt (locDens A (fun _ => sumPot (fun _ => 1) pot) k) (A.chart k x) := by
      have h1 : ContinuousAt (fun y => ∑ w : Fin e → Ψ × Fin N, (∏ _i : Fin e, (1 : ℝ)) *
          locDens A (fun i => pot (w i)) k y) (A.chart k x) :=
        tendsto_finset_sum _ fun w _ => continuousAt_const.mul
          (dens_cont A U hU _ _ (fun i => hth (w i)) (fun i => hph (w i)) k _ hyt (by rwa [hsx]))
      refine h1.congr ?_
      filter_upwards [((A.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨hyt, show _ ∈ U by rwa [hsx]⟩] with y hy
      exact (locDens_sumPot_expand A pot (fun _ _ => 1) k hy.1 fun a => hC a _ hy.2).symm
    have hcf : ContinuousAt (fun y => hne.some.χ k ((A.chart k).symm y) * 1 *
        locDens A (fun _ => sumPot (fun _ => 1) pot) k y) (A.chart k x) :=
      ((cont_chart A _ (hne.some.smooth k) k _ hyt).mul continuousAt_const).mul hcd
    obtain ⟨ν, -, hν, h⟩ := PositivityTheory.Xgp.t_per_point e X A Ψ N j hj pot x V g hg he k hxk
    have hv : hne.some.χ k ((A.chart k).symm (A.chart k x)) * 1 *
        locDens A (fun _ => sumPot (fun _ => 1) pot) k (A.chart k x) ≠ 0 := by
      rw [h, hsx]
      exact mul_ne_zero (mul_ne_zero hk one_ne_zero) (mul_pos (hν him) hP1).ne'
    exact Measure.measure_pos_of_mem_nhds _ (inter_mem (hcf.eventually_ne hv) ((A.chart k).open_target.mem_nhds hyt))
  refine ⟨_, div_pos hpos hP1, (PositivityTheory.Xgp.t_poly_delta Ψ N _ _ fun c => ?_).1⟩
  rw [← hprop c, (hexp c).2]
  simp only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]
  exact Finset.sum_congr rfl fun w _ => mul_comm _ _
