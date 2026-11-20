import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Use `haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddHaarMeasure := by`. Unfold `GlobalTheory.CompanionTheory.MirPair.piHaar`. Use `infer_instance`.

Use `haveI : SigmaFinite (GlobalTheory.CompanionTheory.MirPair.piHaar ν m) := by`. Unfold `GlobalTheory.CompanionTheory.MirPair.piHaar`. Use `infer_instance`. Use `haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddRightInvariant := inferInstance`. Use `set μ := GlobalTheory.CompanionTheory.MirPair.piHaar ν m with hμ`.

Establish `hbox : ∀ s : kˣ, GlobalTheory.SplitWeil.FourierPi.box (Fin m) s = (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s : Set (Fin m → k))`. Introduce `s`. Rewrite using `[GlobalTheory.CompanionTheory.BZOnto.PerpSmall.coe_box]`. Both sides reduce to the same expression. Use `set B' : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m (c * t⁻¹) : Set (Fin m → k)) with hB'`.

Use `set Bt : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m t : Set (Fin m → k)) with hBt`. Establish `hB'c : IsCompact B'` using `GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m _`. Establish `hB'm : MeasurableSet B'` using `hB'c.isClosed.measurableSet`. Establish `hBtm : MeasurableSet Bt` using `(GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m t).isClosed.measurableSet`. Establish `hpos : 0 < μ.real B'`.

Rewrite using `[measureReal_def]`. Conclude with `ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box_mem_nhds m _)).ne' hB'c.measure_lt_top.ne`. Establish `hfour : ∀ x, ∫ b, B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ x) : Circle) : ℂ) ∂μ = Bt.indicator (fun _ => ((μ.real B' : ℝ) : ℂ)) x`. Introduce `x`. Establish `e` using `GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi μ hc t x`.

Rewrite `e` using `[hbox, hbox]`. Conclude with `e`. Establish `hcc : Continuous (fun z : Circle => (z : ℂ))` using `continuous_induced_dom`. Establish `hdot : Continuous fun q : (Fin m → k) × (Fin m → k) => q.1 ⬝ᵥ q.2` using `GlobalTheory.SplitWeil.FourierPi.continuous_dot`. Establish `hψc : Continuous fun q : (Fin m → k) × (Fin m → k) => ((ψ (-(q.1 ⬝ᵥ q.2)) : Circle) : ℂ)` using `hcc.comp (hψ.comp hdot.neg)`.

Establish `hg1 : Integrable (B'.indicator fun _ => (1 : ℂ)) μ` using `(integrable_indicator_iff hB'm).2 (continuousOn_const.integrableOn_compact' hB'c hB'm)`. Establish `hg2 : Integrable (M.indicator f) μ` using `(integrable_indicator_iff hMm).2 (hf.continuousOn.integrableOn_compact' hM hMm)`. Establish `hint : Integrable (fun z : (Fin m → k) × (Fin m → k) => ((ψ (-(z.1 ⬝ᵥ z.2)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) z.1 * M.indicator f z.2)) (μ.prod μ)`. Use `(hg1.mul_prod hg2).bdd_mul (c := 1) hψc.aestronglyMeasurable (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Simplify using `[Circle.norm_coe]`.

Establish `hswap : ∫ b, (∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ = ∫ x, (∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ` using `integral_integral_swap hint`. Establish `hD : (fun b => ∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = B'.indicator (fun _ => A)`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b ∈ B'`. Simplify using `only [Set.indicator_of_mem hb, one_mul]`.

Establish `hx : (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * M.indicator f x) = M.indicator (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x)`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hxM : x ∈ M`. Simplify using `only [Set.indicator_of_mem hxM]`. Simplify using `only [Set.indicator_of_notMem hxM, mul_zero]`.

Rewrite using `[hx, integral_indicator hMm]`. Conclude with `h b hb`. Simplify using `[Set.indicator_of_notMem hb]`. Establish `hE : (fun x => ∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = fun x => ((μ.real B' : ℝ) : ℂ) * (M ∩ Bt).indicator f x`. Use function extensionality and compare the values at `x`.

Establish `e : ∀ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) = B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ -x) : Circle) : ℂ) * M.indicator f x`. Introduce `b`. Rewrite using `[dotProduct_neg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`.

Rewrite using `[integral_mul_const, hfour (-x)]`. Establish `hneg : -x ∈ Bt ↔ x ∈ Bt`. Simplify using `only [hBt, SetLike.mem_coe, neg_mem_iff]`. Distinguish the cases in `hxB : x ∈ Bt`. Distinguish the cases in `hxM : x ∈ M`.

Simplify using `only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_mem hxM, Set.indicator_of_mem (Set.mem_inter hxM hxB)]`. Simplify using `only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_notMem hxM, Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxM hx.1), mul_zero]`. Simplify using `only [Set.indicator_of_notMem (fun hx : -x ∈ Bt => hxB (hneg.1 hx)), Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxB hx.2), zero_mul, mul_zero]`. Rewrite `hswap` using `[hD, hE, integral_indicator_const _ hB'm, integral_const_mul, integral_indicator (hMm.inter hBtm), Complex.real_smul]`. Conclude with `(mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne') hswap).symm`.
-/
theorem setIntegral_inter_box_of_twists {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (c : kˣ) (hψ : Continuous ψ) (hc : HasConductor ψ c) (m : ℕ) (t : kˣ)
    (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ) (hM : IsCompact M) (hMm : MeasurableSet M)
    (hf : Continuous f)
    (h : ∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) :
    ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddHaarMeasure := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.MirPair.piHaar ν m) := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddRightInvariant := inferInstance
  set μ := GlobalTheory.CompanionTheory.MirPair.piHaar ν m with hμ
  have hbox : ∀ s : kˣ, GlobalTheory.SplitWeil.FourierPi.box (Fin m) s = (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s : Set (Fin m → k)) := by
    intro s
    rw [GlobalTheory.CompanionTheory.BZOnto.PerpSmall.coe_box]
    rfl
  set B' : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m (c * t⁻¹) : Set (Fin m → k)) with hB'
  set Bt : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m t : Set (Fin m → k)) with hBt
  have hB'c : IsCompact B' := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m _
  have hB'm : MeasurableSet B' := hB'c.isClosed.measurableSet
  have hBtm : MeasurableSet Bt := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m t).isClosed.measurableSet
  have hpos : 0 < μ.real B' := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box_mem_nhds m _)).ne'
      hB'c.measure_lt_top.ne
  have hfour : ∀ x, ∫ b, B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ x) : Circle) : ℂ) ∂μ =
      Bt.indicator (fun _ => ((μ.real B' : ℝ) : ℂ)) x := by
    intro x
    have e := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi μ hc t x
    rw [hbox, hbox] at e
    exact e
  have hcc : Continuous (fun z : Circle => (z : ℂ)) := continuous_induced_dom
  have hdot : Continuous fun q : (Fin m → k) × (Fin m → k) => q.1 ⬝ᵥ q.2 :=
    GlobalTheory.SplitWeil.FourierPi.continuous_dot
  have hψc : Continuous fun q : (Fin m → k) × (Fin m → k) => ((ψ (-(q.1 ⬝ᵥ q.2)) : Circle) : ℂ) :=
    hcc.comp (hψ.comp hdot.neg)
  have hg1 : Integrable (B'.indicator fun _ => (1 : ℂ)) μ :=
    (integrable_indicator_iff hB'm).2 (continuousOn_const.integrableOn_compact' hB'c hB'm)
  have hg2 : Integrable (M.indicator f) μ :=
    (integrable_indicator_iff hMm).2 (hf.continuousOn.integrableOn_compact' hM hMm)
  have hint : Integrable (fun z : (Fin m → k) × (Fin m → k) => ((ψ (-(z.1 ⬝ᵥ z.2)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) z.1 * M.indicator f z.2)) (μ.prod μ) := by
    refine (hg1.mul_prod hg2).bdd_mul (c := 1) hψc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp [Circle.norm_coe]
  have hswap : ∫ b, (∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ =
      ∫ x, (∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ :=
    integral_integral_swap hint
  have hD : (fun b => ∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = B'.indicator (fun _ => A) := by
    funext b
    by_cases hb : b ∈ B'
    · simp only [Set.indicator_of_mem hb, one_mul]
      have hx : (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * M.indicator f x) =
          M.indicator (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x) := by
        funext x
        by_cases hxM : x ∈ M
        · simp only [Set.indicator_of_mem hxM]
        · simp only [Set.indicator_of_notMem hxM, mul_zero]
      rw [hx, integral_indicator hMm]
      exact h b hb
    · simp [Set.indicator_of_notMem hb]
  have hE : (fun x => ∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) =
      fun x => ((μ.real B' : ℝ) : ℂ) * (M ∩ Bt).indicator f x := by
    funext x
    have e : ∀ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) =
        B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ -x) : Circle) : ℂ) * M.indicator f x := by
      intro b
      rw [dotProduct_neg]
      ring
    simp only [e]
    rw [integral_mul_const, hfour (-x)]
    have hneg : -x ∈ Bt ↔ x ∈ Bt := by
      simp only [hBt, SetLike.mem_coe, neg_mem_iff]
    by_cases hxB : x ∈ Bt
    · by_cases hxM : x ∈ M
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_mem hxM,
          Set.indicator_of_mem (Set.mem_inter hxM hxB)]
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_notMem hxM,
          Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxM hx.1), mul_zero]
    · simp only [Set.indicator_of_notMem (fun hx : -x ∈ Bt => hxB (hneg.1 hx)),
        Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxB hx.2), zero_mul, mul_zero]
  rw [hD, hE, integral_indicator_const _ hB'm, integral_const_mul,
    integral_indicator (hMm.inter hBtm), Complex.real_smul] at hswap
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne') hswap).symm

end GlobalTheory.CompanionTheory.MirPair
