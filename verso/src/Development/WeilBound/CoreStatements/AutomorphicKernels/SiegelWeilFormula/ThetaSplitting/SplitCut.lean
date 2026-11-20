import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Conclude with `KSplitW.commW d R w x hx y`.
-/
theorem commW (d : SD σ) (R : RD d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  exact KSplitW.commW d R w x hx y

/- English proof (translation)
Conclude with `KSplitW.iota_mem_K d R w y hy`.
-/
theorem iota_mem_K (d : SD σ) (R : RD d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  exact KSplitW.iota_mem_K d R w y hy

/- English proof (translation)
Conclude with `KSplitW.kSplit d R w k hk`.
-/
theorem kSplit (d : SD σ) (R : RD d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  exact KSplitW.kSplit d R w k hk

/- English proof (translation)
Conclude with `KSplitP.iota_isPar d R w q hq`.
-/
theorem iota_isPar (d : SD σ) (R : RD d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  exact KSplitP.iota_isPar d R w q hq

/- English proof (translation)
Conclude with `KSplitP.isPar_mul hp hp'`.
-/
theorem isPar_mul {n : ℕ} {Y : Spc F E n} {p p' : G2 σ Y} {t t' : GL (Fin n) (AE F E)} (hp : IsPar p t) (hp' : IsPar p' t') :
    IsPar (p * p') (t * t') := by
  exact KSplitP.isPar_mul hp hp'

/- English proof (translation)
Conclude with `KSplitP.siegel d hp`.
-/
theorem siegel (d : SD σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ := by
  exact KSplitP.siegel d hp

/- English proof (translation)
Conclude with `KSplitP.T_zero d Φ`.
-/
theorem T_zero (d : SD σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  exact KSplitP.T_zero d Φ

/- English proof (translation)
Conclude with `KSplitP.loc_zero d R w`.
-/
theorem loc_zero (d : SD σ) (R : RD d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  exact KSplitP.loc_zero d R w

/- English proof (translation)
Conclude with `KSplitP.fP_sw P`.
-/
theorem fP_sw {m n : ℕ} (P : PX m n) : IsSw (fP P) := by
  exact KSplitP.fP_sw P

/- English proof (translation)
Conclude with `KSplitP.absE_pos z`.
-/
theorem absE_pos (z : (AE F E)ˣ) : 0 < (absE F E z : ℝ) := by
  exact KSplitP.absE_pos z

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g`. Take `⟨p, t, hp, k, hk, rfl⟩` from `d.ok.hgt.iwa g`. Take `⟨y, hk'K, hk'w⟩` from `kSplit d R w k hk`. Use `set k' := (R.ι w y)⁻¹ * k with hk'`. Establish `hcomm` using `commW d R w k' hk'w`.

Take `⟨A, hA⟩` from `hAw F E σ d R w k' hk'w`. Establish `hΨi : d.Indep w Ψ` using `((hF F E σ d R).2.1 w Ψ hΨ).2`. Take `⟨C, hC⟩` from `siegel d hp`. Use `⟨p * k', y, C * A Ψ 0, (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ), absE_pos _, ?_, fun y' => ⟨?_, fun P => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hcomm y, hk', mul_inv_cancel_left]`.

Take `⟨q, k₀, rfl, hq, hk₀, hloc⟩` from `Glob.locIwasawa y'`. Take `⟨tq, hPq, habs⟩` from `iota_isPar d R w q hq`. Establish `e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k')`. Rewrite using `[map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]`. Simplify using `only [mul_assoc]`.

Establish `hval` using `d.ok.hgt.val _ _ (isPar_mul hp hPq) _ ((d.K).mul_mem (iota_mem_K d R w k₀ hk₀) hk'K)`. Establish `h0 : 0 ≤ d.a ((p * R.ι w q) * (R.ι w k₀ * k'))` using `by rw [hval]; exact NNReal.coe_nonneg _`. Use `show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _`. Rewrite using `[e, Real.coe_toNNReal _ h0, hval, map_mul, map_mul, NNReal.coe_mul, habs, hloc]`. Establish `hsw` using `fP_sw P`.

Establish `hΞ` using `(hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2`. Establish `hΞs : d.om (R.ι w y') (φ P) ∈ d.sch` using `d.ok.dbl.weil.2.1.pres _ _ (hφ P).1`. Establish `h2` using `(hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ`. Establish `hs2 : d.om k' (d.om (R.ι w y') (φ P)) ∈ d.sch` using `d.ok.dbl.weil.2.1.pres _ _ hΞs`. Unfold `SD.sec0`.

Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hs2, ← T_zero, h2]`. Simplify using `only [RD.tens, loc_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gSplit_of (hF : FockMem) (hAw : AwayAct) : GSplit := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  obtain ⟨y, hk'K, hk'w⟩ := kSplit d R w k hk
  set k' := (R.ι w y)⁻¹ * k with hk'
  have hcomm := commW d R w k' hk'w
  obtain ⟨A, hA⟩ := hAw F E σ d R w k' hk'w
  have hΨi : d.Indep w Ψ := ((hF F E σ d R).2.1 w Ψ hΨ).2
  obtain ⟨C, hC⟩ := siegel d hp
  refine ⟨p * k', y, C * A Ψ 0, (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ), absE_pos _, ?_,
    fun y' => ⟨?_, fun P => ?_⟩⟩
  · rw [mul_assoc, hcomm y, hk', mul_inv_cancel_left]
  · obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := Glob.locIwasawa y'
    obtain ⟨tq, hPq, habs⟩ := iota_isPar d R w q hq
    have e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k') := by
      rw [map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]
      simp only [mul_assoc]
    have hval := d.ok.hgt.val _ _ (isPar_mul hp hPq) _ ((d.K).mul_mem (iota_mem_K d R w k₀ hk₀) hk'K)
    have h0 : 0 ≤ d.a ((p * R.ι w q) * (R.ι w k₀ * k')) := by rw [hval]; exact NNReal.coe_nonneg _
    show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _
    rw [e, Real.coe_toNNReal _ h0, hval, map_mul, map_mul, NNReal.coe_mul, habs, hloc]
  · have hsw := fP_sw P
    have hΞ := (hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2
    have hΞs : d.om (R.ι w y') (φ P) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ (hφ P).1
    have h2 := (hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ
    have hs2 : d.om k' (d.om (R.ι w y') (φ P)) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ hΞs
    unfold SD.sec0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hs2, ← T_zero, h2]
    simp only [RD.tens, loc_zero]
    ring

end PositivityTheory.SiegelWeilFormula.KSplit

end
