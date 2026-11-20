import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

/- English proof (translation)
Introduce `K _ _ n _ _ ν _ β f hβ hf`. Establish `hs : IsCompact (tsupport β)` using `hβ.cpt`. Use `set F : AdelicGLn.AdelicGL K n × archGroup K n → ℂ := fun p => (β p.2 : ℂ) * f (p.1 * infEmb K n p.2) with hFdef`. Establish `hF : Continuous F` using `(Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd)))`. Establish `hFx : ∀ x, Continuous fun y => F (x, y)` using `fun x => hF.comp (continuous_const.prodMk continuous_id)`.

Establish `hint : ∀ x, IntegrableOn (fun y => F (x, y)) (tsupport β) ν` using `fun x => (hFx x).continuousOn.integrableOn_compact hs`. Establish `e : ∀ x, sm ν β f x = ∫ y in tsupport β, F (x, y) ∂ν` using `fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by`. Simplify using `[hFdef, image_eq_zero_of_notMem_tsupport hy]).symm`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`.

Rewrite using `[Metric.continuousAt_iff']`. Introduce `ε hε`. Establish `hc : 0 ≤ ν.real (tsupport β)` using `measureReal_nonneg`. Use `set δ : ℝ := ε / (ν.real (tsupport β) + 1) with hδdef`. Establish `hδ : 0 < δ` using `div_pos hε (by linarith)`.

Establish `hopen : IsOpen {p : AdelicGLn.AdelicGL K n × archGroup K n | dist (F p) (F (x₀, p.2)) < δ}` using `isOpen_lt (hF.dist (hF.comp (continuous_const.prodMk continuous_snd))) continuous_const`. Take `⟨u, v, hu, -, hxu, hsv, huv⟩` from `generalized_tube_lemma (isCompact_singleton (x := x₀)) hs hopen (by`. Introduce and unpack `⟨x, y⟩ ⟨hx, -⟩`. Take `rfl : x = x₀` from `hx`. Simplify using `using hδ)`.

Use `filter_upwards [hu.mem_nhds (hxu rfl)] with x hx`. Rewrite using `[e, e, dist_eq_norm, ← integral_sub (hint x) (hint x₀)]`. Establish `hb : ‖∫ y in tsupport β, (F (x, y) - F (x₀, y)) ∂ν‖ ≤ δ * ν.real (tsupport β)`. Use `norm_setIntegral_le_of_norm_le_const hs.measure_lt_top fun y hy => ?_` and prove the remaining obligations. Use `huv (Set.mk_mem_prod hx (hsv hy))` as an intermediate fact.

Simplify using `only [Set.mem_setOf_eq, dist_eq_norm] at this`. Conclude with `this.le`. Use `lt_of_le_of_lt hb ?_` and prove the remaining obligations. Rewrite using `[hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem continuous_sm_of_ker : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ),
    Ker ν β → Continuous f → Continuous (sm ν β f) := by
  intro K _ _ n _ _ ν _ β f hβ hf
  have hs : IsCompact (tsupport β) := hβ.cpt
  set F : AdelicGLn.AdelicGL K n × archGroup K n → ℂ :=
    fun p => (β p.2 : ℂ) * f (p.1 * infEmb K n p.2) with hFdef
  have hF : Continuous F :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul
      (hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd)))
  have hFx : ∀ x, Continuous fun y => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (fun y => F (x, y)) (tsupport β) ν := fun x =>
    (hFx x).continuousOn.integrableOn_compact hs
  have e : ∀ x, sm ν β f x = ∫ y in tsupport β, F (x, y) ∂ν := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [hFdef, image_eq_zero_of_notMem_tsupport hy]).symm
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hc : 0 ≤ ν.real (tsupport β) := measureReal_nonneg
  set δ : ℝ := ε / (ν.real (tsupport β) + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hopen : IsOpen {p : AdelicGLn.AdelicGL K n × archGroup K n | dist (F p) (F (x₀, p.2)) < δ} :=
    isOpen_lt (hF.dist (hF.comp (continuous_const.prodMk continuous_snd))) continuous_const
  obtain ⟨u, v, hu, -, hxu, hsv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x₀)) hs hopen (by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain rfl : x = x₀ := hx
    simpa using hδ)
  filter_upwards [hu.mem_nhds (hxu rfl)] with x hx
  rw [e, e, dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have hb : ‖∫ y in tsupport β, (F (x, y) - F (x₀, y)) ∂ν‖ ≤ δ * ν.real (tsupport β) := by
    refine norm_setIntegral_le_of_norm_le_const hs.measure_lt_top fun y hy => ?_
    have := huv (Set.mk_mem_prod hx (hsv hy))
    simp only [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine lt_of_le_of_lt hb ?_
  rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CompanionTheory.Conc
