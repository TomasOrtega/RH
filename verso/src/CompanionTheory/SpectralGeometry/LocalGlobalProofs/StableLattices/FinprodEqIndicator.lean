import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerPos

/- English proof (translation)
Establish `e : ∏ i ∈ s, z i = ((∏ i ∈ s, (z i).re : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => Complex.ext (by simp) (by simp [(h i).2])`. Rewrite using `[e, Complex.ofReal_re, ENNReal.ofReal_prod_of_nonneg fun i _ => (h i).1]`.
-/
theorem ofReal_re_prod {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i, 0 ≤ (z i).re ∧ (z i).im = 0) :
    ENNReal.ofReal (∏ i ∈ s, z i).re = ∏ i ∈ s, ENNReal.ofReal (z i).re := by
  have e : ∏ i ∈ s, z i = ((∏ i ∈ s, (z i).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => Complex.ext (by simp) (by simp [(h i).2])
  rw [e, Complex.ofReal_re, ENNReal.ofReal_prod_of_nonneg fun i _ => (h i).1]

/- English proof (translation)
Establish `h` using `(ENNReal.continuous_ofReal.tendsto p).comp hp`. Use `h.congr fun s => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Conclude with `ENNReal.ofReal_prod_of_nonneg fun i _ => h0 i`.
-/
theorem hasProd_ofReal {ι : Type*} {a : ι → ℝ} {p : ℝ} (hp : HasProd a p) (h0 : ∀ i, 0 ≤ a i) :
    HasProd (fun i => ENNReal.ofReal (a i)) (ENNReal.ofReal p) := by
  have h := (ENNReal.continuous_ofReal.tendsto p).comp hp
  refine h.congr fun s => ?_
  simp only [Function.comp_apply]
  exact ENNReal.ofReal_prod_of_nonneg fun i _ => h0 i

/- English proof (translation)
Set `r : ι → ℝ` to `fun v => (L v).toReal`. Establish `hr0 : ∀ v, 0 ≤ r v` using `fun v => ENNReal.toReal_nonneg`. Establish `hLr : ∀ v, ENNReal.ofReal (r v) = L v` using `fun v => ENNReal.ofReal_toReal (hL v)`. Establish `hra : ∀ v, v ∉ S → r v = a v` using `fun v hv => by`. Simplify using `only [r]`.

Rewrite using `[hoff v hv, ENNReal.toReal_ofReal (ha0 v)]`. Establish `hsr : Summable fun v => |r v - 1|`. Use `hsum.congr_cofinite ?_` and prove the remaining obligations. Use `filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv`. Rewrite using `[hra v (by simpa using hv)]`.

Take `⟨hm, hsplit, -, -⟩` from `AbsTprod.abs_tprod ι r hsr`. Take `⟨-, htp⟩` from `hsplit S`. Establish `hT : ∏' v : {v // v ∉ S}, r v.1 = ∏' v : {v // v ∉ S}, a v.1` using `tprod_congr fun v => hra v.1 v.2`. Establish `hp` using `hasProd_ofReal hm.hasProd hr0`. Establish `e : (fun i => ENNReal.ofReal (r i)) = L` using `funext hLr`.

Rewrite `hp` using `[e, htp, hT, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hr0 v), ENNReal.ofReal_prod_of_nonneg fun v _ => hr0 v]`. Simplify `hp` using `only [hLr]`.
-/
theorem hasProd_of_tail {ι : Type} (L : ι → ℝ≥0∞) (a : ι → ℝ) (S : Finset ι) (hL : ∀ v, L v ≠ ⊤)
    (ha0 : ∀ v, 0 ≤ a v) (hoff : ∀ v, v ∉ S → L v = ENNReal.ofReal (a v))
    (hsum : Summable fun v => |a v - 1|) :
    HasProd L ((∏ v ∈ S, L v) * ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)) := by
  classical
  let r : ι → ℝ := fun v => (L v).toReal
  have hr0 : ∀ v, 0 ≤ r v := fun v => ENNReal.toReal_nonneg
  have hLr : ∀ v, ENNReal.ofReal (r v) = L v := fun v => ENNReal.ofReal_toReal (hL v)
  have hra : ∀ v, v ∉ S → r v = a v := fun v hv => by
    simp only [r]
    rw [hoff v hv, ENNReal.toReal_ofReal (ha0 v)]
  have hsr : Summable fun v => |r v - 1| := by
    refine hsum.congr_cofinite ?_
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
    rw [hra v (by simpa using hv)]
  obtain ⟨hm, hsplit, -, -⟩ := AbsTprod.abs_tprod ι r hsr
  obtain ⟨-, htp⟩ := hsplit S
  have hT : ∏' v : {v // v ∉ S}, r v.1 = ∏' v : {v // v ∉ S}, a v.1 :=
    tprod_congr fun v => hra v.1 v.2
  have hp := hasProd_ofReal hm.hasProd hr0
  have e : (fun i => ENNReal.ofReal (r i)) = L := funext hLr
  rw [e, htp, hT, ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hr0 v),
    ENNReal.ofReal_prod_of_nonneg fun v _ => hr0 v] at hp
  simpa only [hLr] using hp

/- English proof (translation)
Distinguish the cases in `hX : X ∈ intOff b S`. Rewrite using `[Set.indicator_of_mem hX]`. Use `finprod_eq_prod_of_mulSupport_subset _ ?_` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hvS`.

Apply `hv` to reduce the goal to its premises. Establish `hvS' : v ∉ S` using `by simpa using hvS`. Simplify using `only [hS v hvS']`. Conclude with `Set.indicator_of_mem (hX v hvS') _`. Rewrite using `[Set.indicator_of_notMem hX]`.

Establish `: ∃ v, v ∉ S ∧ projV v (projFin X) ∉ latV b v`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Conclude with `hX hne`. Take `⟨v, hvS, hv⟩` from `this`.

Use `finprod_eq_zero _ v ?_ ?_` and prove the remaining obligations. Simplify using `only [hS v hvS]`. Conclude with `Set.indicator_of_notMem hv _`. Establish `hfin : {w | projV w (projFin X) ∉ latV b w}.Finite` using `Filter.eventually_cofinite.1 (MeasProj.eventually_mem_latV b (projFin X))`. Use `(hfin.union S.finite_toSet).subset ?_` and prove the remaining obligations.

Introduce `w hw`. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc`. Apply `hw` to reduce the goal to its premises. Simplify using `only [hS w hc.2]`.

Conclude with `Set.indicator_of_mem hc.1 _`.
-/
theorem finprod_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∏ᶠ v, Φv v (projV v (projFin X)) =
      (intOff b S).indicator (fun Y => ∏ v ∈ S, Φv v (projV v (projFin Y))) X := by
  classical
  by_cases hX : X ∈ intOff b S
  · rw [Set.indicator_of_mem hX]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro v hv
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := by simpa using hvS
    simp only [hS v hvS']
    exact Set.indicator_of_mem (hX v hvS') _
  · rw [Set.indicator_of_notMem hX]
    have : ∃ v, v ∉ S ∧ projV v (projFin X) ∉ latV b v := by
      by_contra hne
      push Not at hne
      exact hX hne
    obtain ⟨v, hvS, hv⟩ := this
    refine finprod_eq_zero _ v ?_ ?_
    · simp only [hS v hvS]
      exact Set.indicator_of_notMem hv _
    · have hfin : {w | projV w (projFin X) ∉ latV b w}.Finite :=
        Filter.eventually_cofinite.1 (MeasProj.eventually_mem_latV b (projFin X))
      refine (hfin.union S.finite_toSet).subset ?_
      intro w hw
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hw
      simp only [hS w hc.2]
      exact Set.indicator_of_mem hc.1 _

end GlobalTheory.CompanionTheory.SW.EulerPos

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM d b n M I minf m hEu hm cinf c hc Φ Φi Φf Φv hΦi hpure hpos hprod`. Take `⟨hpi, hpf, hpv, hlat, -⟩` from `GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M`. Use `haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hCM n M`. Use `haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hCM n M`. Use `haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hCM n M v`.

Take `⟨hfin, hsum, S₀, hEP⟩` from `hEu`. Take `⟨-, -, -, -, -, -, -, S₁, hS₁⟩` from `GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hc hc`. Set `S : Finset (HeightOneSpectrum (𝓞 F))` to `(S₀ ∪ S₁) ∪ (Filter.eventually_cofinite.1 hpure.2.1).toFinset`. Establish `hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1`. Introduce `v hv`.

Assume the negation of the conclusion as `h`. Conclude with `hv (Finset.mem_union_right _ (by simpa using h))`. Establish `hS₀ : S₀ ⊆ S` using `fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)`. Establish `hS₁S : S₁ ⊆ S` using `fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)`. Take `⟨hc1, hcS⟩` from `hS₁ S hS₁S`.

Set `φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞` to `fun v X => ENNReal.ofReal (Φv v X).re`. Establish `hcv : ∀ v, Continuous (Φv v)` using `fun v => (hpure.1 v).1.continuous`. Establish `hφ : ∀ v, Measurable (φ v)` using `fun v => ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp (hcv v).measurable)`. Establish `hΦ : Φ = pureL b S Φi φ`. Use function extensionality and compare the values at `X`.

Rewrite using `[hprod X, hpure.2.2 (projFin X), GlobalTheory.CompanionTheory.SW.EulerPos.finprod_eq_indicator b Φv S hS X]`. Unfold `pureL`. Distinguish the cases in `hX : X ∈ intOff b S`. Rewrite using `[Set.indicator_of_mem hX, Set.indicator_of_mem hX, GlobalTheory.CompanionTheory.SW.EulerPos.ofReal_re_prod S _ fun v => hpos v _]`. Simplify using `[Set.indicator_of_notMem hX]`.

Establish `hBfin : ∀ v, ∫⁻ X, φ v X ∂(m v) ≠ ⊤`. Introduce `v`. Use `haveI := hm v`. Establish `hi : Integrable (Φv v) (m v)` using `(hcv v).integrable_of_hasCompactSupport (hpure.1 v).2`. Conclude with `hi.re.lintegral_lt_top.ne`.

Establish `hLB : ∀ v, ∫⁻ X, φ v X ∂(c v • m v) = (c v : ℝ≥0∞) * ∫⁻ X, φ v X ∂(m v)`. Introduce `v`. Rewrite using `[lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]`. Establish `hLfin : ∀ v, ∫⁻ X, φ v X ∂(c v • m v) ≠ ⊤` using `fun v => by`. Rewrite using `[hLB v]`.

Conclude with `ENNReal.mul_ne_top ENNReal.coe_ne_top (hBfin v)`. Set `a : HeightOneSpectrum (𝓞 F) → ℝ` to `fun v => (m v (latV b v)).toReal`. Establish `hoff : ∀ v, v ∉ S → ∫⁻ X, φ v X ∂(c v • m v) = ENNReal.ofReal (a v)`. Introduce `v hv`. Establish `hl : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))` using `(hlat v).2.measurableSet`.

Establish `hφv : φ v = (latV b v).indicator 1`. Use function extensionality and compare the values at `X`. Simplify using `only [φ, hS v hv]`. Distinguish the cases in `hX : X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))`. Simplify using `[Set.indicator_of_mem hX]`.

Simplify using `[Set.indicator_of_notMem hX]`. Rewrite using `[hLB v, hc1 v hv, hφv, lintegral_indicator_one hl]`. Simplify using `only [ENNReal.coe_one, one_mul, a]`. Conclude with `(ENNReal.ofReal_toReal (hfin v).ne).symm`. Establish `hHP` using `GlobalTheory.CompanionTheory.SW.EulerPos.hasProd_of_tail (fun v => ∫⁻ X, φ v X ∂(c v • m v)) a S hLfin (fun _ => ENNReal.toReal_nonneg) hoff hsum`.

Use `⟨?_, hHP.multipliable, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Conclude with `GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b n M S Φi φ hΦi hφ`. Express the relevant statement in the definitionally equal form `∫⁻ X, Φ X ∂I = (∫⁻ X, Φi X ∂(cinf • minf)) * ∏' v, ∫⁻ X, φ v X ∂(c v • m v)`. Establish `h1 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1` using `by exact_mod_cast hcS`.

Rewrite using `[hHP.tprod_eq, hΦ, hEP S hS₀ Φi φ hΦi hφ, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, Finset.prod_congr rfl fun v _ => hLB v, Finset.prod_mul_distrib]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`. Simplify using the standard rewrite rules. Use `_ = _ := by ring`.
-/
theorem GlobalTheory.CompanionTheory.SW.EulerPos.euler_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → (∀ v, IsLocallyFiniteMeasure (m v)) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Measurable Φi → IsPureFin b Φf Φv → (∀ v Y, 0 ≤ (Φv v Y).re ∧ (Φv v Y).im = 0) → (∀ X, Φ X = Φi (projInf X) * ENNReal.ofReal (Φf (projFin X)).re) → Measurable Φ ∧ Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(c v • m v)) ∧ ∫⁻ X, Φ X ∂I = (∫⁻ X, Φi X ∂(cinf • minf)) * ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(c v • m v) := by
  intro F E _ _ _ _ _ σ hCM d b n M I minf m hEu hm cinf c hc Φ Φi Φf Φv hΦi hpure hpos hprod
  classical
  obtain ⟨hpi, hpf, hpv, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hCM n M
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hCM n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hCM n M v
  obtain ⟨hfin, hsum, S₀, hEP⟩ := hEu
  obtain ⟨-, -, -, -, -, -, -, S₁, hS₁⟩ := GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hc hc
  let S : Finset (HeightOneSpectrum (𝓞 F)) :=
    (S₀ ∪ S₁) ∪ (Filter.eventually_cofinite.1 hpure.2.1).toFinset
  have hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (by simpa using h))
  have hS₀ : S₀ ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hS₁S : S₁ ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  obtain ⟨hc1, hcS⟩ := hS₁ S hS₁S
  let φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞ :=
    fun v X => ENNReal.ofReal (Φv v X).re
  have hcv : ∀ v, Continuous (Φv v) := fun v => (hpure.1 v).1.continuous
  have hφ : ∀ v, Measurable (φ v) := fun v =>
    ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp (hcv v).measurable)
  have hΦ : Φ = pureL b S Φi φ := by
    funext X
    rw [hprod X, hpure.2.2 (projFin X), GlobalTheory.CompanionTheory.SW.EulerPos.finprod_eq_indicator b Φv S hS X]
    unfold pureL
    by_cases hX : X ∈ intOff b S
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX,
        GlobalTheory.CompanionTheory.SW.EulerPos.ofReal_re_prod S _ fun v => hpos v _]
    · simp [Set.indicator_of_notMem hX]
  have hBfin : ∀ v, ∫⁻ X, φ v X ∂(m v) ≠ ⊤ := by
    intro v
    haveI := hm v
    have hi : Integrable (Φv v) (m v) :=
      (hcv v).integrable_of_hasCompactSupport (hpure.1 v).2
    exact hi.re.lintegral_lt_top.ne
  have hLB : ∀ v, ∫⁻ X, φ v X ∂(c v • m v) = (c v : ℝ≥0∞) * ∫⁻ X, φ v X ∂(m v) := by
    intro v
    rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hLfin : ∀ v, ∫⁻ X, φ v X ∂(c v • m v) ≠ ⊤ := fun v => by
    rw [hLB v]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hBfin v)
  let a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (m v (latV b v)).toReal
  have hoff : ∀ v, v ∉ S → ∫⁻ X, φ v X ∂(c v • m v) = ENNReal.ofReal (a v) := by
    intro v hv
    have hl : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
      (hlat v).2.measurableSet
    have hφv : φ v = (latV b v).indicator 1 := by
      funext X
      simp only [φ, hS v hv]
      by_cases hX : X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))
      · simp [Set.indicator_of_mem hX]
      · simp [Set.indicator_of_notMem hX]
    rw [hLB v, hc1 v hv, hφv, lintegral_indicator_one hl]
    simp only [ENNReal.coe_one, one_mul, a]
    exact (ENNReal.ofReal_toReal (hfin v).ne).symm
  have hHP := GlobalTheory.CompanionTheory.SW.EulerPos.hasProd_of_tail (fun v => ∫⁻ X, φ v X ∂(c v • m v)) a S hLfin
    (fun _ => ENNReal.toReal_nonneg) hoff hsum
  refine ⟨?_, hHP.multipliable, ?_⟩
  · rw [hΦ]
    exact GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b n M S Φi φ hΦi hφ
  · change ∫⁻ X, Φ X ∂I = (∫⁻ X, Φi X ∂(cinf • minf)) * ∏' v, ∫⁻ X, φ v X ∂(c v • m v)
    have h1 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hcS
    rw [hHP.tprod_eq, hΦ, hEP S hS₀ Φi φ hΦi hφ, lintegral_smul_measure, ENNReal.smul_def,
      smul_eq_mul, Finset.prod_congr rfl fun v _ => hLB v, Finset.prod_mul_distrib]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) * ((∫⁻ X, Φi X ∂minf) *
            (∏ v ∈ S, ∫⁻ X, φ v X ∂(m v)) *
            ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal)) := by
          rw [h1]; simp
      _ = _ := by ring
