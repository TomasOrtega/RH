import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Establish `hc : Continuous fun ε : ℝ => ENNReal.ofReal (1 + ε)` using `ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)`. Establish `ht0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1)`. Establish `h1` using `(hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))`. Simplify using `using h1`. Establish `ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * (c * Y)) (𝓝[>] 0) (𝓝 (c * Y))`.

Establish `h1` using `ENNReal.Tendsto.mul_const (b := c * Y) ht0 (Or.inl one_ne_zero)`. Simplify using `using h1`. Conclude with `ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => by`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ti_le_of_forall_pos (x c Y : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ c * (ENNReal.ofReal (1 + ε) * Y)) : x ≤ c * Y := by
  have hc : Continuous fun ε : ℝ => ENNReal.ofReal (1 + ε) :=
    ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)
  have ht0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h1
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * (c * Y)) (𝓝[>] 0) (𝓝 (c * Y)) := by
    have h1 := ENNReal.Tendsto.mul_const (b := c * Y) ht0 (Or.inl one_ne_zero)
    simpa using h1
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => by
    calc x ≤ c * (ENNReal.ofReal (1 + ε) * Y) := h ε hε
      _ = ENNReal.ofReal (1 + ε) * (c * Y) := by ring)

/- English proof (translation)
Establish `h : ∀ j, HasCompactSupport (fun x => f x j)` using `fun j => (hf j).2`. Establish `hsub : Function.support f ⊆ ⋃ j, Function.support (fun x => f x j)`. Introduce `x hx`. Rewrite using `[Set.mem_iUnion]`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Apply `hx` to reduce the goal to its premises. Use extensionality with `j`. Simplify `hne j` using `[Function.mem_support]`. Establish `hts : tsupport f ⊆ ⋃ j, tsupport (fun x => f x j)` using `by show closure (Function.support f) ⊆ ⋃ j, closure (Function.support fun x => f x j)`.

Rewrite using `[← closure_iUnion_of_finite]`. Conclude with `closure_mono hsub`. Conclude with `IsCompact.of_isClosed_subset (isCompact_iUnion fun j => h j) (isClosed_tsupport f) hts`.
-/
theorem ti_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (hf : IsTestForm n z f) : HasCompactSupport f := by
  have h : ∀ j, HasCompactSupport (fun x => f x j) := fun j => (hf j).2
  have hsub : Function.support f ⊆ ⋃ j, Function.support (fun x => f x j) := by
    intro x hx
    rw [Set.mem_iUnion]
    by_contra hne
    push_neg at hne
    apply hx
    ext j
    simpa [Function.mem_support] using hne j
  have hts : tsupport f ⊆ ⋃ j, tsupport (fun x => f x j) := by
    show closure (Function.support f) ⊆ ⋃ j, closure (Function.support fun x => f x j)
    rw [← closure_iUnion_of_finite]
    exact closure_mono hsub
  exact IsCompact.of_isClosed_subset (isCompact_iUnion fun j => h j) (isClosed_tsupport f) hts

/- English proof (translation)
Establish `hex : ∃ c : OpenPartialHomeomorph M (V n), IsChart n z c ∧ x ∈ c.source` using `⟨e, he, hx⟩`. Rewrite using `[db, dif_pos hex]`. Take `⟨hc, hxc⟩` from `Classical.choose_spec hex`. Apply `wdb_congr` to reduce the goal to its premises. Establish `hzx : z x = e x` using `he hx`.

Establish `hzc : z x = (Classical.choose hex) x` using `hc hxc`. Establish `h1 : ∀ᶠ y in 𝓝 (z x), y ∈ e.target`. Rewrite using `[hzx]`. Conclude with `e.open_target.mem_nhds (e.map_source hx)`. Establish `h2 : ∀ᶠ y in 𝓝 (z x), y ∈ (Classical.choose hex).target`.

Rewrite using `[hzc]`. Conclude with `(Classical.choose hex).open_target.mem_nhds ((Classical.choose hex).map_source hxc)`. Establish `h3 : ∀ᶠ y in 𝓝 (z x), e.symm y ∈ (Classical.choose hex).source`. Establish `hca : ContinuousAt e.symm (z x)`. Rewrite using `[hzx]`.

Conclude with `e.continuousAt_symm (e.map_source hx)`. Apply `hca.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[hzx, e.left_inv hx]`. Conclude with `(Classical.choose hex).open_source.mem_nhds hxc`. Use `filter_upwards [h1, h2, h3] with y hy1 hy2 hy3`.

Use `show f ((Classical.choose hex).symm y) = f (e.symm y)`. Use `congr 1`. Apply `(Classical.choose hex).injOn ((Classical.choose hex).map_target hy2) hy3` to reduce the goal to its premises. Rewrite using `[(Classical.choose hex).right_inv hy2, ← hc hy3, he (e.map_target hy1), e.right_inv hy1]`.
-/
private theorem db_eq_wdb_comp_symm_of_isChart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (j : Fin n) (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) {x : M}
    (hx : x ∈ e.source) : db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have hex : ∃ c : OpenPartialHomeomorph M (V n), IsChart n z c ∧ x ∈ c.source := ⟨e, he, hx⟩
  rw [db, dif_pos hex]
  obtain ⟨hc, hxc⟩ := Classical.choose_spec hex
  apply wdb_congr
  have hzx : z x = e x := he hx
  have hzc : z x = (Classical.choose hex) x := hc hxc
  have h1 : ∀ᶠ y in 𝓝 (z x), y ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have h2 : ∀ᶠ y in 𝓝 (z x), y ∈ (Classical.choose hex).target := by
    rw [hzc]
    exact (Classical.choose hex).open_target.mem_nhds ((Classical.choose hex).map_source hxc)
  have h3 : ∀ᶠ y in 𝓝 (z x), e.symm y ∈ (Classical.choose hex).source := by
    have hca : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    apply hca.preimage_mem_nhds
    rw [hzx, e.left_inv hx]
    exact (Classical.choose hex).open_source.mem_nhds hxc
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  show f ((Classical.choose hex).symm y) = f (e.symm y)
  congr 1
  apply (Classical.choose hex).injOn ((Classical.choose hex).map_target hy2) hy3
  rw [(Classical.choose hex).right_inv hy2, ← hc hy3, he (e.map_target hy1), e.right_inv hy1]

/- English proof (translation)
Introduce `e he`. Establish `hG : ContDiffOn ℝ 2 (F ∘ e.symm) e.target` using `(hF e he).of_le (by first`. Consider the case `exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)`. Consider the case `exact WithTop.coe_le_coe.mpr le_top`. Consider the case `simp)`.

Establish `hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ (F ∘ e.symm) y) e.target` using `hG.fderiv_of_isOpen e.open_target (by norm_num)`. Establish `hW : ContDiffOn ℝ 1 (fun y => wdb n j (F ∘ e.symm) y) e.target`. Unfold `wdb`. Conclude with `((hD.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const _`. Use `hW.congr fun y hy => ?_` and prove the remaining obligations.

Use `show db n z j F (e.symm y) = wdb n j (F ∘ e.symm) y`. Rewrite using `[db_eq_wdb_comp_symm_of_isChart j F e he (e.map_target hy), he (e.map_target hy), e.right_inv hy]`.
-/
private theorem ck_one_db_of_smooth {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n} {F : M → ℂ}
    (hF : Smooth n z F) (j : Fin n) : Ck n z 1 (fun x => db n z j F x) := by
  intro e he
  have hG : ContDiffOn ℝ 2 (F ∘ e.symm) e.target := (hF e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ (F ∘ e.symm) y) e.target :=
    hG.fderiv_of_isOpen e.open_target (by norm_num)
  have hW : ContDiffOn ℝ 1 (fun y => wdb n j (F ∘ e.symm) y) e.target := by
    unfold wdb
    exact ((hD.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const _
  refine hW.congr fun y hy => ?_
  show db n z j F (e.symm y) = wdb n j (F ∘ e.symm) y
  rw [db_eq_wdb_comp_symm_of_isChart j F e he (e.map_target hy), he (e.map_target hy), e.right_inv hy]

/- English proof (translation)
Introduce `e he`. Use `((ha e he).sub ((contDiffOn_const (c := ((c : ℝ) : ℂ))).mul (hb e he))).congr fun y _ => ?_` and prove the remaining obligations. Simplify using `[Function.comp]`.
-/
private theorem smoothR_sub_const_mul {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    {a b : M → ℝ} (ha : SmoothR n z a) (hb : SmoothR n z b) (c : ℝ) :
    SmoothR n z (fun x => a x - c * b x) := by
  intro e he
  refine ((ha e he).sub ((contDiffOn_const (c := ((c : ℝ) : ℂ))).mul (hb e he))).congr
    fun y _ => ?_
  simp [Function.comp]

/- English proof (translation)
Introduce `X ph F0 h hph hlev hF0 hh hdom hI f hf`. Establish `hz` using `X.isLocalHomeomorph`. Apply `ti_le_of_forall_pos` to reduce the goal to its premises. Introduce `ε hε`. Establish `hck2 : Ck n X.z 2 F0` using `fun e he => (hF0 e he).of_le (by first`.

Consider the case `exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)`. Consider the case `exact WithTop.coe_le_coe.mpr le_top`. Consider the case `simp)`. Establish `hcj : ∀ j, Continuous fun x => db n X.z j F0 x`. Introduce `j`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨e, hxe, hze⟩` from `hz x`. Establish `he : IsChart n X.z e` using `fun y _ => by rw [hze]`. Establish `hC` using `(ck_one_db_of_smooth hF0 j e he).continuousOn`.

Establish `h1 : ContinuousOn (((fun x => db n X.z j F0 x) ∘ e.symm) ∘ e) e.source` using `hC.comp e.continuousOn (fun y hy => e.map_source hy)`. Establish `h2 : ContinuousOn (fun x => db n X.z j F0 x) e.source` using `h1.congr fun y hy => by simp [e.left_inv hy]`. Conclude with `h2.continuousAt (e.open_source.mem_nhds hxe)`. Establish `hcont : Continuous (dbarF n X.z F0)` using `by show Continuous fun x => WithLp.toLp 2 (fun j => db n X.z j F0 x) first`. Consider the case `exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi hcj)`.

Consider the case `exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℂ)).comp (continuous_pi hcj)`. Consider the case `fun_prop`. Take `⟨ph', ψ, e', U, hph', hψ, he', hcut, hU, hCU, hUeq, hle, hlevi, hL2⟩` from `hCh X ph (dbarF n X.z F0) (tsupport f) ε hph hcont (ti_hasCompactSupport n X.z f hf) hε`. Establish `hprim` using `hP X.z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hle hlevi hI`. Establish `hclos` using `hC X.z hz e' ph' ψ (dbarF n X.z F0) _ ε he' hph' hψ hcut hL2 hI hε hprim`.

Establish `hw1 : SmoothR n X.z (w1 ph' ψ)` using `smoothR_sub_const_mul hph' hψ 2`. Establish `hw2 : SmoothR n X.z (w2 ph' ψ)`. Establish `h1` using `smoothR_sub_const_mul hph' hψ 1`. Simplify using `only [one_mul] at h1`. Conclude with `h1`.

Establish `hWS0 : IsWeakS n X.z (dbarF n X.z F0) 0`. Establish `h1` using `hWS X.z hz (dbarF n X.z F0) (fun j => ck_one_db_of_smooth hF0 j)`. Establish `h0 : sbar n X.z (dbarF n X.z F0) = 0`. Use function extensionality and compare the values at `x`. Conclude with `hSD X.z hz F0 hck2 x`.

Rewrite `h1` using `[h0]`. Then use the resulting hypothesis. Take `⟨hT, f₁, hf₁, hS1, hadj, hip⟩` from `hS X.z hz (w1 ph' ψ) (w2 ph' ψ) (dbarF n X.z F0) f hw1 hw2 hL2 hWS0 hf`. Take `⟨hloc1, hloc2⟩` from `hL X.z hz ph ph' ψ U f hU hf hCU hUeq`. Establish `hfin` using `hclos f₁ (tstar n X.z (w1 ph' ψ) (w2 ph' ψ) f) hf₁ hT hadj hS1`. Rewrite `hfin` using `[← hip, hloc1, hloc2]`.

Conclude with `hfin`.
-/
theorem testIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCh : ChoiceStatement n M) (hP : PrimedIneqStatement n M)
    (hC : ClosureIneqStatement n M) (hS : SplitTestStatement n M) (hL : LocalityStatement n M)
    (hWS : WeakSSmoothStatement n M) (hSD : SbarDbarStatement n M) : TestIneqStatement n M := by
  intro X ph F0 h hph hlev hF0 hh hdom hI f hf
  have hz := X.isLocalHomeomorph
  apply ti_le_of_forall_pos
  intro ε hε
  have hck2 : Ck n X.z 2 F0 := fun e he => (hF0 e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hcj : ∀ j, Continuous fun x => db n X.z j F0 x := by
    intro j
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hxe, hze⟩ := hz x
    have he : IsChart n X.z e := fun y _ => by rw [hze]
    have hC := (ck_one_db_of_smooth hF0 j e he).continuousOn
    have h1 : ContinuousOn (((fun x => db n X.z j F0 x) ∘ e.symm) ∘ e) e.source :=
      hC.comp e.continuousOn (fun y hy => e.map_source hy)
    have h2 : ContinuousOn (fun x => db n X.z j F0 x) e.source :=
      h1.congr fun y hy => by simp [e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  have hcont : Continuous (dbarF n X.z F0) := by
    show Continuous fun x => WithLp.toLp 2 (fun j => db n X.z j F0 x)
    first
      | exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | fun_prop
  obtain ⟨ph', ψ, e', U, hph', hψ, he', hcut, hU, hCU, hUeq, hle, hlevi, hL2⟩ :=
    hCh X ph (dbarF n X.z F0) (tsupport f) ε hph hcont (ti_hasCompactSupport n X.z f hf) hε
  have hprim := hP X.z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hle hlevi hI
  have hclos := hC X.z hz e' ph' ψ (dbarF n X.z F0) _ ε he' hph' hψ hcut hL2 hI hε hprim
  have hw1 : SmoothR n X.z (w1 ph' ψ) := smoothR_sub_const_mul hph' hψ 2
  have hw2 : SmoothR n X.z (w2 ph' ψ) := by
    have h1 := smoothR_sub_const_mul hph' hψ 1
    simp only [one_mul] at h1
    exact h1
  have hWS0 : IsWeakS n X.z (dbarF n X.z F0) 0 := by
    have h1 := hWS X.z hz (dbarF n X.z F0) (fun j => ck_one_db_of_smooth hF0 j)
    have h0 : sbar n X.z (dbarF n X.z F0) = 0 := by
      funext x
      exact hSD X.z hz F0 hck2 x
    rwa [h0] at h1
  obtain ⟨hT, f₁, hf₁, hS1, hadj, hip⟩ :=
    hS X.z hz (w1 ph' ψ) (w2 ph' ψ) (dbarF n X.z F0) f hw1 hw2 hL2 hWS0 hf
  obtain ⟨hloc1, hloc2⟩ := hL X.z hz ph ph' ψ U f hU hf hCU hUeq
  have hfin := hclos f₁ (tstar n X.z (w1 ph' ψ) (w2 ph' ψ) f) hf₁ hT hadj hS1
  rw [← hip, hloc1, hloc2] at hfin
  exact hfin

end

end ReciprocityTheory.L2DbarEstimates.F
