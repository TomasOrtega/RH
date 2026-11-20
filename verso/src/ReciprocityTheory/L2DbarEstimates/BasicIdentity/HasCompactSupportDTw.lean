import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Introduce `e he`. Establish `hg : ContDiff ℝ k (fun c : ℂ => ((Real.exp (-c.re) : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff.neg)`. Use `(hg.comp_contDiffOn (hph e he)).congr fun w _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem ck_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (hph : CkR n z k ph) :
    Ck n z k (fun x => (Real.exp (-ph x) : ℂ)) := by
  intro e he
  have hg : ContDiff ℝ k (fun c : ℂ => ((Real.exp (-c.re) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff.neg)
  refine (hg.comp_contDiffOn (hph e he)).congr fun w _ => ?_
  simp

/- English proof (translation)
Rewrite using `[he hx]`. Conclude with `((hf e he).differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds (e.map_source hx))`.
-/
private theorem differentiableAt_comp_chart_symm_of_ck_one {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) : DifferentiableAt ℝ (f ∘ e.symm) (z x) := by
  rw [he hx]
  exact ((hf e he).differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))

/- English proof (translation)
Distinguish the cases in `h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Simplify using `only [db, dif_pos h]`. Take `⟨he, hx⟩` from `Classical.choose_spec h`. Use `set e := Classical.choose h`. Establish `hzx : z x = e x` using `he hx`.

Establish `hex : e.symm (z x) = x`. Rewrite using `[hzx]`. Conclude with `e.left_inv hx`. Establish `hP` using `differentiableAt_comp_chart_symm_of_ck_one n z (fun y => (ph y : ℂ)) hph e he x hx`. Establish `hQ : DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x)`.

Use `Complex.reCLM.differentiableAt.comp (z x) hP` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `h1 : fderiv ℝ ((fun y => (Real.exp (-ph y) : ℂ)) ∘ e.symm) (z x) = Complex.ofRealCLM.comp (Real.exp (-ph (e.symm (z x))) • -(fderiv ℝ (fun w => ph (e.symm w)) (z x)))` using `(Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt.neg.exp).fderiv`. Establish `h2 : fderiv ℝ ((fun y => (ph y : ℂ)) ∘ e.symm) (z x) = Complex.ofRealCLM.comp (fderiv ℝ (fun w => ph (e.symm w)) (z x))` using `(Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt).fderiv`. Simplify using `only [wdb]`.

Rewrite using `[h1, h2]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, Complex.ofRealCLM_apply, smul_eq_mul, hex]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[db, dif_neg h]`.
-/
theorem db_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n)
    (x : M) :
    db n z j (fun y => (Real.exp (-ph y) : ℂ)) x =
      -((Real.exp (-ph x) : ℂ) * db n z j (fun y => (ph y : ℂ)) x) := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hex : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hP := differentiableAt_comp_chart_symm_of_ck_one n z (fun y => (ph y : ℂ)) hph e he x hx
    have hQ : DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x) := by
      have := Complex.reCLM.differentiableAt.comp (z x) hP
      simpa [Function.comp_def] using this
    have h1 : fderiv ℝ ((fun y => (Real.exp (-ph y) : ℂ)) ∘ e.symm) (z x) =
        Complex.ofRealCLM.comp (Real.exp (-ph (e.symm (z x))) •
          -(fderiv ℝ (fun w => ph (e.symm w)) (z x))) :=
      (Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt.neg.exp).fderiv
    have h2 : fderiv ℝ ((fun y => (ph y : ℂ)) ∘ e.symm) (z x) =
        Complex.ofRealCLM.comp (fderiv ℝ (fun w => ph (e.symm w)) (z x)) :=
      (Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt).fderiv
    simp only [wdb]
    rw [h1, h2]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Complex.ofRealCLM_apply, smul_eq_mul, hex]
    push_cast
    ring
  · simp [db, dif_neg h]

/- English proof (translation)
Establish `h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source` using `⟨e, he, hx⟩`. Rewrite using `[d, dif_pos h]`. Take `⟨he', hx'⟩` from `Classical.choose_spec h`. Use `set e' := Classical.choose h`. Establish `hzx : z x = e x` using `he hx`.

Establish `hzx' : z x = e' x` using `he' hx'`. Establish `hev : ∀ᶠ w in nhds (z x), e'.symm w = e.symm w`. Establish `ht : ∀ᶠ w in nhds (z x), w ∈ e.target`. Rewrite using `[hzx]`. Conclude with `e.open_target.mem_nhds (e.map_source hx)`.

Establish `ht' : ∀ᶠ w in nhds (z x), w ∈ e'.target`. Rewrite using `[hzx']`. Conclude with `e'.open_target.mem_nhds (e'.map_source hx')`. Establish `hsrc : ∀ᶠ w in nhds (z x), e'.symm w ∈ e.source`. Establish `hc : ContinuousAt e'.symm (z x)`.

Rewrite using `[hzx']`. Conclude with `e'.continuousAt_symm (e'.map_source hx')`. Establish `hx0 : e'.symm (z x) = x`. Rewrite using `[hzx']`. Conclude with `e'.left_inv hx'`.

Conclude with `hc.preimage_mem_nhds (by rw [hx0]; exact e.open_source.mem_nhds hx)`. Use `filter_upwards [ht, ht', hsrc] with w hw hw' hws`. Apply `e.injOn hws (e.map_target hw)` to reduce the goal to its premises. Rewrite using `[e.right_inv hw, ← he hws, he' (e'.map_target hw'), e'.right_inv hw']`. Establish `hf : u ∘ e'.symm =ᶠ[nhds (z x)] u ∘ e.symm` using `hev.mono fun w hw => by`.

Simplify using `only [Function.comp_apply, hw]`. Simplify using `only [wd, hf.fderiv_eq]`.
-/
private theorem d_eq_wd_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) : d n z j u x = wd n j (u ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  rw [d, dif_pos h]
  obtain ⟨he', hx'⟩ := Classical.choose_spec h
  set e' := Classical.choose h

  have hzx : z x = e x := he hx
  have hzx' : z x = e' x := he' hx'
  have hev : ∀ᶠ w in nhds (z x), e'.symm w = e.symm w := by
    have ht : ∀ᶠ w in nhds (z x), w ∈ e.target := by
      rw [hzx]
      exact e.open_target.mem_nhds (e.map_source hx)
    have ht' : ∀ᶠ w in nhds (z x), w ∈ e'.target := by
      rw [hzx']
      exact e'.open_target.mem_nhds (e'.map_source hx')
    have hsrc : ∀ᶠ w in nhds (z x), e'.symm w ∈ e.source := by
      have hc : ContinuousAt e'.symm (z x) := by
        rw [hzx']
        exact e'.continuousAt_symm (e'.map_source hx')
      have hx0 : e'.symm (z x) = x := by
        rw [hzx']
        exact e'.left_inv hx'
      exact hc.preimage_mem_nhds (by rw [hx0]; exact e.open_source.mem_nhds hx)
    filter_upwards [ht, ht', hsrc] with w hw hw' hws
    apply e.injOn hws (e.map_target hw)
    rw [e.right_inv hw, ← he hws, he' (e'.map_target hw'), e'.right_inv hw']
  have hf : u ∘ e'.symm =ᶠ[nhds (z x)] u ∘ e.symm := hev.mono fun w hw => by
    simp only [Function.comp_apply, hw]
  simp only [wd, hf.fderiv_eq]

/- English proof (translation)
Establish `hD : ContDiffOn ℝ k (fun y => fderiv ℝ U y) s` using `hU.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)`. Establish `h1` using `hD.clm_apply (contDiffOn_const (c := bas n j))`. Establish `h2` using `hD.clm_apply (contDiffOn_const (c := Complex.I • bas n j))`. Conclude with `(h1.sub (contDiffOn_const.mul h2)).div_const 2`.
-/
private theorem contDiffOn_wd_of_contDiffOn_succ (n : ℕ) (j : Fin n) (k : ℕ) (U : V n → ℂ) (s : Set (V n))
    (hs : IsOpen s) (hU : ContDiffOn ℝ ((k + 1 : ℕ)) U s) : ContDiffOn ℝ k (wd n j U) s := by
  have hD : ContDiffOn ℝ k (fun y => fderiv ℝ U y) s :=
    hU.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)
  have h1 := hD.clm_apply (contDiffOn_const (c := bas n j))
  have h2 := hD.clm_apply (contDiffOn_const (c := Complex.I • bas n j))
  exact (h1.sub (contDiffOn_const.mul h2)).div_const 2

/- English proof (translation)
Introduce `e he`. Establish `key : ∀ w ∈ e.target, (dTw n z ph j u ∘ e.symm) w = wd n j (u ∘ e.symm) w - (u ∘ e.symm) w * wd n j ((fun y => (ph y : ℂ)) ∘ e.symm) w`. Introduce `w hw`. Establish `hs : e.symm w ∈ e.source` using `e.map_target hw`. Establish `hz : z (e.symm w) = w`.

Rewrite using `[he hs]`. Conclude with `e.right_inv hw`. Simplify using `only [Function.comp_apply, dTw]`. Rewrite using `[d_eq_wd_comp_chart_symm n z j u e he _ hs, d_eq_wd_comp_chart_symm n z j _ e he _ hs, hz]`. Use `ContDiffOn.congr ?_ key` and prove the remaining obligations.

Conclude with `(contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hu e he)).sub (((hu e he).of_le (by exact_mod_cast Nat.le_succ k)).mul (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hph e he)))`.
-/
theorem ck_dTw {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hph : CkR n z (k + 1) ph) (hu : Ck n z (k + 1) u) : Ck n z k (dTw n z ph j u) := by
  intro e he
  have key : ∀ w ∈ e.target, (dTw n z ph j u ∘ e.symm) w =
      wd n j (u ∘ e.symm) w - (u ∘ e.symm) w * wd n j ((fun y => (ph y : ℂ)) ∘ e.symm) w := by
    intro w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    have hz : z (e.symm w) = w := by
      rw [he hs]
      exact e.right_inv hw
    simp only [Function.comp_apply, dTw]
    rw [d_eq_wd_comp_chart_symm n z j u e he _ hs, d_eq_wd_comp_chart_symm n z j _ e he _ hs, hz]
  refine ContDiffOn.congr ?_ key
  exact (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hu e he)).sub
    (((hu e he).of_le (by exact_mod_cast Nat.le_succ k)).mul
      (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hph e he)))

/- English proof (translation)
Distinguish the cases in `h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Rewrite using `[d, dif_pos h]`. Take `⟨he, hx⟩` from `Classical.choose_spec h`. Use `set e := Classical.choose h`. Establish `hzx : z x = e x` using `he hx`.

Establish `hc : ContinuousAt e.symm (z x)`. Rewrite using `[hzx]`. Conclude with `e.continuousAt_symm (e.map_source hx)`. Establish `hx0 : e.symm (z x) = x`. Rewrite using `[hzx]`.

Conclude with `e.left_inv hx`. Establish `hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ)`. Establish `ht` using `hc.tendsto`. Rewrite `ht` using `[hx0]`. Conclude with `ht.eventually hu`.

Simplify using `only [wd, hev.fderiv_eq]`. Simplify using the standard rewrite rules. Rewrite using `[d, dif_neg h]`.
-/
private theorem d_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (x : M) (hu : u =ᶠ[nhds x] 0) : d n z j u x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · rw [d, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hc : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    have hx0 : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ) := by
      have ht := hc.tendsto
      rw [hx0] at ht
      exact ht.eventually hu
    simp only [wd, hev.fderiv_eq]
    simp
  · rw [d, dif_neg h]

/- English proof (translation)
Distinguish the cases in `h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source`. Rewrite using `[db, dif_pos h]`. Take `⟨he, hx⟩` from `Classical.choose_spec h`. Use `set e := Classical.choose h`. Establish `hzx : z x = e x` using `he hx`.

Establish `hc : ContinuousAt e.symm (z x)`. Rewrite using `[hzx]`. Conclude with `e.continuousAt_symm (e.map_source hx)`. Establish `hx0 : e.symm (z x) = x`. Rewrite using `[hzx]`.

Conclude with `e.left_inv hx`. Establish `hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ)`. Establish `ht` using `hc.tendsto`. Rewrite `ht` using `[hx0]`. Conclude with `ht.eventually hu`.

Simplify using `only [wdb, hev.fderiv_eq]`. Simplify using the standard rewrite rules. Rewrite using `[db, dif_neg h]`.
-/
private theorem db_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (x : M) (hu : u =ᶠ[nhds x] 0) : db n z j u x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · rw [db, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hc : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    have hx0 : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ) := by
      have ht := hc.tendsto
      rw [hx0] at ht
      exact ht.eventually hu
    simp only [wdb, hev.fderiv_eq]
    simp
  · rw [db, dif_neg h]

/- English proof (translation)
Use `closure_minimal (fun x hx => ?_) (isClosed_tsupport u)` and prove the remaining obligations. Assume the negation of the conclusion as `hxu`. Apply `hx` to reduce the goal to its premises. Establish `hu0 : u =ᶠ[nhds x] 0` using `notMem_tsupport_iff_eventuallyEq.1 hxu`. Simplify using `only [dTw]`.

Rewrite using `[d_eq_zero_of_eventuallyEq_zero n z j u x hu0, hu0.eq_of_nhds]`. Simplify using the standard rewrite rules.
-/
theorem tsupport_dTw_subset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (u : M → ℂ) :
    tsupport (dTw n z ph j u) ⊆ tsupport u := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport u)
  by_contra hxu
  apply hx
  have hu0 : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxu
  simp only [dTw]
  rw [d_eq_zero_of_eventuallyEq_zero n z j u x hu0, hu0.eq_of_nhds]
  simp

/- English proof (translation)
Use `hu.mono' fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hxu`. Conclude with `hx (d_eq_zero_of_eventuallyEq_zero n z j u x (notMem_tsupport_iff_eventuallyEq.1 hxu))`.
-/
theorem hasCompactSupport_d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (d n z j u) := by
  refine hu.mono' fun x hx => ?_
  by_contra hxu
  exact hx (d_eq_zero_of_eventuallyEq_zero n z j u x (notMem_tsupport_iff_eventuallyEq.1 hxu))

/- English proof (translation)
Use `hu.mono' fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hxu`. Conclude with `hx (db_eq_zero_of_eventuallyEq_zero n z j u x (notMem_tsupport_iff_eventuallyEq.1 hxu))`.
-/
theorem hasCompactSupport_db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (db n z j u) := by
  refine hu.mono' fun x hx => ?_
  by_contra hxu
  exact hx (db_eq_zero_of_eventuallyEq_zero n z j u x (notMem_tsupport_iff_eventuallyEq.1 hxu))

/- English proof (translation)
Conclude with `hu.mono' ((subset_tsupport _).trans (tsupport_dTw_subset n z ph j u))`.
-/
theorem hasCompactSupport_dTw {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (dTw n z ph j u) := by
  exact hu.mono' ((subset_tsupport _).trans (tsupport_dTw_subset n z ph j u))

end

end ReciprocityTheory.L2DbarEstimates.E
