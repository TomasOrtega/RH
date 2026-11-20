import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

/- English proof (translation)
Apply `L.injective` to reduce the goal to its premises. Rewrite using `[ContinuousLinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `w`. Rewrite using `[hL, KFock.cmb_crd]`. Conclude with `(arc_eq_iff R X (arc R X)).1 rfl w`.
-/
theorem crd_inf_eq (R : RD d)
    (L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ))
    (hL : ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
      L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c)) (X : Mx F E d.m d.n) :
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) =
      L.symm (((EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv) (arc R X)) := by
  apply L.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext w
  rw [hL, KFock.cmb_crd]
  exact (arc_eq_iff R X (arc R X)).1 rfl w

/- English proof (translation)
Use `⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro' hk hc fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ N`. Use `filter_upwards [ho.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use `filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Conclude with `Set.indicator_of_notMem hx _`.
-/
theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {N : Set X} (ho : IsOpen N) (hc : IsClosed N)
    (hk : IsCompact N) : N.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro' hk hc fun x hx => ?_⟩
  · by_cases hx : x ∈ N
    · filter_upwards [ho.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact Set.indicator_of_notMem hx _

/- English proof (translation)
Take `⟨L, hL⟩` from `KFock.archEquiv d R`. Use `set Zc : Vw d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := (EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv with hZc`. Establish `hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g}` using `hf`. Take `⟨N, a, x, hx⟩` from `Submodule.mem_span_set'.1 hΦ`. Use `choose φ gg hgg hxeq using fun i => (x i).2`.

Establish `hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (arc R X))) * gg i (fin d X))`. Introduce `X`. Establish `e1 : f X = (f ∘ d.cmb) (d.crd X)` using `by simp [KFock.cmb_crd]`. Rewrite using `[e1, ← hx, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, hxeq i, smul_eq_mul]`. Use `congr 1`. Simplify using `only [pureA]`. Rewrite using `[crd_inf_eq R L hL X]`. Both sides reduce to the same expression.

Establish `hfjn : ∀ u y, f (jn R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y)`. Introduce `u y`. Rewrite using `[hfX, arc_jn, fin_jn]`. Set `Φv : Yf d → (Fin N → ℂ)` to `fun y i => gg i y`. Establish `hloc : IsLocallyConstant Φv`.

Use `(IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_` and prove the remaining obligations. Establish `h` using `Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y`. Use `filter_upwards [h] with z hz`. Use function extensionality and compare the values at `i`. Conclude with `hz i`.

Use `set K : Set (Yf d) := ⋃ i, tsupport (gg i) with hK`. Establish `hKc : IsCompact K` using `isCompact_iUnion fun i => (hgg i).2`. Take `⟨t, ht⟩` from `hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c) (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)`. Use `set Vals := t.filter (fun c => c ≠ 0) with hVals`. Establish `hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K`.

Introduce `c hc y hy`. Assume the negation of the conclusion as `hyK`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← show Φv y = c from hy]`. Use function extensionality and compare the values at `i`.

Use `show gg i y = 0`. Conclude with `image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)`. Use `haveI := hνf`. Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`. Use `haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI : BorelSpace (Yf d) := Pi.borelSpace`. Set `ψ : (Fin N → ℂ) → Vw d → ℂ` to `fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)`. Establish `hterm : ∀ c ∈ Vals, (fun X => ψ c (arc R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (fin d X)) ∈ R.fock`. Introduce `c hc`. Establish `hc0 : c ≠ 0` using `(Finset.mem_filter.1 hc).2`.

Use `set Nc : Set (Yf d) := {y | Φv y = c} with hNc`. Establish `hNo : IsOpen Nc` using `hloc.isOpen_fiber c`. Establish `hNcl : IsClosed Nc` using `hloc.isClosed_fiber c`. Establish `hNk : IsCompact Nc` using `hKc.of_isClosed_subset hNcl (hfib_sub c hc0)`. Break down `Nc.eq_empty_or_nonempty with he | hne` into its components or cases.

Establish `: (fun X => ψ c (arc R X) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) = 0`. Use function extensionality and compare the values at `X`. Rewrite using `[he, Set.indicator_empty, mul_zero]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Establish `hSB` using `indicator_mem_SB hNo hNcl hNk`. Take `⟨P, hP⟩` from `H _ hSB`. Establish `hm0 : 0 < νf.real Nc`. Rewrite using `[measureReal_def]`.

Conclude with `ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne`. Establish `hval : ∀ u, hg R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ)`. Introduce `u`. Establish `e : (fun y => f (jn R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) = Nc.indicator (fun _ => ψ c u)`. Use function extensionality and compare the values at `y`.

Distinguish the cases in `hy : y ∈ Nc`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hy, star_one, mul_one, hfjn]`. Establish `hy' : ∀ i, gg i y = c i` using `fun i => congrFun hy i`. Simplify using `only [ψ, hy']`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, star_zero, mul_zero]`.

Use `show ∫ y, f (jn R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _`. Rewrite using `[e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]`. Establish `hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) * (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)))`. Introduce `u`. Rewrite using `[← hP u, hval u]`.

Establish `: (νf.real Nc : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hm0.ne'`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (fun X => ψ c (arc R X) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) = ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((arc R X i : ℝ) : ℂ)) P * (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X))`. Use function extensionality and compare the values at `X`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hψ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `Submodule.smul_mem _ _ (poly_mem R P hSB)`. Establish `hsum : f = ∑ c ∈ Vals, (fun X => ψ c (arc R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (fin d X))`. Use function extensionality and compare the values at `X`.

Rewrite using `[Finset.sum_apply, hfX]`. Distinguish the cases in `h0 : Φv (fin d X) = 0`. Establish `hz : ∀ i, gg i (fin d X) = 0` using `fun i => congrFun h0 i`. Simplify using `only [hz, mul_zero, Finset.sum_const_zero]`. Use `(Finset.sum_eq_zero fun c hc => ?_).symm` and prove the remaining obligations.

Establish `hc0 : c ≠ 0` using `(Finset.mem_filter.1 hc).2`. Establish `: fin d X ∉ {y | Φv y = c}` using `fun h => hc0 (h.symm.trans h0)`. Rewrite using `[Set.indicator_of_notMem this, mul_zero]`. Establish `hmemK : fin d X ∈ K` using `hfib_sub _ h0 rfl`. Establish `hmemt : Φv (fin d X) ∈ t`.

Use `ht hmemK` as an intermediate fact. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq] at this`. Take `⟨c, hct, hc⟩` from `this`. Rewrite using `[hc]`. Conclude with `hct`.

Establish `hmemV : Φv (fin d X) ∈ Vals` using `Finset.mem_filter.2 ⟨hmemt, h0⟩`. Rewrite using `[Finset.sum_eq_single_of_mem _ hmemV]`. Rewrite using `[Set.indicator_of_mem (show fin d X ∈ {y | Φv y = Φv (fin d X)} from rfl), mul_one]`. Introduce `c _ hne`. Establish `: fin d X ∉ {y | Φv y = c}` using `fun h => hne h.symm`.

Rewrite using `[Set.indicator_of_notMem this, mul_zero]`. Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ hterm`.
-/
theorem mem_fock_of (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (Yf d), ∃ P : MvPolynomial (Iw d) ℂ,
      ∀ u, hg R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  obtain ⟨L, hL⟩ := KFock.archEquiv d R
  set Zc : Vw d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv with hZc
  have hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ℂ)
      (g : (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      g ∈ SB (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g} := hf
  obtain ⟨N, a, x, hx⟩ := Submodule.mem_span_set'.1 hΦ
  choose φ gg hgg hxeq using fun i => (x i).2

  have hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (arc R X))) * gg i (fin d X)) := by
    intro X
    have e1 : f X = (f ∘ d.cmb) (d.crd X) := by simp [KFock.cmb_crd]
    rw [e1, ← hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hxeq i, smul_eq_mul]
    congr 1
    simp only [pureA]
    rw [crd_inf_eq R L hL X]
    rfl
  have hfjn : ∀ u y, f (jn R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y) := by
    intro u y
    rw [hfX, arc_jn, fin_jn]

  let Φv : Yf d → (Fin N → ℂ) := fun y i => gg i y
  have hloc : IsLocallyConstant Φv := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have h := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y
    filter_upwards [h] with z hz
    funext i
    exact hz i
  set K : Set (Yf d) := ⋃ i, tsupport (gg i) with hK
  have hKc : IsCompact K := isCompact_iUnion fun i => (hgg i).2
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c)
    (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)
  set Vals := t.filter (fun c => c ≠ 0) with hVals

  have hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K := by
    intro c hc y hy
    by_contra hyK
    apply hc
    rw [← show Φv y = c from hy]
    funext i
    show gg i y = 0
    exact image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace

  let ψ : (Fin N → ℂ) → Vw d → ℂ := fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)
  have hterm : ∀ c ∈ Vals, (fun X => ψ c (arc R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (fin d X)) ∈ R.fock := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    set Nc : Set (Yf d) := {y | Φv y = c} with hNc
    have hNo : IsOpen Nc := hloc.isOpen_fiber c
    have hNcl : IsClosed Nc := hloc.isClosed_fiber c
    have hNk : IsCompact Nc := hKc.of_isClosed_subset hNcl (hfib_sub c hc0)
    rcases Nc.eq_empty_or_nonempty with he | hne
    · have : (fun X => ψ c (arc R X) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) = 0 := by
        funext X
        rw [he, Set.indicator_empty, mul_zero]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    · have hSB := indicator_mem_SB hNo hNcl hNk
      obtain ⟨P, hP⟩ := H _ hSB
      have hm0 : 0 < νf.real Nc := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne
      have hval : ∀ u, hg R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ) := by
        intro u
        have e : (fun y => f (jn R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) =
            Nc.indicator (fun _ => ψ c u) := by
          funext y
          by_cases hy : y ∈ Nc
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, star_one, mul_one, hfjn]
            have hy' : ∀ i, gg i y = c i := fun i => congrFun hy i
            simp only [ψ, hy']
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, star_zero, mul_zero]
        show ∫ y, f (jn R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _
        rw [e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]
      have hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) *
          (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) := by
        intro u
        rw [← hP u, hval u]
        have : (νf.real Nc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
        field_simp
      have e2 : (fun X => ψ c (arc R X) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) =
          ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((arc R X i : ℝ) : ℂ)) P *
            (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) := by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul, hψ]
        ring
      rw [e2]
      exact Submodule.smul_mem _ _ (poly_mem R P hSB)

  have hsum : f = ∑ c ∈ Vals, (fun X => ψ c (arc R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (fin d X)) := by
    funext X
    rw [Finset.sum_apply, hfX]
    by_cases h0 : Φv (fin d X) = 0
    · have hz : ∀ i, gg i (fin d X) = 0 := fun i => congrFun h0 i
      simp only [hz, mul_zero, Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      have : fin d X ∉ {y | Φv y = c} := fun h => hc0 (h.symm.trans h0)
      rw [Set.indicator_of_notMem this, mul_zero]
    · have hmemK : fin d X ∈ K := hfib_sub _ h0 rfl
      have hmemt : Φv (fin d X) ∈ t := by
        have := ht hmemK
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
        obtain ⟨c, hct, hc⟩ := this
        rw [hc]
        exact hct
      have hmemV : Φv (fin d X) ∈ Vals := Finset.mem_filter.2 ⟨hmemt, h0⟩
      rw [Finset.sum_eq_single_of_mem _ hmemV]
      · rw [Set.indicator_of_mem (show fin d X ∈ {y | Φv y = Φv (fin d X)} from rfl), mul_one]
      · intro c _ hne
        have : fin d X ∉ {y | Φv y = c} := fun h => hne h.symm
        rw [Set.indicator_of_notMem this, mul_zero]
  rw [hsum]
  exact Submodule.sum_mem _ hterm

end PositivityTheory.SiegelWeilFormula.KFP.OswGen

end
