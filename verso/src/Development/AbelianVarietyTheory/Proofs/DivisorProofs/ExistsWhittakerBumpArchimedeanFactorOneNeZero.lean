import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `hs : Continuous (fun z : Cinf E => sInf E z)` using `((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))`. Conclude with `continuous_subtype_val.comp ((GroundTheory.Global.continuous_adelicChar (K := E)).comp hs)`.
-/
theorem continuous_psiInf : Continuous (psiInf (E := E)) := by
  have hs : Continuous (fun z : Cinf E => sInf E z) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact continuous_subtype_val.comp ((GroundTheory.Global.continuous_adelicChar (K := E)).comp hs)

/- English proof (translation)
Simplify using `[psiInf, map_zero]`.
-/
theorem psiInf_zero : psiInf (0 : Cinf E) = 1 := by
  simp [psiInf, map_zero]

variable {E} {n : ℕ}

/- English proof (translation)
Unfold `sdM`. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (continuous_apply j).comp (continuous_apply i)`.
-/
theorem continuous_sdM_of : Continuous fun x : Lie E n => sdM (Matrix.of x) := by
  unfold sdM
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_apply j).comp (continuous_apply i)

/- English proof (translation)
Unfold `sdM`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `(Finset.mem_filter.1 hj).2`. Conclude with `Matrix.one_apply_ne fun e => by subst e; omega`.
-/
theorem sdM_one : sdM (1 : Matrix (Fin n) (Fin n) (Cinf E)) = 0 := by
  unfold sdM
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  have hj' := (Finset.mem_filter.1 hj).2
  exact Matrix.one_apply_ne fun e => by subst e; omega

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun t : Vp E n => nu t i j`. Distinguish the cases in `hij : i < j`. Simplify using `only [nu, Matrix.of_apply, dif_pos hij]`. Conclude with `continuous_apply _`.

Simplify using `only [nu, Matrix.of_apply, dif_neg hij]`. Conclude with `continuous_const`.
-/
theorem continuous_toL_nu : Continuous fun t : Vp E n => toL (nu t) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun t : Vp E n => nu t i j
  by_cases hij : i < j
  · simp only [nu, Matrix.of_apply, dif_pos hij]
    exact continuous_apply _
  · simp only [nu, Matrix.of_apply, dif_neg hij]
    exact continuous_const

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i < j`. Simplify using `[nu, hij, Matrix.one_apply, hij.ne]`. Simplify using `[nu, hij, Matrix.one_apply]`.
-/
theorem nu_zero : nu (0 : Vp E n) = 1 := by
  ext i j
  by_cases hij : i < j
  · simp [nu, hij, Matrix.one_apply, hij.ne]
  · simp [nu, hij, Matrix.one_apply]

/- English proof (translation)
Use `set h : Lie E n → ℝ := fun x => (psiInf (-sdM (Matrix.of x))).re with hh`. Establish `hc : Continuous h` using `Complex.continuous_re.comp ((continuous_psiInf E).comp continuous_sdM_of.neg)`. Establish `hof : Matrix.of (oneL E n) = 1` using `Matrix.of.apply_symm_apply _`. Establish `h1 : h (oneL E n) = 1`. Simplify using `only [hh, hof, sdM_one, neg_zero, psiInf_zero, Complex.one_re]`.

Establish `hU : {x | 0 < h x} ∩ invSet E n ∈ nhds (oneL E n)` using `Filter.inter_mem ((isOpen_lt continuous_const hc).mem_nhds (by simp [h1])) (isOpen_invSet.mem_nhds (by change IsUnit (Matrix.of (oneL E n)); rw [hof]; exact isUnit_one))`. Take `⟨f, hfs, hfc, hfd, hfr, hf1⟩` from `exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU`. Use `⟨f, hfd, hfc, hfs.trans Set.inter_subset_right, ?_⟩` and prove the remaining obligations. Use `set φ : Vp E n → Lie E n := fun t => toL (nu t) with hφ`. Establish `hφc : Continuous φ` using `continuous_toL_nu`.

Use `set ψ : Lie E n → Vp E n := fun x p => x p.1.1 p.1.2 with hψ`. Establish `hψc : Continuous ψ` using `continuous_pi fun p => (continuous_apply p.1.2).comp (continuous_apply p.1.1)`. Establish `hψφ : ∀ t, ψ (φ t) = t` using `fun t => by`. Use function extensionality and compare the values at `p`. Express the relevant statement in the definitionally equal form `nu t p.1.1 p.1.2 = t p`.

Simplify using `[nu, p.2]`. Establish `hfφ : HasCompactSupport (fun t => f (φ t))`. Use `HasCompactSupport.intro ((hfc.isCompact).image hψc) fun t ht => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `ht ⟨φ t, subset_tsupport _ hne, hψφ t⟩`.

Establish `hsd : ∀ t, sdM (nu t) = sdM (Matrix.of (φ t))` using `fun t => by`. Rewrite using `[hφ]`. Simplify using `only [toL, Equiv.apply_symm_apply]`. Establish `hb : bumpInf f (oneL E n) = ∫ t : Vp E n, (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t)))`. Rewrite using `[bumpInf, hof]`.

Simplify using `only [Matrix.mul_one, hsd]`. Both sides reduce to the same expression. Use `set G : Vp E n → ℂ := fun t => (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) with hG`. Establish `hGc : Continuous G` using `(Complex.continuous_ofReal.comp (hfd.continuous.comp hφc)).mul ((continuous_psiInf E).comp (continuous_sdM_of.neg.comp hφc))`. Establish `hGs : HasCompactSupport G` using `(hfφ.comp_left Complex.ofReal_zero).mul_right`.

Establish `hint : Integrable G` using `hGc.integrable_of_hasCompactSupport hGs`. Establish `hre : (∫ t, G t).re = ∫ t, f (φ t) * h (φ t)`. Use `(Complex.reCLM.integral_comp_comm hint).symm` as an intermediate fact. Simplify using `only [Complex.reCLM_apply] at this`. Rewrite using `[this]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Simplify using `[hG, hh, Complex.re_ofReal_mul]`. Use `haveI : (volume : Measure (InfinitePlace E → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _`. Use `haveI : (volume : Measure (Vp E n)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _`.

Establish `hpos : 0 < ∫ t, f (φ t) * h (φ t)`. Use `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Vp E n)) ((hfd.continuous.comp hφc).mul (hc.comp hφc)) hfφ.mul_right (fun t => ?_) ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ f (φ t)` using `(hfr ⟨φ t, rfl⟩).1`. Distinguish the cases in `hz : f (φ t) = 0`. Simplify using `[hz]`.

Conclude with `mul_nonneg h0 (hfs (subset_tsupport _ hz)).1.le`. Establish `: φ 0 = oneL E n` using `by rw [hφ]; simp only [nu_zero]`. Simplify using `[this, hf1, h1]`. Introduce `h0`. Rewrite `h0` using `[hb]`.

Rewrite `hre` using `[h0, Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bumpInf_oneL_ne_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) :
    ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
      bumpInf f (oneL E n) ≠ 0 := by
  classical
  set h : Lie E n → ℝ := fun x => (psiInf (-sdM (Matrix.of x))).re with hh
  have hc : Continuous h :=
    Complex.continuous_re.comp ((continuous_psiInf E).comp continuous_sdM_of.neg)
  have hof : Matrix.of (oneL E n) = 1 := Matrix.of.apply_symm_apply _
  have h1 : h (oneL E n) = 1 := by
    simp only [hh, hof, sdM_one, neg_zero, psiInf_zero, Complex.one_re]
  have hU : {x | 0 < h x} ∩ invSet E n ∈ nhds (oneL E n) :=
    Filter.inter_mem ((isOpen_lt continuous_const hc).mem_nhds (by simp [h1]))
      (isOpen_invSet.mem_nhds (by change IsUnit (Matrix.of (oneL E n)); rw [hof]; exact isUnit_one))
  obtain ⟨f, hfs, hfc, hfd, hfr, hf1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  refine ⟨f, hfd, hfc, hfs.trans Set.inter_subset_right, ?_⟩
  set φ : Vp E n → Lie E n := fun t => toL (nu t) with hφ
  have hφc : Continuous φ := continuous_toL_nu
  set ψ : Lie E n → Vp E n := fun x p => x p.1.1 p.1.2 with hψ
  have hψc : Continuous ψ := continuous_pi fun p => (continuous_apply p.1.2).comp (continuous_apply p.1.1)
  have hψφ : ∀ t, ψ (φ t) = t := fun t => by
    funext p
    change nu t p.1.1 p.1.2 = t p
    simp [nu, p.2]
  have hfφ : HasCompactSupport (fun t => f (φ t)) := by
    refine HasCompactSupport.intro ((hfc.isCompact).image hψc) fun t ht => ?_
    by_contra hne
    exact ht ⟨φ t, subset_tsupport _ hne, hψφ t⟩
  have hsd : ∀ t, sdM (nu t) = sdM (Matrix.of (φ t)) := fun t => by
    rw [hφ]; simp only [toL, Equiv.apply_symm_apply]
  have hb : bumpInf f (oneL E n) = ∫ t : Vp E n, (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) := by
    rw [bumpInf, hof]
    simp only [Matrix.mul_one, hsd]
    rfl
  set G : Vp E n → ℂ := fun t => (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) with hG
  have hGc : Continuous G :=
    (Complex.continuous_ofReal.comp (hfd.continuous.comp hφc)).mul
      ((continuous_psiInf E).comp (continuous_sdM_of.neg.comp hφc))
  have hGs : HasCompactSupport G := (hfφ.comp_left Complex.ofReal_zero).mul_right
  have hint : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  have hre : (∫ t, G t).re = ∫ t, f (φ t) * h (φ t) := by
    have := (Complex.reCLM.integral_comp_comm hint).symm
    simp only [Complex.reCLM_apply] at this
    rw [this]
    congr 1
    funext t
    simp [hG, hh, Complex.re_ofReal_mul]
  haveI : (volume : Measure (InfinitePlace E → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  haveI : (volume : Measure (Vp E n)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  have hpos : 0 < ∫ t, f (φ t) * h (φ t) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Vp E n))
      ((hfd.continuous.comp hφc).mul (hc.comp hφc)) hfφ.mul_right (fun t => ?_) ?_
    · have h0 : 0 ≤ f (φ t) := (hfr ⟨φ t, rfl⟩).1
      by_cases hz : f (φ t) = 0
      · simp [hz]
      · exact mul_nonneg h0 (hfs (subset_tsupport _ hz)).1.le
    · have : φ 0 = oneL E n := by rw [hφ]; simp only [nu_zero]
      simp [this, hf1, h1]
  intro h0
  rw [hb] at h0
  rw [h0, Complex.zero_re] at hre
  linarith

end GlobalTheory.WhitBump
