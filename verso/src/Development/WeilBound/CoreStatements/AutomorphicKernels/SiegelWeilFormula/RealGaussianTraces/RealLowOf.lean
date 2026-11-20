import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.CpowProdOfReal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : IsTotallyReal F := hCM.1`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2`. Set `b : Module.Basis (Fin 2) F E` to `Module.finBasisOfFinrankEq F E h2`. Set `eT` to `GlobalTheory.SiegelWeilConvCompare.tensHomeo (F := F) (E := E) (Ainf F) b`.

Set `eR : Ainf F ≃ₜ (InfinitePlace F → ℝ)` to `Homeomorph.piCongrRight fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph`. Establish `hRadd : ∀ x y : InfinitePlace F → ℝ, eR.symm (x + y) = eR.symm x + eR.symm y`. Introduce `x y`. Use function extensionality and compare the values at `v`. Conclude with `(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.map_add (x v) (y v)`.

Establish `hTadd : ∀ x y : Fin 2 → Ainf F, eT.symm (x + y) = eT.symm x + eT.symm y`. Introduce `x y`. Conclude with `(Algebra.TensorProduct.basis (Ainf F) b).equivFun.symm.map_add x y`. Set `f : (Fin 2 → InfinitePlace F → ℝ) → (ι → ℂ)` to `fun x i => θ i (eT.symm (fun k => eR.symm (x k)))`. Establish `hfadd : ∀ x y, f (x + y) = f x + f y`.

Introduce `x y`. Use function extensionality and compare the values at `i`. Simplify using `only [f, Pi.add_apply]`. Rewrite using `[show (fun k => eR.symm (x k + y k)) = (fun k => eR.symm (x k)) + (fun k => eR.symm (y k)) from`. Use function extensionality and compare the values at `fun k => hRadd (x k) (y k), hTadd, map_add]`.

Set `fA : (Fin 2 → InfinitePlace F → ℝ) →+ (ι → ℂ)` to `{ toFun := f map_zero' := by`. Establish `h0` using `hfadd 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `(add_eq_left.1 h0.symm)`. Use the proof step `map_add' := hfadd }`.

Establish `hfc : Continuous fA` using `continuous_pi fun i => (hP.cont i).comp (eT.symm.continuous.comp (continuous_pi fun k => eR.symm.continuous.comp (continuous_apply k)))`. Set `L` to `fA.toRealLinearMap hfc`. Establish `hbij : Function.Bijective L`. Establish `h1 : Function.Bijective (fun x : Fin 2 → InfinitePlace F → ℝ => fun k => eR.symm (x k))` using `(Equiv.piCongrRight fun _ => eR.symm.toEquiv).bijective`. Conclude with `hP.bij.comp (eT.symm.bijective.comp h1)`.

Establish `hr` using `(LinearEquiv.ofBijective (L : (Fin 2 → InfinitePlace F → ℝ) →ₗ[ℝ] (ι → ℂ)) hbij).finrank_eq`. Simplify using `only [Module.finrank_pi, Module.finrank_fin_fun, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self] at hr`. Establish `hc : Fintype.card (InfinitePlace F) = Module.finrank ℚ F`. Rewrite using `[NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_places (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) :
    Fintype.card ι = Module.finrank ℚ F := by
  classical
  haveI : IsTotallyReal F := hCM.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let eT := GlobalTheory.SiegelWeilConvCompare.tensHomeo (F := F) (E := E) (Ainf F) b
  let eR : Ainf F ≃ₜ (InfinitePlace F → ℝ) := Homeomorph.piCongrRight fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have hRadd : ∀ x y : InfinitePlace F → ℝ, eR.symm (x + y) = eR.symm x + eR.symm y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.map_add (x v) (y v)
  have hTadd : ∀ x y : Fin 2 → Ainf F, eT.symm (x + y) = eT.symm x + eT.symm y := by
    intro x y
    exact (Algebra.TensorProduct.basis (Ainf F) b).equivFun.symm.map_add x y
  let f : (Fin 2 → InfinitePlace F → ℝ) → (ι → ℂ) := fun x i => θ i (eT.symm (fun k => eR.symm (x k)))
  have hfadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y; funext i
    simp only [f, Pi.add_apply]
    rw [show (fun k => eR.symm (x k + y k)) = (fun k => eR.symm (x k)) + (fun k => eR.symm (y k)) from
      funext fun k => hRadd (x k) (y k), hTadd, map_add]
  let fA : (Fin 2 → InfinitePlace F → ℝ) →+ (ι → ℂ) :=
    { toFun := f
      map_zero' := by
        have h0 := hfadd 0 0
        rw [add_zero] at h0
        exact (add_eq_left.1 h0.symm)
      map_add' := hfadd }
  have hfc : Continuous fA := continuous_pi fun i => (hP.cont i).comp
    (eT.symm.continuous.comp (continuous_pi fun k => eR.symm.continuous.comp (continuous_apply k)))
  let L := fA.toRealLinearMap hfc
  have hbij : Function.Bijective L := by
    have h1 : Function.Bijective (fun x : Fin 2 → InfinitePlace F → ℝ => fun k => eR.symm (x k)) :=
      (Equiv.piCongrRight fun _ => eR.symm.toEquiv).bijective
    exact hP.bij.comp (eT.symm.bijective.comp h1)
  have hr := (LinearEquiv.ofBijective (L : (Fin 2 → InfinitePlace F → ℝ) →ₗ[ℝ] (ι → ℂ)) hbij).finrank_eq
  simp only [Module.finrank_pi, Module.finrank_fin_fun, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self] at hr
  have hc : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      add_zero, IsTotallyReal.finrank]
  omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n hMn ψ hψ ι _ θ l hP e fr hfr g μ ν hμ hν T hT`. Use `haveI : IsTotallyReal F := hCM.1`. Use `haveI := secondCountable_tens (F := F) (E := E)`. Use `haveI := borel_tens (F := F) (E := E)`. Use `haveI := borel_herm (F := F) (E := E) σ n`.

Take `⟨eC, heC⟩` from `exists_crdHomeo σ hCM ψ θ l hP fr g`. Take `⟨eb, heb⟩` from `exists_ybHomeo σ hCM ψ θ l hP g`. Use `haveI := haar_volE ι n`. Use `haveI := haar_volW ι M n`. Use `haveI : μ.IsAddHaarMeasure := hμ.1`.

Use `haveI : ν.IsAddHaarMeasure := hν.1`. Take `⟨cμ, -, hcμ⟩` from `exists_map_eq_smul (volume : Measure (ι → Fin M → Fin n → ℂ)) μ eC`. Take `⟨cb, -, hcb⟩` from `exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eb`. Establish `hl : ∀ i, l i ≠ 0` using `hP.ne`. Establish `hβ : ∀ i, (herm (ygAll σ θ g T i)).det ≠ 0` using `det_herm_ygAll σ hCM ψ θ l hP g T hT`.

Establish `hw : ∀ i, ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re → Integrable (fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z) ∧ z ^ (n - M) * W z = ∫ y, fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z y`. Introduce `i`. Establish `hc : 0 < 2 * Real.pi * |l i|` using `by have := abs_pos.2 (hl i); positivity`. Establish `ht : 2 * Real.pi * l i = 2 * Real.pi * |l i| ∨ 2 * Real.pi * l i = -(2 * Real.pi * |l i|)`. Break down `le_or_gt 0 (l i) with h | h` into its components or cases.

Use `left`. Rewrite using `[abs_of_nonneg h]`. Use `right`. Rewrite using `[abs_of_neg h]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h M n hMn (e i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) hc ht (ygAll σ θ g T i) (hβ i)`. Use `choose Wi hWid hrest using hw`. Use `choose σ₀ hσ₀ using hrest`. Use `set s0 : ℂ := ((M : ℂ) - n) / 2 with hs0`. Use `⟨fun z => (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0), ?_, ((M : ℝ) - n) / 2 + ∑ i, |σ₀ i|, fun z hz => ?_⟩` and prove the remaining obligations.

Use `(differentiable_const _).mul ?_` and prove the remaining obligations. Use `Differentiable.finset_prod (u := Finset.univ) (f := fun i z => Wi i (z - s0)) (fun i _ => (hWid i).comp (differentiable_id.sub_const s0))` as an intermediate fact. Rewrite `this` using `[Finset.prod_fn]`. Conclude with `this`. Establish `hzi : ∀ i, σ₀ i < (z - s0).re`.

Introduce `i`. Establish `h1 : (z - s0).re = z.re - ((M : ℝ) - n) / 2`. Rewrite using `[hs0]`. Simplify using the standard rewrite rules. Establish `h2 : σ₀ i ≤ ∑ j, |σ₀ j|` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₀ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))`.

Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint : ∀ i, Integrable (fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i) (ygAll σ θ g T i) (z - s0))` using `fun i => (hσ₀ i _ (hzi i)).1`. Take `⟨h1, h2⟩` from `integral_whI σ hCM ψ θ l hP J (fun i _ => e i) fr hfr g (fun _ => 1) μ eC heC cμ hcμ ν eb heb cb hcb T z hint`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite `h2` using `[← hs0]`. Rewrite using `[h2]`. Establish `h3 : ∀ i, ∫ y, fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i) (ygAll σ θ g T i) (z - s0) y = (z - s0) ^ (n - M) * Wi i (z - s0)` using `fun i => ((hσ₀ i _ (hzi i)).2).symm`. Simplify using `only [h3]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places σ hCM ψ θ l hP, ← pow_mul, mul_comm (n - M)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem realLow_of (h : WROrd) : RealLow := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hMn ψ hψ ι _ θ l hP e fr hfr g μ ν hμ hν T hT
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  obtain ⟨eC, heC⟩ := exists_crdHomeo σ hCM ψ θ l hP fr g
  obtain ⟨eb, heb⟩ := exists_ybHomeo σ hCM ψ θ l hP g
  haveI := haar_volE ι n
  haveI := haar_volW ι M n
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨cμ, -, hcμ⟩ := exists_map_eq_smul (volume : Measure (ι → Fin M → Fin n → ℂ)) μ eC
  obtain ⟨cb, -, hcb⟩ := exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eb
  have hl : ∀ i, l i ≠ 0 := hP.ne
  have hβ : ∀ i, (herm (ygAll σ θ g T i)).det ≠ 0 := det_herm_ygAll σ hCM ψ θ l hP g T hT
  have hw : ∀ i, ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
      Integrable (fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z) ∧
      z ^ (n - M) * W z = ∫ y, fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z y := by
    intro i
    have hc : 0 < 2 * Real.pi * |l i| := by have := abs_pos.2 (hl i); positivity
    have ht : 2 * Real.pi * l i = 2 * Real.pi * |l i| ∨ 2 * Real.pi * l i = -(2 * Real.pi * |l i|) := by
      rcases le_or_gt 0 (l i) with h | h
      · left; rw [abs_of_nonneg h]
      · right; rw [abs_of_neg h]; ring
    exact h M n hMn (e i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) hc ht (ygAll σ θ g T i) (hβ i)
  choose Wi hWid hrest using hw
  choose σ₀ hσ₀ using hrest
  set s0 : ℂ := ((M : ℂ) - n) / 2 with hs0
  refine ⟨fun z => (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0), ?_, ((M : ℝ) - n) / 2 + ∑ i, |σ₀ i|,
    fun z hz => ?_⟩
  · refine (differentiable_const _).mul ?_
    have := Differentiable.finset_prod (u := Finset.univ) (f := fun i z => Wi i (z - s0))
      (fun i _ => (hWid i).comp (differentiable_id.sub_const s0))
    rw [Finset.prod_fn] at this
    exact this
  · have hzi : ∀ i, σ₀ i < (z - s0).re := by
      intro i
      have h1 : (z - s0).re = z.re - ((M : ℝ) - n) / 2 := by
        rw [hs0]; simp
      have h2 : σ₀ i ≤ ∑ j, |σ₀ j| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₀ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i))
      rw [h1]; linarith
    have hint : ∀ i, Integrable (fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i)
        (ygAll σ θ g T i) (z - s0)) := fun i => (hσ₀ i _ (hzi i)).1
    obtain ⟨h1, h2⟩ := integral_whI σ hCM ψ θ l hP J (fun i _ => e i) fr hfr g (fun _ => 1) μ eC heC cμ hcμ ν eb heb
      cb hcb T z hint
    refine ⟨h1, ?_⟩
    rw [← hs0] at h2
    rw [h2]
    have h3 : ∀ i, ∫ y, fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i)
        (ygAll σ θ g T i) (z - s0) y = (z - s0) ^ (n - M) * Wi i (z - s0) := fun i => ((hσ₀ i _ (hzi i)).2).symm
    simp only [h3]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places σ hCM ψ θ l hP, ← pow_mul,
      mul_comm (n - M)]
    ring

end PositivityTheory.SiegelWeilFormula.GReal
