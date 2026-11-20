import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal ComplexOrder

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Set `ℓ : W →L[ℝ] ℂ` to `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => Fin n → ℂ) a).comp L)`. Establish `hℓ : ∀ w, ℓ w = L w a i` using `fun w => rfl`. Consider the cases of `b`. Establish `h : (fun w => if false = true then star (L w a i) else L w a i) = ⇑ℓ`.

Use function extensionality and compare the values at `w`. Simplify using `[hℓ]`. Rewrite using `[h]`. Conclude with `ℓ.hasTemperateGrowth`. Establish `h : (fun w => if true = true then star (L w a i) else L w a i) = ⇑(Complex.conjCLE.toContinuousLinearMap.comp ℓ)`.

Use function extensionality and compare the values at `w`. Simplify using `[hℓ]`. Rewrite using `[h]`. Conclude with `(Complex.conjCLE.toContinuousLinearMap.comp ℓ).hasTemperateGrowth`.
-/
private theorem hasTemperateGrowth_evX_comp_clm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {M n : ℕ}
    (L : W →L[ℝ] (Fin M → Fin n → ℂ)) (k : Fin M × Fin n × Bool) :
    Function.HasTemperateGrowth
      (fun w => if k.2.2 = true then star (L w k.1 k.2.1) else L w k.1 k.2.1) := by
  obtain ⟨a, i, b⟩ := k
  let ℓ : W →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => Fin n → ℂ) a).comp L)
  have hℓ : ∀ w, ℓ w = L w a i := fun w => rfl
  cases b
  · have h : (fun w => if false = true then star (L w a i) else L w a i) = ⇑ℓ := by
      funext w
      simp [hℓ]
    rw [h]
    exact ℓ.hasTemperateGrowth
  · have h : (fun w => if true = true then star (L w a i) else L w a i) =
        ⇑(Complex.conjCLE.toContinuousLinearMap.comp ℓ) := by
      funext w
      simp [hℓ]
    rw [h]
    exact (Complex.conjCLE.toContinuousLinearMap.comp ℓ).hasTemperateGrowth

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : (fun w => evX (MvPolynomial.C a : PX M n) (L w)) = fun _ => a`. Use function extensionality and compare the values at `w`. Simplify using `[evX]`.

Rewrite using `[h]`. Conclude with `Function.HasTemperateGrowth.const a`. Consider the case `add p q hp hq`. Establish `h : (fun w => evX (p + q : PX M n) (L w)) = (fun w => evX p (L w)) + (fun w => evX q (L w))`. Use function extensionality and compare the values at `w`.

Simplify using `[evX]`. Rewrite using `[h]`. Conclude with `hp.add hq`. Consider the case `mul_X p k hp`. Establish `h : (fun w => evX (p * MvPolynomial.X k : PX M n) (L w)) = (fun w => evX p (L w)) * (fun w => if k.2.2 = true then star (L w k.1 k.2.1) else L w k.1 k.2.1)`.

Use function extensionality and compare the values at `w`. Simplify using `[evX]`. Rewrite using `[h]`. Conclude with `hp.mul (hasTemperateGrowth_evX_comp_clm L k)`.
-/
theorem hasTemperateGrowth_evX {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {M n : ℕ}
    (L : W →L[ℝ] (Fin M → Fin n → ℂ)) (P : PX M n) :
    Function.HasTemperateGrowth (fun w => evX P (L w)) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : (fun w => evX (MvPolynomial.C a : PX M n) (L w)) = fun _ => a := by
      funext w
      simp [evX]
    rw [h]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have h : (fun w => evX (p + q : PX M n) (L w)) =
        (fun w => evX p (L w)) + (fun w => evX q (L w)) := by
      funext w
      simp [evX]
    rw [h]
    exact hp.add hq
  | mul_X p k hp =>
    have h : (fun w => evX (p * MvPolynomial.X k : PX M n) (L w)) =
        (fun w => evX p (L w)) *
          (fun w => if k.2.2 = true then star (L w k.1 k.2.1) else L w k.1 k.2.1) := by
      funext w
      simp [evX]
    rw [h]
    exact hp.mul (hasTemperateGrowth_evX_comp_clm L k)

/- English proof (translation)
Set `pr : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℂ)` to `fun i a j => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => Fin n → ℂ) a).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin M → Fin n → ℂ) i))`. Establish `hpr : ∀ i a j x, pr i a j x = x i a j` using `fun _ _ _ _ => rfl`. Set `re3 : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ)` to `fun i a j => Complex.reCLM.comp (pr i a j)`. Set `im3 : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ)` to `fun i a j => Complex.imCLM.comp (pr i a j)`. Establish `hre : ∀ i a j x, re3 i a j x = (x i a j).re` using `fun _ _ _ _ => rfl`.

Establish `him : ∀ i a j x, im3 i a j x = (x i a j).im` using `fun _ _ _ _ => rfl`. Set `B : (ι → Fin M → Fin n → ℂ) →L[ℝ] (ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ` to `∑ i, ∑ a, ∑ j, (-c i) • ((re3 i a j).smulRight (re3 i a j) + (im3 i a j).smulRight (im3 i a j))`. Establish `hB : ∀ x, B x x = -∑ i, c i * ∑ a, ∑ j, ‖x i a j‖ ^ 2`. Introduce `x`. Simplify using `only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, hre, him, smul_eq_mul]`.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hneg : ∀ x, x ≠ 0 → B x x < 0`. Introduce `x hx`.

Rewrite using `[hB, neg_lt_zero]`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`. Take `⟨a, ha⟩` from `Function.ne_iff.mp hi`. Take `⟨j, hj⟩` from `Function.ne_iff.mp ha`. Apply `Finset.sum_pos' (fun i _ => mul_nonneg (hc i).le (by positivity)) ⟨i, Finset.mem_univ _, ?_⟩` to reduce the goal to its premises.

Apply `mul_pos (hc i)` to reduce the goal to its premises. Apply `Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, ?_⟩` to reduce the goal to its premises. Apply `Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, ?_⟩` to reduce the goal to its premises. Conclude with `pow_pos (norm_pos_iff.mpr (by simpa using hj)) 2`. Take `⟨g, hg⟩` from `GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag B hneg`.

Use `⟨g, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hg, hB, Complex.ofReal_exp]`. Simplify using `only [gs]`. Rewrite using `[← Complex.exp_sum]`. Use `congr 1`.

Use `push_cast`. Rewrite using `[Finset.sum_neg_distrib]`.
-/
private theorem exists_schwartz_prod_gs {ι : Type} [Fintype ι] {M n : ℕ} (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) :
    ∃ g : SchwartzMap (ι → Fin M → Fin n → ℂ) ℂ, ∀ x, g x = ∏ i, gs (c i) (x i) := by
  let pr : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℂ) := fun i a j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin M → Fin n → ℂ) i))
  have hpr : ∀ i a j x, pr i a j x = x i a j := fun _ _ _ _ => rfl
  let re3 : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ) := fun i a j =>
    Complex.reCLM.comp (pr i a j)
  let im3 : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ) := fun i a j =>
    Complex.imCLM.comp (pr i a j)
  have hre : ∀ i a j x, re3 i a j x = (x i a j).re := fun _ _ _ _ => rfl
  have him : ∀ i a j x, im3 i a j x = (x i a j).im := fun _ _ _ _ => rfl
  let B : (ι → Fin M → Fin n → ℂ) →L[ℝ] (ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ :=
    ∑ i, ∑ a, ∑ j, (-c i) • ((re3 i a j).smulRight (re3 i a j) + (im3 i a j).smulRight (im3 i a j))
  have hB : ∀ x, B x x = -∑ i, c i * ∑ a, ∑ j, ‖x i a j‖ ^ 2 := by
    intro x
    simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, hre, him, smul_eq_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hneg : ∀ x, x ≠ 0 → B x x < 0 := by
    intro x hx
    rw [hB, neg_lt_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hi
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    apply Finset.sum_pos' (fun i _ => mul_nonneg (hc i).le (by positivity)) ⟨i, Finset.mem_univ _, ?_⟩
    apply mul_pos (hc i)
    apply Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, ?_⟩
    exact pow_pos (norm_pos_iff.mpr (by simpa using hj)) 2
  obtain ⟨g, hg⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag B hneg
  refine ⟨g, fun x => ?_⟩
  rw [hg, hB, Complex.ofReal_exp]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib]

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_schwartz_prod_gs (M := M) (n := n) c hc`. Establish `hbase : ∀ i, Function.HasTemperateGrowth (fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i))` using `fun i => hasTemperateGrowth_evX (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin M → Fin n → ℂ) i) (P i)`. Establish `hp : Function.HasTemperateGrowth (fun x : ι → Fin M → Fin n → ℂ => ∏ i, evX (P i) (x i))`. Use `Finset.prod_induction (s := Finset.univ) (fun i => fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i)) (fun f : (ι → Fin M → Fin n → ℂ) → ℂ => f.HasTemperateGrowth) (fun _ _ h1 h2 => h1.mul h2) (Function.HasTemperateGrowth.const 1) (fun i _ => hbase i)` as an intermediate fact. Establish `h : (∏ i, fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i)) = fun x => ∏ i, evX (P i) (x i)`.

Use function extensionality and compare the values at `x`. Simplify using `[Finset.prod_apply]`. Rewrite `this` using `[h]`. Conclude with `this`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun x => ∏ i, evX (P i) (x i)) g, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply hp, hg, smul_eq_mul, Finset.prod_mul_distrib]`.
-/
theorem exists_schwartz_polyGauss {ι : Type} [Fintype ι] {M n : ℕ} (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (P : ι → PX M n) :
    ∃ f : SchwartzMap (ι → Fin M → Fin n → ℂ) ℂ, ∀ x, f x = ∏ i, (evX (P i) (x i) * gs (c i) (x i)) := by
  obtain ⟨g, hg⟩ := exists_schwartz_prod_gs (M := M) (n := n) c hc
  have hbase : ∀ i, Function.HasTemperateGrowth
      (fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i)) := fun i =>
    hasTemperateGrowth_evX (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin M → Fin n → ℂ) i) (P i)
  have hp : Function.HasTemperateGrowth
      (fun x : ι → Fin M → Fin n → ℂ => ∏ i, evX (P i) (x i)) := by
    have := Finset.prod_induction (s := Finset.univ)
      (fun i => fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i))
      (fun f : (ι → Fin M → Fin n → ℂ) → ℂ => f.HasTemperateGrowth) (fun _ _ h1 h2 => h1.mul h2)
      (Function.HasTemperateGrowth.const 1) (fun i _ => hbase i)
    have h : (∏ i, fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i)) =
        fun x => ∏ i, evX (P i) (x i) := by
      funext x
      simp [Finset.prod_apply]
    rw [h] at this
    exact this
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => ∏ i, evX (P i) (x i)) g, fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hp, hg, smul_eq_mul, Finset.prod_mul_distrib]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Introduce `N e he hes`. Set `A : (Fin N → ℝ) ≃+ (ι → Fin M → Fin n → ℂ)` to `e.symm.trans e0.toAddEquiv`. Establish `hA : Continuous A` using `e0.continuous.comp hes`. Establish `hAs : Continuous A.symm` using `he.comp e0.symm.continuous`. Set `L` to `A.toRealLinearEquiv hA hAs`.

Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun x => ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem isSchwartzInf_comp {ι : Type} [Fintype ι] {M n : ℕ}
    (e0 : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ))
    (f : SchwartzMap (ι → Fin M → Fin n → ℂ) ℂ) : IsSchwartzInf (fun X => f (e0 X)) := by
  intro N e he hes
  let A : (Fin N → ℝ) ≃+ (ι → Fin M → Fin n → ℂ) := e.symm.trans e0.toAddEquiv
  have hA : Continuous A := e0.continuous.comp hes
  have hAs : Continuous A.symm := he.comp e0.symm.continuous
  let L := A.toRealLinearEquiv hA hAs
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun x => ?_⟩
  rfl

end PositivityTheory.SiegelWeilFormula.GReal
