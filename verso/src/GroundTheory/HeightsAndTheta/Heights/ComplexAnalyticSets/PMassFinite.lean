import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

namespace MassFinite

/- English proof (translation)
Set `v : Fin n → EuclideanSpace ℂ (Fin n)` to `fun i => WithLp.toLp 2 fun j => star (U i j)`. Establish `hv : Orthonormal ℂ v`. Rewrite using `[orthonormal_iff_ite]`. Introduce `i k`. Establish `h` using `congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k`.

Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← h]`. Simplify using `[v, PiLp.inner_apply, Matrix.star_apply, mul_comm]`. Use `⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge, fun i z => ?_⟩` and prove the remaining obligations. Rewrite using `[OrthonormalBasis.coe_mk]`.

Simplify using `[v, PiLp.inner_apply, mul_comm]`.
-/
theorem exists_frame {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j := by
  classical
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 fun j => star (U i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp [v, PiLp.inner_apply, Matrix.star_apply, mul_comm]
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge,
    fun i z => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  simp [v, PiLp.inner_apply, mul_comm]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [ComplexSets.pullback]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, map_mul, hp]`.

Simplify using `[ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]`.
-/
theorem eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (ComplexSets.pullback A P) = eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use `hJ` as an intermediate fact. Establish `hr : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J)` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Establish `h` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.span {f})) (Ideal.Quotient.factor_surjective _) hr (by`. Rewrite using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`.

Rewrite `h` using `[hd]`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) = x at h ⊢`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe e`.

Establish `h' : e + 1 ≤ (d : ℕ∞)` using `by exact_mod_cast h`. Establish `he : e ≠ ⊤` using `fun he => by simp [he] at h'`. Conclude with `(ENat.add_one_le_iff he).mp h'` after adjusting the coercions.
-/
theorem dim_sup_lt {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (f : MvPolynomial (Fin n) ℂ) (hf : f ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) < d := by
  have := hJ
  have hr : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.span {f}))
    (Ideal.Quotient.factor_surjective _) hr
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  rw [hd] at h
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have he : e ≠ ⊤ := fun he => by simp [he] at h'
    exact_mod_cast (ENat.add_one_le_iff he).mp h'

/- English proof (translation)
Establish `hfr : Module.finrank ℝ (ι × Fin 2 → ℝ) = Module.finrank ℝ (EuclideanSpace ℂ ι)`. Rewrite using `[Module.finrank_fintype_fun_eq_card, ← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]`. Set `e` to `(LinearEquiv.ofFinrankEq _ _ hfr).toContinuousLinearEquiv`. Establish `hcard : ((2 * Fintype.card ι : ℕ) : ℝ) = ((Fintype.card (ι × Fin 2) : ℕ) : ℝ)`. Simplify using `[mul_comm]`.

Establish `hsub : Metric.ball (0 : EuclideanSpace ℂ ι) R ⊆ e '' (e.symm '' Metric.ball 0 R)`. Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules. Establish `hb : Bornology.IsBounded (e.symm '' Metric.ball (0 : EuclideanSpace ℂ ι) R)` using `e.symm.lipschitz.isBounded_image Metric.isBounded_ball`. Rewrite using `[hcard]`.

Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_` and prove the remaining obligations. Rewrite using `[hausdorffMeasure_pi_real]`. Conclude with `hb.measure_lt_top`.
-/
theorem ball_lt_top {ι : Type*} [Fintype ι] (R : ℝ) :
    μH[((2 * Fintype.card ι : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R) < ⊤ := by
  have hfr : Module.finrank ℝ (ι × Fin 2 → ℝ) = Module.finrank ℝ (EuclideanSpace ℂ ι) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]
  let e := (LinearEquiv.ofFinrankEq _ _ hfr).toContinuousLinearEquiv
  have hcard : ((2 * Fintype.card ι : ℕ) : ℝ) = ((Fintype.card (ι × Fin 2) : ℕ) : ℝ) := by
    simp [mul_comm]
  have hsub : Metric.ball (0 : EuclideanSpace ℂ ι) R ⊆ e '' (e.symm '' Metric.ball 0 R) := by
    rw [Set.image_image]
    simp
  have hb : Bornology.IsBounded (e.symm '' Metric.ball (0 : EuclideanSpace ℂ ι) R) :=
    e.symm.lipschitz.isBounded_image Metric.isBounded_ball
  rw [hcard]
  calc μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R)
      ≤ μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (e '' (e.symm '' Metric.ball 0 R)) := measure_mono hsub
    _ ≤ _ := e.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
      rw [hausdorffMeasure_pi_real]
      exact hb.measure_lt_top

/- English proof (translation)
Use `set e := I.orderIsoOfFin hI`. Use `set A := U.submatrix (I.orderEmbOfFin hI) id`. Set `y : Fin d → ℂ` to `fun k => x (e k)`. Establish `hsub : WithLp.ofLp '' {z ∈ S | frameProj b I z = x} ⊆ ComplexSets.fibre J A y`. Introduce and unpack `_ ⟨z, ⟨hzS, hzx⟩, rfl⟩`.

Use `⟨fun q hq => hS hzS q hq, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun hzx (e k)`. Simplify using `only [frameProj, hb] at h1`. Simplify using `only [y, ← h1, A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Finset.coe_orderIsoOfFin_apply, e]`.

Establish `hinj : Set.InjOn (WithLp.ofLp (p` using `2)) {z ∈ S | frameProj b I z = x} := (WithLp.ofLp_injective 2).injOn`. Unfold `frameFibreCount`. Rewrite using `[← hinj.encard_image, ← (hN y).1.subset hsub |>.cast_ncard_eq]`. Establish `h2` using `Set.ncard_le_ncard hsub (hN y).1`. Establish `h3` using `(hN y).2`.

Conclude with `h2.trans h3` after adjusting the coercions.
-/
theorem count_le {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I : Finset (Fin n)) (hI : I.card = d) (S : Set (EuclideanSpace ℂ (Fin n)))
    (hS : S ⊆ zeroSetEuc J) (N : ℕ)
    (hN : ∀ y, (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).Finite ∧
      (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).ncard ≤ N)
    (x : I → ℂ) : frameFibreCount b I S x ≤ N := by
  set e := I.orderIsoOfFin hI
  set A := U.submatrix (I.orderEmbOfFin hI) id
  let y : Fin d → ℂ := fun k => x (e k)
  have hsub : WithLp.ofLp '' {z ∈ S | frameProj b I z = x} ⊆ ComplexSets.fibre J A y := by
    rintro _ ⟨z, ⟨hzS, hzx⟩, rfl⟩
    refine ⟨fun q hq => hS hzS q hq, ?_⟩
    funext k
    have h1 := congrFun hzx (e k)
    simp only [frameProj, hb] at h1
    simp only [y, ← h1, A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id,
      Finset.coe_orderIsoOfFin_apply, e]
  have hinj : Set.InjOn (WithLp.ofLp (p := 2)) {z ∈ S | frameProj b I z = x} :=
    (WithLp.ofLp_injective 2).injOn
  unfold frameFibreCount
  rw [← hinj.encard_image, ← (hN y).1.subset hsub |>.cast_ncard_eq]
  have h2 := Set.ncard_le_ncard hsub (hN y).1
  have h3 := (hN y).2
  exact_mod_cast h2.trans h3

/- English proof (translation)
Use `set A := U.submatrix (I₀.orderEmbOfFin hI) id`. Use `set e := I₀.orderIsoOfFin hI`. Introduce and unpack `z ⟨hzZ, hzP⟩`. Take `⟨U', V, g, hU', -, hV, hzV, hg, -, hAg, hZV⟩` from `hP _ hzP (WithLp.ofLp z) ⟨hzZ, rfl⟩`. Set `σ : (I₀ → ℂ) →L[ℂ] (Fin d → ℂ)` to `ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)`.

Establish `hσ : ∀ w k, σ w k = w (e k)` using `fun _ _ => rfl`. Set `L` to `(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm`. Establish `hL : ∀ v, L v = WithLp.toLp 2 v` using `fun _ => rfl`. Establish `hcP : Continuous fun w : Fin d → ℂ => eval w P` using `MvPolynomial.continuous_eval P`. Establish `hcA : Continuous fun z' : EuclideanSpace ℂ (Fin n) => A *ᵥ WithLp.ofLp z'` using `(Continuous.matrix_mulVec continuous_const continuous_id).comp (PiLp.continuous_ofLp 2 _)`.

Use `⟨σ ⁻¹' (U' ∩ {w | eval w P ≠ 0}), {z' | WithLp.ofLp z' ∈ V ∧ eval (A *ᵥ WithLp.ofLp z') P ≠ 0}, fun w => L (g (σ w)), (hU'.inter (isOpen_ne_fun hcP continuous_const)).preimage σ.continuous, (hV.preimage (PiLp.continuous_ofLp 2 _)).inter (isOpen_ne_fun (hcP.comp hcA) continuous_co …` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun (hAg _ hw.1) (e.symm i)`. Simplify using `only [A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, hσ, ← Finset.coe_orderIsoOfFin_apply, e, OrderIso.apply_symm_apply] at h1`. Simplify using `only [frameProj, hb, hL]`.

Simplify using `using h1`. Use extensionality with `z'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hz'Z, -⟩, hz'V, hz'P⟩`. Establish `hmem : WithLp.ofLp z' ∈ ComplexSets.zeroSet J ∩ V` using `⟨hz'Z, hz'V⟩`.

Rewrite `hmem` using `[hZV]`. Take `⟨w0, hw0, hgw0⟩` from `hmem`. Establish `hσw : σ (fun i => w0 (e.symm i)) = w0`. Use function extensionality and compare the values at `k`. Simplify using `[hσ]`.

Use `⟨fun i => w0 (e.symm i), ⟨by rw [hσw]; exact hw0, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_ofPred_eq, hσw, ← hAg w0 hw0, hgw0]`. Conclude with `hz'P`. Simplify using `only [hσw, hL, hgw0]`. Introduce and unpack `⟨w, ⟨hwU, hwP⟩, rfl⟩`.

Establish `hmem : g (σ w) ∈ ComplexSets.zeroSet J ∩ V` using `hZV ▸ ⟨σ w, hwU, rfl⟩`. Establish `hA : A *ᵥ WithLp.ofLp (L (g (σ w))) = σ w` using `hAg _ hwU`. Use `⟨⟨fun q hq => hmem.1 q hq, ?_⟩, hmem.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_ofPred_eq, hA]`. Conclude with `hwP`.

Rewrite using `[hA]`. Conclude with `hwP`.
-/
theorem good_localGraph {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I₀ : Finset (Fin n)) (hI : I₀.card = d) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
      ∀ x ∈ ComplexSets.fibre J (U.submatrix (I₀.orderEmbOfFin hI) id) y,
        ∃ (U' : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ)) (g : (Fin d → ℂ) → (Fin n → ℂ)),
          IsOpen U' ∧ y ∈ U' ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U' ∧ g y = x ∧
          (∀ w ∈ U', U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ g w = w) ∧
          ComplexSets.zeroSet J ∩ V = g '' U') :
    ∀ z ∈ zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0},
      ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
          DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
          (zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0}) ∩ V =
            g '' Ω := by
  set A := U.submatrix (I₀.orderEmbOfFin hI) id
  set e := I₀.orderIsoOfFin hI
  rintro z ⟨hzZ, hzP⟩
  obtain ⟨U', V, g, hU', -, hV, hzV, hg, -, hAg, hZV⟩ := hP _ hzP (WithLp.ofLp z) ⟨hzZ, rfl⟩
  let σ : (I₀ → ℂ) →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)
  have hσ : ∀ w k, σ w k = w (e k) := fun _ _ => rfl
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm
  have hL : ∀ v, L v = WithLp.toLp 2 v := fun _ => rfl
  have hcP : Continuous fun w : Fin d → ℂ => eval w P := MvPolynomial.continuous_eval P
  have hcA : Continuous fun z' : EuclideanSpace ℂ (Fin n) => A *ᵥ WithLp.ofLp z' :=
    (Continuous.matrix_mulVec continuous_const continuous_id).comp (PiLp.continuous_ofLp 2 _)
  refine ⟨σ ⁻¹' (U' ∩ {w | eval w P ≠ 0}),
    {z' | WithLp.ofLp z' ∈ V ∧ eval (A *ᵥ WithLp.ofLp z') P ≠ 0}, fun w => L (g (σ w)),
    (hU'.inter (isOpen_ne_fun hcP continuous_const)).preimage σ.continuous,
    (hV.preimage (PiLp.continuous_ofLp 2 _)).inter (isOpen_ne_fun (hcP.comp hcA) continuous_const),
    ⟨hzV, hzP⟩, L.differentiable.comp_differentiableOn (hg.comp σ.differentiable.differentiableOn
      fun w hw => hw.1), fun w hw => ?_, ?_⟩
  · funext i
    have h1 := congrFun (hAg _ hw.1) (e.symm i)
    simp only [A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, hσ,
      ← Finset.coe_orderIsoOfFin_apply, e, OrderIso.apply_symm_apply] at h1
    simp only [frameProj, hb, hL]
    simpa using h1
  · ext z'
    constructor
    · rintro ⟨⟨hz'Z, -⟩, hz'V, hz'P⟩
      have hmem : WithLp.ofLp z' ∈ ComplexSets.zeroSet J ∩ V := ⟨hz'Z, hz'V⟩
      rw [hZV] at hmem
      obtain ⟨w0, hw0, hgw0⟩ := hmem
      have hσw : σ (fun i => w0 (e.symm i)) = w0 := by
        funext k
        simp [hσ]
      refine ⟨fun i => w0 (e.symm i), ⟨by rw [hσw]; exact hw0, ?_⟩, ?_⟩
      · rw [Set.mem_ofPred_eq, hσw, ← hAg w0 hw0, hgw0]
        exact hz'P
      · simp only [hσw, hL, hgw0]
    · rintro ⟨w, ⟨hwU, hwP⟩, rfl⟩
      have hmem : g (σ w) ∈ ComplexSets.zeroSet J ∩ V := hZV ▸ ⟨σ w, hwU, rfl⟩
      have hA : A *ᵥ WithLp.ofLp (L (g (σ w))) = σ w := hAg _ hwU
      refine ⟨⟨fun q hq => hmem.1 q hq, ?_⟩, hmem.2, ?_⟩
      · rw [Set.mem_ofPred_eq, hA]
        exact hwP
      · rw [hA]
        exact hwP

end MassFinite

/- English proof (translation)
Introduce `n d J hJ hd R`. Establish `hdn : d ≤ n`. Establish `h1` using `ringKrullDim_quotient_le J`. Rewrite `h1` using `[hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using `using h1`.

Take `⟨U, hU, hUfin⟩` from `(hG n d J hJ hd).2.2.2 1 (fun _ => 1)`. Take `⟨b, hb⟩` from `MassFinite.exists_frame U hU`. Establish `hfin : ∀ (I : Finset (Fin n)) (hI : I.card = d), ComplexSets.IsFiniteProjection J (U.submatrix (I.orderEmbOfFin hI) id)` using `fun I hI => by`. Simplify using `using hUfin 0 (I.orderEmbOfFin hI).toEmbedding`. Take `⟨I₀, -, hI₀⟩` from `Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (by simpa using hdn)`.

Use `set A := U.submatrix (I₀.orderEmbOfFin hI₀) id`. Take `⟨P, hP0, hP⟩` from `hD n d J A hJ hd (hfin I₀ hI₀)`. Use `set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}`. Establish `hPJ : ComplexSets.pullback A P ∉ J` using `fun hmem => hP0 <| (hfin I₀ hI₀).injective <| by`. Rewrite using `[map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hmem`. Establish `hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0` using `hN n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)`. Establish `hsub : zeroSetEuc J ∩ Metric.ball 0 R ⊆ zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ Metric.ball 0 R`. Introduce and unpack `z ⟨hz, hzR⟩`. Distinguish the cases in `hzP : eval (A *ᵥ WithLp.ofLp z) P = 0`.

Use `left`. Introduce `q hq`. Take `⟨j, hj, c, hc, rfl⟩` from `Submodule.mem_sup.mp hq`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hc`. Establish `hzj : eval (fun i => z i) j = 0` using `hz j hj`.

Establish `hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0`. Rewrite using `[MassFinite.eval_pullback]`. Conclude with `hzP`. Simplify using `[hzj, hpb]`. Conclude with `Or.inr ⟨⟨hz, hzP⟩, hzR⟩`.

Establish `hgood` using `hL n d b I₀ G hI₀ (MassFinite.good_localGraph J U b hb I₀ hI₀ P (fun y hy x hx => ((hP y hy).2.2 x hx))) R`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hbad, zero_add]`. Use `lt_of_le_of_lt hgood (ENNReal.sum_lt_top.mpr fun I hI => ENNReal.mul_lt_top ?_ ?_)` and prove the remaining obligations. Establish `hIc` using `(Finset.mem_powersetCard.mp hI).2`.

Use `lt_of_le_of_lt (iSup_le fun x => MassFinite.count_le J U b hb I hIc G (fun z hz => hz.1) (ComplexSets.projDegree J (U.submatrix (I.orderEmbOfFin hIc) id)) (fun y => ?_) x) ENNReal.coe_lt_top` and prove the remaining obligations. Establish `h` using `hF n d J _ hJ hd (hfin I hIc) y`. Conclude with `⟨h.2.1, h.2.2⟩`. Establish `h` using `MassFinite.ball_lt_top (ι := I) R`. Rewrite `h` using `[Fintype.card_coe, (Finset.mem_powersetCard.mp hI).2]`. Then use the resulting hypothesis.
-/
theorem MassFinite.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hF : ComplexSets.FibreBound.Statement) (hD : ComplexSets.DiscriminantCover.Statement)
    (hN : NullSmaller.Statement) (hL : LocalGraphMass.Statement) : MassFinite.Statement := by
  intro n d J hJ hd R
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨U, hU, hUfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame U hU
  have hfin : ∀ (I : Finset (Fin n)) (hI : I.card = d),
      ComplexSets.IsFiniteProjection J (U.submatrix (I.orderEmbOfFin hI) id) := fun I hI => by
    simpa using hUfin 0 (I.orderEmbOfFin hI).toEmbedding
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := U.submatrix (I₀.orderEmbOfFin hI₀) id
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd (hfin I₀ hI₀)
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| (hfin I₀ hI₀).injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    hN n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ Metric.ball 0 R ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ Metric.ball 0 R := by
    rintro z ⟨hz, hzR⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzR⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J U b hb I₀ hI₀ P
    (fun y hy x hx => ((hP y hy).2.2 x hx))) R
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪
          G ∩ Metric.ball 0 R) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ Metric.ball 0 R) := measure_union_le _ _
    _ < ⊤ := by
      rw [hbad, zero_add]
      refine lt_of_le_of_lt hgood (ENNReal.sum_lt_top.mpr fun I hI => ENNReal.mul_lt_top ?_ ?_)
      · have hIc := (Finset.mem_powersetCard.mp hI).2
        refine lt_of_le_of_lt (iSup_le fun x => MassFinite.count_le J U b hb I hIc G
          (fun z hz => hz.1) (ComplexSets.projDegree J (U.submatrix (I.orderEmbOfFin hIc) id))
          (fun y => ?_) x) ENNReal.coe_lt_top
        have h := hF n d J _ hJ hd (hfin I hIc) y
        exact ⟨h.2.1, h.2.2⟩
      · have h := MassFinite.ball_lt_top (ι := I) R
        rwa [Fintype.card_coe, (Finset.mem_powersetCard.mp hI).2] at h

end

end GroundTheory.Heights₂.Heights
