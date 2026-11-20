import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Subst

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]`.
-/
theorem consCol_mulVec_map {E S : Type} [Field E] [CommRing S] (φ : E →+* S) {M : ℕ}
    (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (t : S) (w : Fin M → S) :
    ((Matrix.of fun i => Fin.cons (α := fun _ => E) (x 0 i) (B i) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) E).map φ).mulVec (Fin.cons t w) =
      t • (fun i => φ (x 0 i)) + (B.map φ).mulVec w := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

/- English proof (translation)
Take `⟨-, ha, hx, hB, hJ', -, hd⟩` from `h`. Introduce `h0`. Take `⟨v, hv, hPv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `e` using `consCol_mulVec_map (RingHom.id E) x B (v 0) (Fin.tail v)`. Rewrite `e` using `[Fin.cons_self_tail]`.

Establish `e' : v 0 • x 0 + B.mulVec (Fin.tail v) = 0`. Rewrite using `[← hPv]`. Conclude with `e.symm`. Set `r : Fin (M + 1) → E` to `Matrix.vecMul (fun i => σ (x 0 i)) J`. Establish `hr : ∀ y, hE σ J (x 0) y = r ⬝ᵥ y`.

Introduce `y`. Simplify using `only [hE, Formalism.UG.hform, r, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression. Establish `h1 : r ⬝ᵥ B.mulVec (Fin.tail v) = 0`.

Rewrite using `[Matrix.dotProduct_mulVec]`. Establish `: Matrix.vecMul r B = 0`. Use function extensionality and compare the values at `j`. Conclude with `(hr _).symm.trans (hB j)`. Rewrite using `[this, zero_dotProduct]`.

Establish `h2 : v 0 = 0`. Use `congrArg (fun y => r ⬝ᵥ y) e'` as an intermediate fact. Simplify using `only [dotProduct_add, h1, dotProduct_smul, ← hr (x 0), hx, add_zero, dotProduct_zero, smul_eq_mul, mul_eq_zero] at this`. Break down `this with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd ((map_eq_zero _).1 h) ha`. Rewrite `e'` using `[h2, zero_smul, zero_add]`. Establish `h3 : J'.mulVec (Fin.tail v) = 0`. Rewrite using `[hJ', ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero]`. Establish `h4 : Fin.tail v = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hd h3`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[← Fin.cons_self_tail v, h2, h4]`. Use function extensionality and compare the values at `i`. Use `Fin.cases rfl (fun _ => rfl) i` and prove the remaining obligations.
-/
theorem det_consCol_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (h : StepData σ J x a B J') : (consCol x B).det ≠ 0 := by
  obtain ⟨-, ha, hx, hB, hJ', -, hd⟩ := h
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e := consCol_mulVec_map (RingHom.id E) x B (v 0) (Fin.tail v)
  rw [Fin.cons_self_tail] at e
  have e' : v 0 • x 0 + B.mulVec (Fin.tail v) = 0 := by
    rw [← hPv]
    exact e.symm
  let r : Fin (M + 1) → E := Matrix.vecMul (fun i => σ (x 0 i)) J
  have hr : ∀ y, hE σ J (x 0) y = r ⬝ᵥ y := by
    intro y
    simp only [hE, Formalism.UG.hform, r, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have h1 : r ⬝ᵥ B.mulVec (Fin.tail v) = 0 := by
    rw [Matrix.dotProduct_mulVec]
    have : Matrix.vecMul r B = 0 := by
      funext j
      exact (hr _).symm.trans (hB j)
    rw [this, zero_dotProduct]
  have h2 : v 0 = 0 := by
    have := congrArg (fun y => r ⬝ᵥ y) e'
    simp only [dotProduct_add, h1, dotProduct_smul, ← hr (x 0), hx, add_zero, dotProduct_zero,
      smul_eq_mul, mul_eq_zero] at this
    rcases this with h | h
    · exact h
    · exact absurd ((map_eq_zero _).1 h) ha
  rw [h2, zero_smul, zero_add] at e'
  have h3 : J'.mulVec (Fin.tail v) = 0 := by
    rw [hJ', ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero]
  have h4 : Fin.tail v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd h3
  apply hv
  rw [← Fin.cons_self_tail v, h2, h4]
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

/- English proof (translation)
Establish `key` using `GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct S h1 h2 lam hl 1 (M + 1) G 1 hG (by simp)`. Establish `hm1 : modu S 1 = 1` using `(GlobalTheory.GaugeEx.modu_basic S).2.2.1`. Rewrite `key` using `[Matrix.det_one, hm1, pow_one, one_pow, mul_one]`. Establish `hU : ∀ K : ℕ, MeasurePreserving (fun X : Fin 1 → Fin K → S => X 0) (tupMeas lam 1 K) (Measure.pi fun _ => lam)` using `fun K => measurePreserving_funUnique (Measure.pi fun _ : Fin K => lam) (Fin 1)`. Establish `hGc : Continuous fun z : Fin (M + 1) → S => G.mulVec z` using `continuous_const.matrix_mulVec continuous_id`.

Establish `hlr : lrAct G (1 : Matrix (Fin 1) (Fin 1) S) = fun X _ => G.mulVec (X 0)`. Use function extensionality and compare the values at `X a`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Simplify using `[lrAct]`. Establish `hlrm : Measurable (lrAct G (1 : Matrix (Fin 1) (Fin 1) S))`.

Rewrite using `[hlr]`. Conclude with `measurable_pi_lambda _ fun _ => hGc.measurable.comp (measurable_pi_apply 0)`. Establish `hfG : Measurable fun z : Fin (M + 1) → S => f (G.mulVec z)` using `hf.comp hGc.measurable`. Establish `hP` using `(measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => lam) 0).symm`. Establish `hc : ∀ p : S × (Fin M → S), (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => S) 0).symm p = Fin.cons p.1 p.2`.

Introduce `p`. Simplify using `[MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_smul_measure, lintegral_map (f := fun X : Fin 1 → Fin (M + 1) → S => f (X 0)) (hf.comp (measurable_pi_apply 0)) hlrm, hlr]`. Both sides reduce to the same expression.

Use `_ = (modu S G.det : ℝ≥0∞) * ∫⁻ z, f (G.mulVec z) ∂(Measure.pi fun _ => lam) := by`. Rewrite using `[(hU _).lintegral_comp hfG]`. Use `_ = _ := by`. Use `congr 1`. Rewrite using `[← hP.lintegral_comp hfG]`.

Use `(lintegral_prod _ (hfG.comp hP.measurable).aemeasurable).trans ?_` and prove the remaining obligations. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Establish `hm : Measurable fun w : Fin M → S => f (G.mulVec (Fin.cons t w))`. Use `(hfG.comp hP.measurable).comp (measurable_prodMk_left (x := t))` as an intermediate fact. Use `this using 2 with w` and compare the differences between its conclusion and the goal.

Simplify using `only [Function.comp, hc]`. Rewrite using `[(hU M).lintegral_comp hm]`. Simplify using `only [Function.comp, hc]`.
-/
theorem lintegral_subst (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (h1 : IsArtinianRing S) (h2 : IsReduced S) (lam : Measure S) (hl : lam.IsAddHaarMeasure) (M : ℕ)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) S) (hG : IsUnit G.det)
    (f : (Fin (M + 1) → S) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(Measure.pi fun _ => lam) =
      (modu S G.det : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (G.mulVec (Fin.cons t (y' 0))) ∂(tupMeas lam 1 M) ∂lam := by
  have key := GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct S h1 h2 lam hl 1 (M + 1) G 1 hG (by simp)
  have hm1 : modu S 1 = 1 := (GlobalTheory.GaugeEx.modu_basic S).2.2.1
  rw [Matrix.det_one, hm1, pow_one, one_pow, mul_one] at key
  have hU : ∀ K : ℕ, MeasurePreserving (fun X : Fin 1 → Fin K → S => X 0) (tupMeas lam 1 K)
      (Measure.pi fun _ => lam) := fun K =>
    measurePreserving_funUnique (Measure.pi fun _ : Fin K => lam) (Fin 1)
  have hGc : Continuous fun z : Fin (M + 1) → S => G.mulVec z :=
    continuous_const.matrix_mulVec continuous_id
  have hlr : lrAct G (1 : Matrix (Fin 1) (Fin 1) S) = fun X _ => G.mulVec (X 0) := by
    funext X a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [lrAct]
  have hlrm : Measurable (lrAct G (1 : Matrix (Fin 1) (Fin 1) S)) := by
    rw [hlr]
    exact measurable_pi_lambda _ fun _ => hGc.measurable.comp (measurable_pi_apply 0)
  have hfG : Measurable fun z : Fin (M + 1) → S => f (G.mulVec z) := hf.comp hGc.measurable
  have hP := (measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => lam) 0).symm
  have hc : ∀ p : S × (Fin M → S),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => S) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  calc ∫⁻ z, f z ∂(Measure.pi fun _ => lam)
      = ∫⁻ X, f (X 0) ∂(tupMeas lam 1 (M + 1)) := ((hU _).lintegral_comp hf).symm
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ X, f (G.mulVec (X 0)) ∂(tupMeas lam 1 (M + 1)) := by
        conv_lhs => rw [key]
        rw [lintegral_smul_measure, lintegral_map (f := fun X : Fin 1 → Fin (M + 1) → S => f (X 0))
          (hf.comp (measurable_pi_apply 0)) hlrm, hlr]
        rfl
    _ = (modu S G.det : ℝ≥0∞) * ∫⁻ z, f (G.mulVec z) ∂(Measure.pi fun _ => lam) := by
        rw [(hU _).lintegral_comp hfG]
    _ = _ := by
        congr 1
        rw [← hP.lintegral_comp hfG]
        refine (lintegral_prod _ (hfG.comp hP.measurable).aemeasurable).trans ?_
        refine lintegral_congr fun t => ?_
        have hm : Measurable fun w : Fin M → S => f (G.mulVec (Fin.cons t w)) := by
          have := (hfG.comp hP.measurable).comp (measurable_prodMk_left (x := t))
          convert this using 2 with w
          simp only [Function.comp, hc]
        rw [(hU M).lintegral_comp hm]
        simp only [Function.comp, hc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hR M J x a B J' hS lam hl g y hy f hf`. Take `⟨n1, n2, -⟩` from `GlobalTheory.GaugeEx.nice_tensor F E R hR`. Establish `hP : IsUnit (inclR (F` using `F) R (consCol x B).det) := (IsUnit.mk0 _ (det_consCol_ne_zero σ J x a B J' hS)).map _`. Establish `hJ : IsUnit (JR (F` using `F) R J).det := by`. Establish `: IsUnit (inclR (F` using `F) R J.det) := (IsUnit.mk0 _ hS.1.2).map _`.

Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Use `set A : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) := (HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)).val with hA`. Establish `hAu : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)`. Establish `hU : Formalism.UG.cT (sigR R σ) A * JR R J * A = JR R J` using `(show HR R σ J from g).2`. Establish `hN : A.det * sigR R σ A.det = 1`.

Use `congrArg Matrix.det hU` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Apply `hJ.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[mul_one]`. Use `conv_rhs => rw [← this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmA : modu (R ⊗[F] E) A.det = 1`. Rewrite using `[(GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ hCM R A.det 1 hAu (by rw [map_one, hN])).2]`. Conclude with `(GlobalTheory.GaugeEx.modu_basic R).2.2.1`. Establish `hdet : (A * (consCol x B).map (inclR (F` using `F) R)).det = A.det * inclR (F := F) R (consCol x B).det := by`.

Rewrite using `[Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]`. Rewrite using `[lintegral_subst (R ⊗[F] E) n1 n2 lam hl M (A * (consCol x B).map (inclR (F := F) R)) (by rw [hdet]; exact hAu.mul hP) f hf, hdet, (GlobalTheory.GaugeEx.modu_basic (R ⊗[F] E)).2.1 _ _ hAu hP, hmA, one_mul]`. Use `congr 1`. Use `lintegral_congr fun t => lintegral_congr fun y' => congrArg f ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, consCol, consCol_mulVec_map, Matrix.mulVec_add, Matrix.mulVec_smul]`.

Substitute `hy` using the available equality. Both sides reduce to the same expression.
-/
theorem subst : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ (lam : Measure (R ⊗[F] E)), lam.IsAddHaarMeasure → ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E), g • ratTup (F := F) R x = y → ∀ f : (Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ z, f z ∂(Measure.pi fun _ => lam) = (modu (R ⊗[F] E) (inclR R (consCol x B).det) : ℝ≥0∞) * ∫⁻ t, ∫⁻ y', f (t • y 0 + pairOf R σ J B y g y' 1) ∂(tupMeas lam 1 M) ∂lam := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hR M J x a B J' hS lam hl g y hy f hf
  obtain ⟨n1, n2, -⟩ := GlobalTheory.GaugeEx.nice_tensor F E R hR
  have hP : IsUnit (inclR (F := F) R (consCol x B).det) :=
    (IsUnit.mk0 _ (det_consCol_ne_zero σ J x a B J' hS)).map _
  have hJ : IsUnit (JR (F := F) R J).det := by
    have : IsUnit (inclR (F := F) R J.det) := (IsUnit.mk0 _ hS.1.2).map _
    rwa [RingHom.map_det] at this
  set A : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) :=
    (HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)).val with hA
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have hU : Formalism.UG.cT (sigR R σ) A * JR R J * A = JR R J := (show HR R σ J from g).2
  have hN : A.det * sigR R σ A.det = 1 := by
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply hJ.mul_left_cancel
    rw [mul_one]
    conv_rhs => rw [← this]
    ring
  have hmA : modu (R ⊗[F] E) A.det = 1 := by
    rw [(GlobalTheory.GaugeEx.modu_eq_modu_norm F E σ hCM R A.det 1 hAu (by rw [map_one, hN])).2]
    exact (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  have hdet : (A * (consCol x B).map (inclR (F := F) R)).det =
      A.det * inclR (F := F) R (consCol x B).det := by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [lintegral_subst (R ⊗[F] E) n1 n2 lam hl M (A * (consCol x B).map (inclR (F := F) R))
    (by rw [hdet]; exact hAu.mul hP) f hf, hdet,
    (GlobalTheory.GaugeEx.modu_basic (R ⊗[F] E)).2.1 _ _ hAu hP, hmA, one_mul]
  congr 1
  refine lintegral_congr fun t => lintegral_congr fun y' => congrArg f ?_
  rw [← Matrix.mulVec_mulVec, consCol, consCol_mulVec_map, Matrix.mulVec_add, Matrix.mulVec_smul]
  subst hy
  rfl

end GlobalTheory.GaugeEx.Subst
