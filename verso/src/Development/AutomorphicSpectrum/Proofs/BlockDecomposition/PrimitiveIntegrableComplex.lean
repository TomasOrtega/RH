import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1

noncomputable section

open MeasureTheory Matrix
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.PrimalIntC

/- English proof (translation)
Unfold `psiC`. Establish `: Continuous fun x : ℂ => ((x.re : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp Complex.continuous_re`. Use `fun_prop`.
-/
theorem continuous_psiC : Continuous psiC := by
  unfold psiC
  have : Continuous fun x : ℂ => ((x.re : ℝ) : ℂ) := Complex.continuous_ofReal.comp Complex.continuous_re
  fun_prop

/- English proof (translation)
Unfold `ph`. Conclude with `(measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)).pow_const m`.
-/
theorem measurable_ph (m : ℤ) : Measurable (ph m) := by
  unfold ph
  exact (measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)).pow_const m

/- English proof (translation)
Introduce `_ hs` and use `⟨_, hs, rfl⟩`.
-/
theorem measurable_val : Measurable (Units.val : ℂˣ → ℂ) := fun _ hs => ⟨_, hs, rfl⟩

/- English proof (translation)
Unfold `chC`. Establish `hn : Measurable fun a : ℂˣ => ‖(a : ℂ)‖` using `measurable_norm.comp measurable_val`. Use `Measurable.mul ?_ ?_` and prove the remaining obligations. Conclude with `(measurable_val.div (Complex.measurable_ofReal.comp hn)).pow_const n`. Conclude with `(Complex.measurable_ofReal.comp (hn.pow_const 2)).pow_const z`.
-/
theorem measurable_chC (n : ℤ) (z : ℂ) : Measurable (chC n z) := by
  unfold chC
  have hn : Measurable fun a : ℂˣ => ‖(a : ℂ)‖ := measurable_norm.comp measurable_val
  refine Measurable.mul ?_ ?_
  · exact (measurable_val.div (Complex.measurable_ofReal.comp hn)).pow_const n
  · exact (Complex.measurable_ofReal.comp (hn.pow_const 2)).pow_const z

/- English proof (translation)
Establish `ha : 0 < ‖(a : ℂ)‖` using `norm_pos_iff.2 a.ne_zero`. Establish `h1 : ‖((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ n‖ = 1`. Rewrite using `[norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self ha.ne', _root_.one_zpow]`. Establish `h2 : ‖(((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)) ^ z‖ = ‖(a : ℂ)‖ ^ (2 * z.re)`. Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ha.le]`.

Evaluate the numerical expressions. Unfold `chC`. Rewrite using `[norm_mul, h1, h2, one_mul]`.
-/
theorem norm_chC (n : ℤ) (z : ℂ) (a : ℂˣ) : ‖chC n z a‖ = ‖(a : ℂ)‖ ^ (2 * z.re) := by
  have ha : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 a.ne_zero
  have h1 : ‖((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ n‖ = 1 := by
    rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self ha.ne', _root_.one_zpow]
  have h2 : ‖(((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)) ^ z‖ = ‖(a : ℂ)‖ ^ (2 * z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  unfold chC
  rw [norm_mul, h1, h2, one_mul]

/- English proof (translation)
Establish `: Continuous fun h : M22 => (Matrix.of h).det`. Simplify using `only [Matrix.det_fin_two, Matrix.of_apply]`. Use `fun_prop`. Conclude with `this.measurable`.
-/
theorem measurable_det_of : Measurable fun h : M22 => (Matrix.of h).det := by
  have : Continuous fun h : M22 => (Matrix.of h).det := by
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    fun_prop
  exact this.measurable

/- English proof (translation)
Establish `hd : Measurable fun h : M22 => ((Matrix.of h).det)⁻¹` using `measurable_det_of.inv`. Establish `e : (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j) = fun h => ((Matrix.of h).det)⁻¹ * (Matrix.adjugate (Matrix.of h)) i j`. Use function extensionality and compare the values at `h`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Simplify using `[Matrix.smul_apply]`.

Rewrite using `[e]`. Use `hd.mul ?_` and prove the remaining obligations. Apply the tactic sequence `have hc : Continuous fun h : M22 => (Matrix.adjugate (Matrix.of h)) i j := by fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> fun_prop`. Conclude with `hc.measurable`.
-/
theorem measurable_inv_entry (i j : Fin 2) :
    Measurable fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  have hd : Measurable fun h : M22 => ((Matrix.of h).det)⁻¹ := measurable_det_of.inv
  have e : (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j) =
      fun h => ((Matrix.of h).det)⁻¹ * (Matrix.adjugate (Matrix.of h)) i j := by
    funext h
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp [Matrix.smul_apply]
  rw [e]
  refine hd.mul ?_
  have hc : Continuous fun h : M22 => (Matrix.adjugate (Matrix.of h)) i j := by
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> fun_prop
  exact hc.measurable

/- English proof (translation)
Establish `hb : Continuous fun r : M22 × (Fin 2 → ℂ) => blk r.2`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop`. Establish `h1 : Continuous fun r : M22 × (Fin 2 → ℂ) => (Matrix.of r.1 : Matrix (Fin 2) (Fin 2) ℂ)` using `continuous_fst`. Conclude with `(h1.matrix_mul hb).matrix_mul continuous_const`.
-/
theorem continuous_mat :
    Continuous fun r : M22 × (Fin 2 → ℂ) =>
      (Matrix.of.symm (Matrix.of r.1 * blk r.2 * ((1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) : M23) := by
  have hb : Continuous fun r : M22 × (Fin 2 → ℂ) => blk r.2 := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop
  have h1 : Continuous fun r : M22 × (Fin 2 → ℂ) => (Matrix.of r.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_fst
  exact (h1.matrix_mul hb).matrix_mul continuous_const

/- English proof (translation)
Use `measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `e : ∀ q, Matrix.vecMul ![T q, T q * Y q] (G q) j = T q * G q 0 j + T q * Y q * G q 1 j`. Introduce `q`. Simplify using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Simplify using `only [e]`.

Conclude with `(hT.mul (hG 0 j)).add ((hT.mul hY).mul (hG 1 j))`.
-/
theorem measurable_row {Q : Type*} [MeasurableSpace Q] (T Y : Q → ℂ)
    (G : Q → Matrix (Fin 2) (Fin 2) ℂ) (hT : Measurable T) (hY : Measurable Y)
    (hG : ∀ i j, Measurable fun q => G q i j) :
    Measurable fun q => Matrix.vecMul ![T q, T q * Y q] (G q) := by
  refine measurable_pi_lambda _ fun j => ?_
  have e : ∀ q, Matrix.vecMul ![T q, T q * Y q] (G q) j =
      T q * G q 0 j + T q * Y q * G q 1 j := by
    intro q
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  simp only [e]
  exact (hT.mul (hG 0 j)).add ((hT.mul hY).mul (hG 1 j))

def matX (r : M22 × (Fin 2 → ℂ)) : M23 :=
  Matrix.of.symm (Matrix.of r.1 * blk r.2 * ((1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))

/- English proof (translation)
The claim follows from `continuous_mat.measurable`.
-/
theorem measurable_matX : Measurable matX := continuous_mat.measurable

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem innQ_eq (Ψ : Sw) (h : M22) (v : Fin 2 → ℂ) :
    innQ Ψ 1 h 1 v = ∫ x : Fin 2 → ℂ, Ψ (matX (h, x), v) * psiC (-((1 : ℂ) * x 1)) := rfl

/- English proof (translation)
Establish `hpr : Measurable fun q : Q × (Fin 2 → ℂ) => (H q.1, q.2)` using `(hH.comp measurable_fst).prodMk measurable_snd`. Establish `hmat : Measurable fun q : Q × (Fin 2 → ℂ) => matX (H q.1, q.2)` using `measurable_matX.comp hpr`. Establish `hx1 : Measurable fun q : Q × (Fin 2 → ℂ) => psiC (-((1 : ℂ) * q.2 1))`. Establish `hc : Continuous fun x : Fin 2 → ℂ => psiC (-((1 : ℂ) * x 1))` using `continuous_psiC.comp (by fun_prop)`. Conclude with `hc.measurable.comp measurable_snd`.

Establish `hpair : Measurable fun q : Q × (Fin 2 → ℂ) => (matX (H q.1, q.2), V q.1)` using `hmat.prodMk (hV.comp measurable_fst)`. Establish `hΨ : Measurable fun q : Q × (Fin 2 → ℂ) => Ψ (matX (H q.1, q.2), V q.1)` using `Ψ.continuous.measurable.comp hpair`. Establish `hF : Measurable fun q : Q × (Fin 2 → ℂ) => Ψ (matX (H q.1, q.2), V q.1) * psiC (-((1 : ℂ) * q.2 1))` using `hΨ.mul hx1`. Simplify using `only [innQ_eq]`. Conclude with `(hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Fin 2 → ℂ)))).measurable`.
-/
theorem measurable_innQ {Q : Type*} [MeasurableSpace Q] (Ψ : Sw) (H : Q → M22)
    (V : Q → Fin 2 → ℂ) (hH : Measurable H) (hV : Measurable V) :
    Measurable fun r => innQ Ψ 1 (H r) 1 (V r) := by
  have hpr : Measurable fun q : Q × (Fin 2 → ℂ) => (H q.1, q.2) :=
    (hH.comp measurable_fst).prodMk measurable_snd
  have hmat : Measurable fun q : Q × (Fin 2 → ℂ) => matX (H q.1, q.2) := measurable_matX.comp hpr
  have hx1 : Measurable fun q : Q × (Fin 2 → ℂ) => psiC (-((1 : ℂ) * q.2 1)) := by
    have hc : Continuous fun x : Fin 2 → ℂ => psiC (-((1 : ℂ) * x 1)) :=
      continuous_psiC.comp (by fun_prop)
    exact hc.measurable.comp measurable_snd
  have hpair : Measurable fun q : Q × (Fin 2 → ℂ) => (matX (H q.1, q.2), V q.1) :=
    hmat.prodMk (hV.comp measurable_fst)
  have hΨ : Measurable fun q : Q × (Fin 2 → ℂ) => Ψ (matX (H q.1, q.2), V q.1) :=
    Ψ.continuous.measurable.comp hpair
  have hF : Measurable fun q : Q × (Fin 2 → ℂ) =>
      Ψ (matX (H q.1, q.2), V q.1) * psiC (-((1 : ℂ) * q.2 1)) := hΨ.mul hx1
  simp only [innQ_eq]
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Fin 2 → ℂ)))).measurable

/- English proof (translation)
The claim follows from `(hA.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))).measurable`.
-/
theorem measurable_integral_snd {R : Type*} [MeasurableSpace R] (A : R → ℂ → ℂ)
    (hA : Measurable fun q : R × ℂ => A q.1 q.2) :
    Measurable fun r => ∫ y : ℂ, A r y :=
  (hA.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))).measurable

/- English proof (translation)
Establish `hp : Measurable fun r : (P × ℂ) × ℂ => r.1.1` using `measurable_fst.comp measurable_fst`. Establish `ht : Measurable fun r : (P × ℂ) × ℂ => r.1.2` using `measurable_snd.comp measurable_fst`. Establish `hV` using `measurable_row (fun r : (P × ℂ) × ℂ => r.1.2) (fun r => r.2) (fun r => g r.1.1) ht measurable_snd fun i j => (hg i j).comp hp`. Establish `h1` using `measurable_innQ Ψ (fun r : (P × ℂ) × ℂ => H r.1.1) _ (hH.comp hp) hV`. Establish `hy2 : Measurable fun r : (P × ℂ) × ℂ => psiC (-r.2)` using `continuous_psiC.measurable.comp measurable_snd.neg`.

Establish `h2 : Measurable fun r : (P × ℂ) × ℂ => innQ Ψ 1 (H r.1.1) 1 (Matrix.vecMul ![r.1.2, r.1.2 * r.2] (g r.1.1)) * psiC (-r.2)` using `h1.mul hy2`. Establish `h3` using `measurable_integral_snd (fun (r : P × ℂ) (y : ℂ) => innQ Ψ 1 (H r.1) 1 (Matrix.vecMul ![r.2, r.2 * y] (g r.1)) * psiC (-y)) h2`. Establish `hph : Measurable fun r : P × ℂ => ph m r.2` using `(measurable_ph m).comp measurable_snd`. Establish `h4 : Measurable fun r : P × ℂ => ph m r.2 * ∫ y : ℂ, innQ Ψ 1 (H r.1) 1 (Matrix.vecMul ![r.2, r.2 * y] (g r.1)) * psiC (-y)` using `hph.mul h3`. Conclude with `measurable_integral_snd (fun (p : P) (t : ℂ) => ph m t * ∫ y : ℂ, innQ Ψ 1 (H p) 1 (Matrix.vecMul ![t, t * y] (g p)) * psiC (-y)) h4`.
-/
theorem measurable_inner {P : Type*} [MeasurableSpace P] (Ψ : Sw) (H : P → M22)
    (g : P → Matrix (Fin 2) (Fin 2) ℂ) (hH : Measurable H)
    (hg : ∀ i j, Measurable fun p => g p i j) (m : ℤ) :
    Measurable fun p : P => ∫ t : ℂ, ph m t * ∫ y : ℂ,
      innQ Ψ 1 (H p) 1 (Matrix.vecMul ![t, t * y] (g p)) * psiC (-y) := by
  have hp : Measurable fun r : (P × ℂ) × ℂ => r.1.1 := measurable_fst.comp measurable_fst
  have ht : Measurable fun r : (P × ℂ) × ℂ => r.1.2 := measurable_snd.comp measurable_fst
  have hV := measurable_row (fun r : (P × ℂ) × ℂ => r.1.2) (fun r => r.2)
    (fun r => g r.1.1) ht measurable_snd fun i j => (hg i j).comp hp
  have h1 := measurable_innQ Ψ (fun r : (P × ℂ) × ℂ => H r.1.1) _ (hH.comp hp) hV
  have hy2 : Measurable fun r : (P × ℂ) × ℂ => psiC (-r.2) :=
    continuous_psiC.measurable.comp measurable_snd.neg
  have h2 : Measurable fun r : (P × ℂ) × ℂ => innQ Ψ 1 (H r.1.1) 1
      (Matrix.vecMul ![r.1.2, r.1.2 * r.2] (g r.1.1)) * psiC (-r.2) := h1.mul hy2
  have h3 := measurable_integral_snd
    (fun (r : P × ℂ) (y : ℂ) => innQ Ψ 1 (H r.1) 1 (Matrix.vecMul ![r.2, r.2 * y] (g r.1)) * psiC (-y)) h2
  have hph : Measurable fun r : P × ℂ => ph m r.2 := (measurable_ph m).comp measurable_snd
  have h4 : Measurable fun r : P × ℂ => ph m r.2 * ∫ y : ℂ, innQ Ψ 1 (H r.1) 1
      (Matrix.vecMul ![r.2, r.2 * y] (g r.1)) * psiC (-y) := hph.mul h3
  exact measurable_integral_snd
    (fun (p : P) (t : ℂ) => ph m t * ∫ y : ℂ, innQ Ψ 1 (H p) 1
      (Matrix.vecMul ![t, t * y] (g p)) * psiC (-y)) h4

/- English proof (translation)
Establish `hH : Measurable fun p : ℂˣ × M22 => p.2` using `measurable_snd`. Establish `ha : Measurable fun p : ℂˣ × M22 => ((p.1 : ℂˣ) : ℂ)` using `measurable_val.comp measurable_fst`. Establish `hdet : Measurable fun p : ℂˣ × M22 => (Matrix.of p.2).det` using `measurable_det_of.comp hH`. Establish `hg : ∀ i j, Measurable fun p : ℂˣ × M22 => (d2 p.1 * (Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j`. Introduce `i j`.

Apply the tactic sequence `have e : ∀ i j, Measurable fun p : ℂˣ × M22 => ((Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => (measurable_inv_entry i j).comp hH`. Use `fin_cases i`. Establish `hm : Measurable fun p : ℂˣ × M22 => ((p.1 : ℂˣ) : ℂ) * ((Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 0 j` using `ha.mul (e 0 j)`. Simplify `hm` using `[d2, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify `e 1 j` using `[d2, Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `hgd : Measurable fun p : ℂˣ × M22 => (d2 p.1 * (Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).det`. Simplify using `only [Matrix.det_fin_two]`. Conclude with `((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))`. Establish `hI` using `measurable_inner Ψ (fun p : ℂˣ × M22 => p.2) (fun p => d2 p.1 * (Matrix.of p.2)⁻¹) hH hg (4 * (k : ℤ) - 4)`. Unfold `prI W2`.

Use `Measurable.mul (Measurable.mul ?_ (Measurable.mul (Measurable.mul ?_ ?_) hI)) ?_` and prove the remaining obligations. Conclude with `Complex.measurable_ofReal.comp (hdet.norm.inv)`. Conclude with `(measurable_ph _).comp hgd`. Conclude with `Complex.measurable_ofReal.comp hgd.norm`. Conclude with `(measurable_chC n _).comp measurable_fst`.
-/
theorem measurable_prI (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) : Measurable (prI k Ψ n s) := by
  have hH : Measurable fun p : ℂˣ × M22 => p.2 := measurable_snd
  have ha : Measurable fun p : ℂˣ × M22 => ((p.1 : ℂˣ) : ℂ) := measurable_val.comp measurable_fst
  have hdet : Measurable fun p : ℂˣ × M22 => (Matrix.of p.2).det := measurable_det_of.comp hH
  have hg : ∀ i j, Measurable fun p : ℂˣ × M22 =>
      (d2 p.1 * (Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro i j
    have e : ∀ i j, Measurable fun p : ℂˣ × M22 =>
        ((Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) i j :=
      fun i j => (measurable_inv_entry i j).comp hH
    fin_cases i
    · have hm : Measurable fun p : ℂˣ × M22 => ((p.1 : ℂˣ) : ℂ) * ((Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 0 j := ha.mul (e 0 j)
      simpa [d2, Matrix.mul_apply, Fin.sum_univ_two] using hm
    · simpa [d2, Matrix.mul_apply, Fin.sum_univ_two] using e 1 j
  have hgd : Measurable fun p : ℂˣ × M22 =>
      (d2 p.1 * (Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).det := by
    simp only [Matrix.det_fin_two]
    exact ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  have hI := measurable_inner Ψ (fun p : ℂˣ × M22 => p.2)
    (fun p => d2 p.1 * (Matrix.of p.2)⁻¹) hH hg (4 * (k : ℤ) - 4)
  unfold prI W2
  refine Measurable.mul (Measurable.mul ?_ (Measurable.mul (Measurable.mul ?_ ?_) hI)) ?_
  · exact Complex.measurable_ofReal.comp (hdet.norm.inv)
  · exact (measurable_ph _).comp hgd
  · exact Complex.measurable_ofReal.comp hgd.norm
  · exact (measurable_chC n _).comp measurable_fst

/- English proof (translation)
Establish `hre : 2 * (s - 1 / 2).re = 2 * s.re - 1`. Simplify using `only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]`. Expand and normalize the polynomial expressions, which then agree. Unfold `prI`. Simplify using `only [norm_mul, norm_chC, hre, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_prI (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (a : ℂˣ) (h : M22) :
    ‖prI k Ψ n s (a, h)‖ = ‖(Matrix.of h).det‖⁻¹ *
      (‖W2 k (innQ Ψ 1 h 1) (d2 a * (Matrix.of h)⁻¹)‖ * ‖(a : ℂ)‖ ^ (2 * s.re - 1)) := by
  have hre : 2 * (s - 1 / 2).re = 2 * s.re - 1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    ring
  unfold prI
  simp only [norm_mul, norm_chC, hre, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
  ring

/- English proof (translation)
Simplify using `[prI, hd]`.
-/
theorem prI_of_det_zero (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (a : ℂˣ) (h : M22)
    (hd : (Matrix.of h).det = 0) : prI k Ψ n s (a, h) = 0 := by
  simp [prI, hd]

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Simplify using `[Matrix.adjugate_fin_two, div_eq_inv_mul]`.
-/
theorem inv_row (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -h 1 0 / (Matrix.of h).det ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = h 0 0 / (Matrix.of h).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [Matrix.adjugate_fin_two, div_eq_inv_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `h0 : ‖h 0 0‖ = 0` using `by nlinarith [sq_nonneg ‖h 0 0‖, sq_nonneg ‖h 1 0‖, norm_nonneg (h 0 0)]`. Establish `h1 : ‖h 1 0‖ = 0` using `by nlinarith [sq_nonneg ‖h 0 0‖, sq_nonneg ‖h 1 0‖, norm_nonneg (h 1 0)]`. Apply `hd` to reduce the goal to its premises. Rewrite using `[Matrix.det_fin_two]`.

Simplify using `[norm_eq_zero.1 h0, norm_eq_zero.1 h1]`.
-/
theorem col_pos (h : M22) (hd : (Matrix.of h).det ≠ 0) : 0 < ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2 := by
  by_contra hc
  have h0 : ‖h 0 0‖ = 0 := by nlinarith [sq_nonneg ‖h 0 0‖, sq_nonneg ‖h 1 0‖, norm_nonneg (h 0 0)]
  have h1 : ‖h 1 0‖ = 0 := by nlinarith [sq_nonneg ‖h 0 0‖, sq_nonneg ‖h 1 0‖, norm_nonneg (h 1 0)]
  apply hd
  rw [Matrix.det_fin_two]
  simp [norm_eq_zero.1 h0, norm_eq_zero.1 h1]

/- English proof (translation)
Take `⟨e0, e1⟩` from `inv_row h hd`. Establish `hA : ‖(Matrix.of h).det‖ ≠ 0` using `norm_ne_zero_iff.2 hd`. Rewrite using `[e0, e1, norm_div, norm_div, norm_neg]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_sq (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    ‖((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) / ‖(Matrix.of h).det‖ ^ 2 := by
  obtain ⟨e0, e1⟩ := inv_row h hd
  have hA : ‖(Matrix.of h).det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  rw [e0, e1, norm_div, norm_div, norm_neg]
  field_simp
  ring

/- English proof (translation)
Establish `hA : ‖(Matrix.of h).det‖ ≠ 0` using `norm_ne_zero_iff.2 hd`. Establish `hc` using `(col_pos h hd).ne'`. Unfold `Yb`. Rewrite using `[row_sq h hd, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem Yb_inv (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    Yb ((Matrix.of h)⁻¹) = ‖(Matrix.of h).det‖ ^ 2 / (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ 2 := by
  have hA : ‖(Matrix.of h).det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  have hc := (col_pos h hd).ne'
  unfold Yb
  rw [row_sq h hd, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]
  field_simp

/- English proof (translation)
Establish `e : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (1 / 2 - σ) = x ^ (1 - 2 * σ)`. Introduce `x hx`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.div_rpow (by positivity) (by positivity), e A hA, e c2 hc, div_eq_mul_inv, ← Real.rpow_neg hc.le]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_power (A c2 σ : ℝ) (hA : 0 < A) (hc : 0 < c2) :
    (A ^ 2 / c2 ^ 2) ^ (1 / 2 - σ) = A ^ (1 - 2 * σ) * c2 ^ (2 * σ - 1) := by
  have e : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (1 / 2 - σ) = x ^ (1 - 2 * σ) := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  rw [Real.div_rpow (by positivity) (by positivity), e A hA, e c2 hc, div_eq_mul_inv,
    ← Real.rpow_neg hc.le]
  congr 2
  ring

/- English proof (translation)
Take `⟨e0, e1⟩` from `inv_row h hd`. Establish `hA : 0 < ‖(Matrix.of h).det‖` using `norm_pos_iff.2 hd`. Establish `b0 : ‖((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ‖eta h‖` using `norm_le_pi_norm (eta h) 0`. Establish `b1 : ‖((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ≤ ‖eta h‖` using `norm_le_pi_norm (eta h) 1`. Rewrite `b0` using `[e0, norm_div, norm_neg]`.

Rewrite `b1` using `[e1, norm_div]`. Establish `hs : (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ ‖h 0 0‖ + ‖h 1 0‖`. Rewrite using `[← Real.sqrt_eq_rpow]`. Use `Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩` and prove the remaining obligations. Use `mul_nonneg (norm_nonneg (h 0 0)) (norm_nonneg (h 1 0))` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `: (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖ ≤ ‖h 0 0‖ / ‖(Matrix.of h).det‖ + ‖h 1 0‖ / ‖(Matrix.of h).det‖`. Rewrite using `[← add_div]`. Conclude with `div_le_div_of_nonneg_right hs hA.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem col_le_eta (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    1 + (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖ ≤ 2 * (1 + ‖eta h‖) := by
  obtain ⟨e0, e1⟩ := inv_row h hd
  have hA : 0 < ‖(Matrix.of h).det‖ := norm_pos_iff.2 hd
  have b0 : ‖((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ‖eta h‖ := norm_le_pi_norm (eta h) 0
  have b1 : ‖((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ≤ ‖eta h‖ := norm_le_pi_norm (eta h) 1
  rw [e0, norm_div, norm_neg] at b0
  rw [e1, norm_div] at b1
  have hs : (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ ‖h 0 0‖ + ‖h 1 0‖ := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have := mul_nonneg (norm_nonneg (h 0 0)) (norm_nonneg (h 1 0))
    nlinarith
  have : (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖ ≤
      ‖h 0 0‖ / ‖(Matrix.of h).det‖ + ‖h 1 0‖ / ‖(Matrix.of h).det‖ := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hs hA.le
  linarith

/- English proof (translation)
Rewrite `hJ` using `[height_power A c2 σ hA hc]`. Establish `hQ : 0 ≤ A ^ (1 - 2 * σ) * c2 ^ (2 * σ - 1)` using `mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hc.le _)`. Establish `hAs : A ^ (-2 - 2 * σ) = A⁻¹ * (A ^ 2)⁻¹ * A ^ (1 - 2 * σ)`. Establish `e : (-2 - 2 * σ) = -(1 : ℝ) + -(2 : ℝ) + (1 - 2 * σ)` using `by ring`. Rewrite using `[e, Real.rpow_add hA, Real.rpow_add hA, Real.rpow_neg hA.le, Real.rpow_neg hA.le, Real.rpow_one]`.

Evaluate the numerical expressions. Establish `hden : 1 / (1 + E) ^ N ≤ 2 ^ N / c1 ^ N`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith) hcE N`. Establish `hI2 : pN ≤ K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N)`.

Use `hI.trans ?_` and prove the remaining obligations. Establish `hn : 0 ≤ K * (A ^ 2)⁻¹ / (1 + nh) ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_mul_div_comm, mul_one]`. Use `_ ≤ K * (A ^ 2)⁻¹ / (1 + nh) ^ N * (2 ^ N / c1 ^ N) := mul_le_mul_of_nonneg_left hden hn`.

Use `_ = K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N) := by rw [div_mul_div_comm]`. Establish `hAi : 0 ≤ A⁻¹` using `by positivity`. Establish `hJ2 : J ≤ |C| * (K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N)) * (A ^ (1 - 2 * σ) * c2 ^ (2 * σ - 1))`. Use `hJ.trans (mul_le_mul_of_nonneg_right ?_ hQ)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hAs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bound_of_det_ne (N : ℕ) (C K σ J p pN E A c2 c1 nh : ℝ) (hA : 0 < A) (hc : 0 < c2)
    (hnh : 0 ≤ nh) (hc1 : 1 ≤ c1) (hE : 0 ≤ E) (hK : 0 ≤ K) (hp : 0 ≤ p) (hpN : p ≤ pN)
    (hJ : J ≤ C * p * (A ^ 2 / c2 ^ 2) ^ (1 / 2 - σ))
    (hI : pN ≤ K * (A ^ 2)⁻¹ / ((1 + nh) ^ N * (1 + E) ^ N))
    (hcE : c1 ≤ 2 * (1 + E)) :
    A⁻¹ * J ≤ (|C| * K * 2 ^ N) *
      (A ^ (-2 - 2 * σ) * c2 ^ (2 * σ - 1) / ((1 + nh) ^ N * c1 ^ N)) := by
  rw [height_power A c2 σ hA hc] at hJ
  have hQ : 0 ≤ A ^ (1 - 2 * σ) * c2 ^ (2 * σ - 1) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hc.le _)
  have hAs : A ^ (-2 - 2 * σ) = A⁻¹ * (A ^ 2)⁻¹ * A ^ (1 - 2 * σ) := by
    have e : (-2 - 2 * σ) = -(1 : ℝ) + -(2 : ℝ) + (1 - 2 * σ) := by ring
    rw [e, Real.rpow_add hA, Real.rpow_add hA, Real.rpow_neg hA.le, Real.rpow_neg hA.le,
      Real.rpow_one]
    norm_num
  have hden : 1 / (1 + E) ^ N ≤ 2 ^ N / c1 ^ N := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hcE N
  have hI2 : pN ≤ K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N) := by
    refine hI.trans ?_
    have hn : 0 ≤ K * (A ^ 2)⁻¹ / (1 + nh) ^ N := by positivity
    calc K * (A ^ 2)⁻¹ / ((1 + nh) ^ N * (1 + E) ^ N)
        = K * (A ^ 2)⁻¹ / (1 + nh) ^ N * (1 / (1 + E) ^ N) := by
          rw [div_mul_div_comm, mul_one]
      _ ≤ K * (A ^ 2)⁻¹ / (1 + nh) ^ N * (2 ^ N / c1 ^ N) := mul_le_mul_of_nonneg_left hden hn
      _ = K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N) := by rw [div_mul_div_comm]
  have hAi : 0 ≤ A⁻¹ := by positivity
  have hJ2 : J ≤ |C| * (K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N)) *
      (A ^ (1 - 2 * σ) * c2 ^ (2 * σ - 1)) := by
    refine hJ.trans (mul_le_mul_of_nonneg_right ?_ hQ)
    calc C * p ≤ |C| * p := mul_le_mul_of_nonneg_right (le_abs_self C) hp
      _ ≤ |C| * pN := mul_le_mul_of_nonneg_left hpN (abs_nonneg C)
      _ ≤ _ := mul_le_mul_of_nonneg_left hI2 (abs_nonneg C)
  calc A⁻¹ * J ≤ A⁻¹ * (|C| * (K * (A ^ 2)⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N)) *
        (A ^ (1 - 2 * σ) * c2 ^ (2 * σ - 1))) := mul_le_mul_of_nonneg_left hJ2 hAi
    _ = _ := by
      rw [hAs]
      ring

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _`.
-/
theorem pS_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ)
    (f : SchwartzMap E ℂ) : 0 ≤ pS N f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

/- English proof (translation)
Establish `hs : Finset.range (N + 1) ⊆ Finset.range (M + 1)` using `Finset.range_subset_range.2 (by omega)`. Unfold `pS`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pS_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {N M : ℕ} (hNM : N ≤ M)
    (f : SchwartzMap E ℂ) : pS N f ≤ pS M f := by
  have hs : Finset.range (N + 1) ⊆ Finset.range (M + 1) :=
    Finset.range_subset_range.2 (by omega)
  unfold pS
  calc ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℝ i j f
      ≤ ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (M + 1), SchwartzMap.seminorm ℝ i j f :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg hs
          fun _ _ _ => apply_nonneg _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs
          fun _ _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

/- English proof (translation)
Introduce `hIbp hAbs hM k hk Ψ n s hs0 hs1`. Take `⟨C, N₁, hC⟩` from `hAbs k hk s.re hs0 hs1`. Take `⟨N₀, hN⟩` from `hM s.re hs0 hs1`. Take `⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ N₁ ≤ N` from `⟨max N₀ N₁, le_max_left _ _, le_max_right _ _⟩`. Establish `hMaj` using `hN N hN0`.

Take `⟨C₁, N', hC₁⟩` from `hIbp N`. Establish `hmeas` using `measurable_prI k Ψ n s`. Establish `hdg : ∀ h : M22, (Matrix.of h).det ≠ 0 → ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0`. Introduce `h hd`. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.

Conclude with `inv_ne_zero hd`. Rewrite using `[integrable_prod_iff' hmeas.aestronglyMeasurable]`. Use `⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hd : (Matrix.of h).det = 0`. Simplify using `only [prI_of_det_zero k Ψ n s _ h hd]`.

Conclude with `integrable_zero _ _ _`. Take `⟨f, hf, -⟩` from `hC₁ Ψ h 1 hd`. Establish `hint` using `(hC f _ (hdg h hd)).1`. Rewrite `hint` using `[hf]`. Use `Integrable.mono' (hint.const_mul ‖(Matrix.of h).det‖⁻¹) ?_ ?_` and prove the remaining obligations.

Conclude with `(hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun a => (norm_prI k Ψ n s a h).le`. Use `Integrable.mono' (hMaj.const_mul (|C| * |C₁ * pS N' Ψ| * 2 ^ N)) ?_ ?_` and prove the remaining obligations. Conclude with `(hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulC)).aestronglyMeasurable`. Use `Filter.Eventually.of_forall fun h => ?_` and prove the remaining obligations.

Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`. Distinguish the cases in `hd : (Matrix.of h).det = 0`. Simplify using `only [prI_of_det_zero k Ψ n s _ h hd, norm_zero, integral_zero]`. Establish `: (0 : ℝ) ≤ ‖(Matrix.of h).det‖ ^ (-2 - 2 * s.re) * (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ (2 * s.re - 1) / ((1 + ‖h‖) ^ N * (1 + (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖) ^ N)` using `by positivity`. Check the signs of the components of the expression.

Take `⟨f, hf, hfb⟩` from `hC₁ Ψ h 1 hd`. Establish `hA : 0 < ‖(Matrix.of h).det‖` using `norm_pos_iff.2 hd`. Establish `hJ` using `(hC f _ (hdg h hd)).2`. Rewrite `hJ` using `[hf, Yb_inv h hd]`. Establish `hval : ∫ a : ℂˣ, ‖prI k Ψ n s (a, h)‖ ∂mulC = ‖(Matrix.of h).det‖⁻¹ * ∫ a : ℂˣ, ‖W2 k (innQ Ψ 1 h 1) (d2 a * (Matrix.of h)⁻¹)‖ * ‖(a : ℂ)‖ ^ (2 * s.re - 1) ∂mulC`.

Simplify using `only [norm_prI k Ψ n s _ h]`. Rewrite using `[integral_const_mul]`. Rewrite using `[hval]`. Establish `hfb' : pS N f ≤ |C₁ * pS N' Ψ| * (‖(Matrix.of h).det‖ ^ 2)⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖eta h‖) ^ N)`. Use `hfb.trans ?_` and prove the remaining obligations.

Simplify using `only [norm_one, one_mul]`. Use `gcongr`. Conclude with `le_abs_self _`. Establish `hnn : 0 ≤ (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖`. Check the signs of the components of the expression.

Conclude with `bound_of_det_ne N C |C₁ * pS N' Ψ| s.re _ (pS N₁ f) (pS N f) ‖eta h‖ _ _ _ ‖h‖ hA (col_pos h hd) (norm_nonneg _) (by linarith) (norm_nonneg _) (abs_nonneg _) (pS_nonneg _ _) (pS_mono hN1 f) hJ hfb' (col_le_eta h hd)`.
-/
theorem main : IbpQ → AbsoluteZetaIntegralBound → ComplexMatrixMajorantIntegrable → PrimInt := by
  intro hIbp hAbs hM k hk Ψ n s hs0 hs1
  obtain ⟨C, N₁, hC⟩ := hAbs k hk s.re hs0 hs1
  obtain ⟨N₀, hN⟩ := hM s.re hs0 hs1
  obtain ⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ N₁ ≤ N := ⟨max N₀ N₁, le_max_left _ _, le_max_right _ _⟩
  have hMaj := hN N hN0
  obtain ⟨C₁, N', hC₁⟩ := hIbp N
  have hmeas := measurable_prI k Ψ n s
  have hdg : ∀ h : M22, (Matrix.of h).det ≠ 0 →
      ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    intro h hd
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hd
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩
  · by_cases hd : (Matrix.of h).det = 0
    · simp only [prI_of_det_zero k Ψ n s _ h hd]
      exact integrable_zero _ _ _
    · obtain ⟨f, hf, -⟩ := hC₁ Ψ h 1 hd
      have hint := (hC f _ (hdg h hd)).1
      rw [hf] at hint
      refine Integrable.mono' (hint.const_mul ‖(Matrix.of h).det‖⁻¹) ?_ ?_
      · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun a => (norm_prI k Ψ n s a h).le
  · refine Integrable.mono' (hMaj.const_mul (|C| * |C₁ * pS N' Ψ| * 2 ^ N)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulC)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hd : (Matrix.of h).det = 0
      · simp only [prI_of_det_zero k Ψ n s _ h hd, norm_zero, integral_zero]
        have : (0 : ℝ) ≤ ‖(Matrix.of h).det‖ ^ (-2 - 2 * s.re) *
            (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ (2 * s.re - 1) /
            ((1 + ‖h‖) ^ N * (1 + (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) /
              ‖(Matrix.of h).det‖) ^ N) := by positivity
        positivity
      · obtain ⟨f, hf, hfb⟩ := hC₁ Ψ h 1 hd
        have hA : 0 < ‖(Matrix.of h).det‖ := norm_pos_iff.2 hd
        have hJ := (hC f _ (hdg h hd)).2
        rw [hf, Yb_inv h hd] at hJ
        have hval : ∫ a : ℂˣ, ‖prI k Ψ n s (a, h)‖ ∂mulC = ‖(Matrix.of h).det‖⁻¹ *
            ∫ a : ℂˣ, ‖W2 k (innQ Ψ 1 h 1) (d2 a * (Matrix.of h)⁻¹)‖ *
              ‖(a : ℂ)‖ ^ (2 * s.re - 1) ∂mulC := by
          simp only [norm_prI k Ψ n s _ h]
          rw [integral_const_mul]
        rw [hval]
        have hfb' : pS N f ≤ |C₁ * pS N' Ψ| * (‖(Matrix.of h).det‖ ^ 2)⁻¹ /
            ((1 + ‖h‖) ^ N * (1 + ‖eta h‖) ^ N) := by
          refine hfb.trans ?_
          simp only [norm_one, one_mul]
          gcongr
          exact le_abs_self _
        have hnn : 0 ≤ (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) ^ ((1 : ℝ) / 2) / ‖(Matrix.of h).det‖ := by
          positivity
        exact bound_of_det_ne N C |C₁ * pS N' Ψ| s.re _ (pS N₁ f) (pS N f) ‖eta h‖ _ _ _ ‖h‖ hA
          (col_pos h hd) (norm_nonneg _) (by linarith) (norm_nonneg _) (abs_nonneg _)
          (pS_nonneg _ _) (pS_mono hN1 f) hJ hfb' (col_le_eta h hd)

end GlobalTheory.CompanionTheory.PrimalIntC
