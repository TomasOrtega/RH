import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

/- English proof (translation)
Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Establish `s2 : s 2 = 2` using `map_ofNat s 2`. Distinguish the cases in `hy0 : y = 0`. Distinguish the cases in `hx0 : x = 0`. Establish `hN : z * s z = -θ ^ 2`.

Rewrite `hdet` using `[hx0, hy0]`. Take the linear combination `-hdet`. Distinguish the cases in `hz : θ + z = 0`. Establish `hz' : z = -θ` using `by linear_combination hz`. Establish `hsz : s z = θ` using `by rw [hz', map_neg, hsθ, neg_neg]`.

Use `⟨θ, 0, 0, θ⁻¹, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Simplify using `[hx0]`. Rewrite using `[map_inv₀, hsθ, hz']`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Rewrite using `[hsz, hsθ]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Simplify using `[hy0]`. Establish `hw : s z - θ ≠ 0`. Introduce `h0`. Apply `hz` to reduce the goal to its premises. Apply `s.injective` to reduce the goal to its premises.

Rewrite using `[map_add, hsθ, map_zero]`. Take the linear combination `h0`. Establish `sa : s ((θ + z) / θ) = (s z - θ) / (-θ)`. Rewrite using `[map_div₀, map_add, hsθ]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `sd : s (θ / (θ + z)) = (-θ) / (s z - θ)`. Rewrite using `[map_div₀, map_add, hsθ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(θ + z) / θ, 0, 0, θ / (θ + z), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Simplify using `[hx0]`. Rewrite using `[sd]`.

Simplify using `only [zero_mul, sub_zero]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hN`. Rewrite using `[sa]`. Simplify using `only [zero_mul, map_zero, mul_zero, zero_sub]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hN`. Simplify using `[hy0]`. Establish `sa : s (x / (2 * θ)) = -(x / (2 * θ))`. Rewrite using `[map_div₀, map_mul, hsθ, s2, hx]`.

Clear the denominators using the available nonvanishing facts. Establish `sc : s ((s z - θ) / (2 * θ)) = -((z + θ) / (2 * θ))`. Rewrite using `[map_div₀, map_mul, hsθ, s2, map_sub, hss, hsθ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `sd : s ((s z + θ) / x) = (z - θ) / x`. Rewrite using `[map_div₀, map_add, hsθ, hss, hx]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨x / (2 * θ), 1, (s z - θ) / (2 * θ), (s z + θ) / x, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sa, map_one]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sd, sc]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sa, map_one]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[sd, sc]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-2) * hdet`. Establish `sa : s ((z + θ) / (2 * θ)) = -((s z - θ) / (2 * θ))`. Rewrite using `[map_div₀, map_mul, hsθ, s2, map_add, hsθ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `sb : s ((z - θ) / y) = (s z + θ) / y`. Rewrite using `[map_div₀, map_sub, hsθ, hy]`. Expand and normalize the polynomial expressions, which then agree.

Establish `sc : s (y / (2 * θ)) = -(y / (2 * θ))`. Rewrite using `[map_div₀, map_mul, hsθ, s2, hy]`. Clear the denominators using the available nonvanishing facts. Use `⟨(z + θ) / (2 * θ), (z - θ) / y, y / (2 * θ), 1, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sa, sb]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-2) * hdet`. Rewrite using `[map_one, sc]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sa, sb]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_one, sc]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem orbField {K : Type} [Field K] [CharZero K] (s : K →+* K) (θ : K) (hθ : θ ≠ 0)
    (hsθ : s θ = -θ) (hss : ∀ w, s (s w) = w) (x y z : K) (hx : s x = x) (hy : s y = y)
    (hdet : x * y - z * s z = θ ^ 2) :
    ∃ a b c d : K, a * d - b * c = 1 ∧ θ * (a * s b - b * s a) = x ∧ θ * (a * s d - b * s c) = z ∧
      θ * (c * s b - d * s a) = s z ∧ θ * (c * s d - d * s c) = y := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have s2 : s 2 = 2 := map_ofNat s 2
  by_cases hy0 : y = 0
  · by_cases hx0 : x = 0
    · have hN : z * s z = -θ ^ 2 := by
        rw [hx0, hy0] at hdet
        linear_combination -hdet
      by_cases hz : θ + z = 0
      · have hz' : z = -θ := by linear_combination hz
        have hsz : s z = θ := by rw [hz', map_neg, hsθ, neg_neg]
        refine ⟨θ, 0, 0, θ⁻¹, ?_, ?_, ?_, ?_, ?_⟩
        · field_simp
          simp
        · simp [hx0]
        · rw [map_inv₀, hsθ, hz']
          field_simp
          simp
        · rw [hsz, hsθ]
          field_simp
          simp
        · simp [hy0]
      · have hw : s z - θ ≠ 0 := by
          intro h0
          apply hz
          apply s.injective
          rw [map_add, hsθ, map_zero]
          linear_combination h0
        have sa : s ((θ + z) / θ) = (s z - θ) / (-θ) := by
          rw [map_div₀, map_add, hsθ]
          congr 1
          ring
        have sd : s (θ / (θ + z)) = (-θ) / (s z - θ) := by
          rw [map_div₀, map_add, hsθ]
          congr 1
          ring
        refine ⟨(θ + z) / θ, 0, 0, θ / (θ + z), ?_, ?_, ?_, ?_, ?_⟩
        · field_simp
          simp
        · simp [hx0]
        · rw [sd]
          simp only [zero_mul, sub_zero]
          field_simp
          linear_combination -hN
        · rw [sa]
          simp only [zero_mul, map_zero, mul_zero, zero_sub]
          field_simp
          linear_combination -hN
        · simp [hy0]
    · have sa : s (x / (2 * θ)) = -(x / (2 * θ)) := by
        rw [map_div₀, map_mul, hsθ, s2, hx]
        field_simp
      have sc : s ((s z - θ) / (2 * θ)) = -((z + θ) / (2 * θ)) := by
        rw [map_div₀, map_mul, hsθ, s2, map_sub, hss, hsθ]
        field_simp
        ring
      have sd : s ((s z + θ) / x) = (z - θ) / x := by
        rw [map_div₀, map_add, hsθ, hss, hx]
        ring
      refine ⟨x / (2 * θ), 1, (s z - θ) / (2 * θ), (s z + θ) / x, ?_, ?_, ?_, ?_, ?_⟩
      · field_simp
        ring
      · rw [sa, map_one]
        field_simp
        ring
      · rw [sd, sc]
        field_simp
        ring
      · rw [sa, map_one]
        field_simp
        ring
      · rw [sd, sc]
        field_simp
        linear_combination (-2) * hdet
  · have sa : s ((z + θ) / (2 * θ)) = -((s z - θ) / (2 * θ)) := by
      rw [map_div₀, map_mul, hsθ, s2, map_add, hsθ]
      field_simp
      ring
    have sb : s ((z - θ) / y) = (s z + θ) / y := by
      rw [map_div₀, map_sub, hsθ, hy]
      ring
    have sc : s (y / (2 * θ)) = -(y / (2 * θ)) := by
      rw [map_div₀, map_mul, hsθ, s2, hy]
      field_simp
    refine ⟨(z + θ) / (2 * θ), (z - θ) / y, y / (2 * θ), 1, ?_, ?_, ?_, ?_, ?_⟩
    · field_simp
      ring
    · rw [sa, sb]
      field_simp
      linear_combination (-2) * hdet
    · rw [map_one, sc]
      field_simp
      ring
    · rw [sa, sb]
      field_simp
      ring
    · rw [map_one, sc]
      field_simp
      ring

/- English proof (translation)
Establish `p : a * b' - b * a' = 0` using `by linear_combination t' * e00 - (a * b' - b * a') * ht`. Establish `q : a * d' - b * c' = 1` using `by linear_combination t' * e01 - (a * d' - b * c' - 1) * ht`. Establish `r : c * b' - d * a' = -1` using `by linear_combination t' * e10 - (c * b' - d * a' + 1) * ht`. Establish `u : c * d' - d * c' = 0` using `by linear_combination t' * e11 - (c * d' - d * c') * ht`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take the linear combination `(-a') * hdet + c * p - a * r`. Take the linear combination `(-b') * hdet + d * p - b * r`. Take the linear combination `(-c') * hdet - a * u + c * q`. Take the linear combination `(-d') * hdet - b * u + d * q`.
-/
private theorem fix_of {R : Type} [CommRing R] (t t' a b c d a' b' c' d' : R) (ht : t * t' = 1)
    (hdet : a * d - b * c = 1) (e00 : t * (a * b' - b * a') = 0) (e01 : t * (a * d' - b * c') = t)
    (e10 : t * (c * b' - d * a') = -t) (e11 : t * (c * d' - d * c') = 0) :
    a' = a ∧ b' = b ∧ c' = c ∧ d' = d := by
  have p : a * b' - b * a' = 0 := by linear_combination t' * e00 - (a * b' - b * a') * ht
  have q : a * d' - b * c' = 1 := by linear_combination t' * e01 - (a * d' - b * c' - 1) * ht
  have r : c * b' - d * a' = -1 := by linear_combination t' * e10 - (c * b' - d * a' + 1) * ht
  have u : c * d' - d * c' = 0 := by linear_combination t' * e11 - (c * d' - d * c') * ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a') * hdet + c * p - a * r
  · linear_combination (-b') * hdet + d * p - b * r
  · linear_combination (-c') * hdet - a * u + c * q
  · linear_combination (-d') * hdet - b * u + d * q

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Dat.herm, X0, rp, Dat.mkE_def]`.
-/
private theorem hermitian_standardVector : D.herm (rp X0) = !![0, rt D.θ; -rt D.θ, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, X0, rp, Dat.mkE_def]

/- English proof (translation)
Establish `hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1`. Use `h.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `key : D.act (gl h) (rp X0) = rp X0 ↔ h.1 * D.herm (rp X0) * D.star2 h.1 = D.herm (rp X0)`. Use `D.herm_act (gl h) (rp X0)` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite `this` using `[e]`. Conclude with `this.symm`. Introduce `e`.

Conclude with `D.herm_injective (this.trans e)`. Rewrite using `[key, hermitian_standardVector]`. Establish `ht : rt D.θ * rt D.θ⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ D.θ_ne_zero, map_one]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Establish `e00` using `congrFun (congrFun e 0) 0`. Establish `e01` using `congrFun (congrFun e 0) 1`. Establish `e10` using `congrFun (congrFun e 1) 0`. Establish `e11` using `congrFun (congrFun e 1) 1`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e00 e01 e10 e11`. Take `⟨f1, f2, f3, f4⟩` from `fix_of (rt D.θ) (rt D.θ⁻¹) (h 0 0) (h 0 1) (h 1 0) (h 1 1) (D.bar (h 0 0)) (D.bar (h 0 1)) (D.bar (h 1 0)) (D.bar (h 1 1)) ht hdet (by linear_combination e00) (by linear_combination e01) (by linear_combination e10) (by linear_combination e11)`. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `f1`.

Conclude with `f2`. Conclude with `f3`. Conclude with `f4`. Introduce `hb`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hb, Fin.zero_eta, Fin.mk_one, Fin.isValue]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `rt D.θ * hdet`. Take the linear combination `(-rt D.θ) * hdet`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem act_fix_iff (h : G1 E) :
    D.act (gl h) (rp X0) = rp X0 ↔ ∀ i j, D.bar (h i j) = h i j := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe
    rwa [Matrix.det_fin_two] at this
  have key : D.act (gl h) (rp X0) = rp X0 ↔
      h.1 * D.herm (rp X0) * D.star2 h.1 = D.herm (rp X0) := by
    have := D.herm_act (gl h) (rp X0)
    constructor
    · intro e
      rw [e] at this
      exact this.symm
    · intro e
      exact D.herm_injective (this.trans e)
  rw [key, hermitian_standardVector]
  have ht : rt D.θ * rt D.θ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ D.θ_ne_zero, map_one]
  constructor
  · intro e
    have e00 := congrFun (congrFun e 0) 0
    have e01 := congrFun (congrFun e 0) 1
    have e10 := congrFun (congrFun e 1) 0
    have e11 := congrFun (congrFun e 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at e00 e01 e10 e11
    obtain ⟨f1, f2, f3, f4⟩ := fix_of (rt D.θ) (rt D.θ⁻¹) (h 0 0) (h 0 1) (h 1 0) (h 1 1)
      (D.bar (h 0 0)) (D.bar (h 0 1)) (D.bar (h 1 0)) (D.bar (h 1 1)) ht hdet
      (by linear_combination e00) (by linear_combination e01) (by linear_combination e10) (by linear_combination e11)
    intro i j
    fin_cases i <;> fin_cases j
    · exact f1
    · exact f2
    · exact f3
    · exact f4
  · intro hb
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, hb, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · ring
    · linear_combination rt D.θ * hdet
    · linear_combination (-rt D.θ) * hdet
    · ring

/- English proof (translation)
Rewrite using `[act_fix_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Establish `hz : ∀ i j, h i j = am E (D.co (h i j) 0)` using `fun i j => D.eq_am_of_bar_eq (hb i j)`. Establish `hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1`.

Use `h.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Use `⟨⟨Matrix.of fun i j => D.co (h i j) 0, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_two]`. Apply `am_injective (E := E)` to reduce the goal to its premises.

Simplify using `only [Matrix.of_apply, map_sub, map_mul, map_one, ← hz]`. Conclude with `hdet`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `hz i j`.

Introduce and unpack `⟨g, hg⟩ i j`. Establish `: h i j = am E (g i j)` using `congrArg (fun u : GL (Fin 2) (A E) => u.1 i j) hg`. Rewrite using `[this]`. Conclude with `D.bar_am _`.
-/
private theorem part2 (h : G1 E) :
    D.act (gl h) (rp X0) = rp X0 ↔ ∃ g : G1 ℚ, gl h = em E (gl g) := by
  rw [act_fix_iff]
  constructor
  · intro hb
    have hz : ∀ i j, h i j = am E (D.co (h i j) 0) := fun i j => D.eq_am_of_bar_eq (hb i j)
    have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
      have := h.det_coe
      rwa [Matrix.det_fin_two] at this
    refine ⟨⟨Matrix.of fun i j => D.co (h i j) 0, ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      apply am_injective (E := E)
      simp only [Matrix.of_apply, map_sub, map_mul, map_one, ← hz]
      exact hdet
    · apply Units.ext
      ext i j
      exact hz i j
  · rintro ⟨g, hg⟩ i j
    have : h i j = am E (g i j) := congrArg (fun u : GL (Fin 2) (A E) => u.1 i j) hg
    rw [this]
    exact D.bar_am _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `hb` using `(act_fix_iff D _).1 e`. Establish `inj : Function.Injective (algebraMap E (A E))` using `AdeleRing.algebraMap_injective (𝓞 E) E`. Establish `hz : ∀ i j, γ i j = algebraMap ℚ E (D.b.repr (γ i j) 0)`.

Introduce `i j`. Establish `h1 : D.bar (rt (γ i j)) = rt (γ i j)` using `hb i j`. Establish `h2` using `D.eq_am_of_bar_eq h1`. Rewrite `h2` using `[D.co_rt, am_rt]`. Conclude with `inj h2`.

Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Use `⟨⟨Matrix.of fun i j => D.b.repr (γ i j) 0, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_two]`.

Apply `(algebraMap ℚ E).injective` to reduce the goal to its premises. Simplify using `only [Matrix.of_apply, map_sub, map_mul, map_one, ← hz]`. Conclude with `hdet`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Use `show rt (γ i j) = am E (rt (D.b.repr (γ i j) 0))`. Rewrite using `[am_rt, ← hz]`. Introduce and unpack `⟨g, hg⟩`. Conclude with `(part2 D _).2 ⟨ratS ℚ g, hg⟩`.
-/
private theorem part3 (γ : SpecialLinearGroup (Fin 2) E) :
    D.act (gl (ratS E γ)) (rp X0) = rp X0 ↔ ∃ g, gl (ratS E γ) = em E (gl (ratS ℚ g)) := by
  constructor
  · intro e
    have hb := (act_fix_iff D _).1 e
    have inj : Function.Injective (algebraMap E (A E)) := AdeleRing.algebraMap_injective (𝓞 E) E
    have hz : ∀ i j, γ i j = algebraMap ℚ E (D.b.repr (γ i j) 0) := by
      intro i j
      have h1 : D.bar (rt (γ i j)) = rt (γ i j) := hb i j
      have h2 := D.eq_am_of_bar_eq h1
      rw [D.co_rt, am_rt] at h2
      exact inj h2
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe
      rwa [Matrix.det_fin_two] at this
    refine ⟨⟨Matrix.of fun i j => D.b.repr (γ i j) 0, ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      apply (algebraMap ℚ E).injective
      simp only [Matrix.of_apply, map_sub, map_mul, map_one, ← hz]
      exact hdet
    · apply Units.ext
      ext i j
      show rt (γ i j) = am E (rt (D.b.repr (γ i j) 0))
      rw [am_rt, ← hz]
  · rintro ⟨g, hg⟩
    exact (part2 D _).2 ⟨ratS ℚ g, hg⟩

/- English proof (translation)
Establish `inj : Function.Injective (algebraMap E (A E))` using `AdeleRing.algebraMap_injective (𝓞 E) E`. Establish `hsq : D.θ ^ 2 = algebraMap ℚ E D.δ` using `D.sq`. Establish `hss : ∀ w, D.σ (D.σ w) = w`. Introduce `w`. Apply `inj` to reduce the goal to its premises.

Use `D.bar_bar (rt w)` as an intermediate fact. Rewrite `this` using `[D.bar_rt, D.bar_rt]`. Then use the resulting hypothesis. Take `⟨z, hzdef⟩ : ∃ z, z = algebraMap ℚ E (ξ 2) + algebraMap ℚ E (ξ 3) * D.θ` from `⟨_, rfl⟩`. Establish `hsz : D.σ z = algebraMap ℚ E (ξ 2) - algebraMap ℚ E (ξ 3) * D.θ`. Rewrite using `[hzdef, map_add, map_mul, D.conj, AlgEquiv.commutes, AlgEquiv.commutes]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdet : algebraMap ℚ E (ξ 1) * algebraMap ℚ E (ξ 0) - z * D.σ z = D.θ ^ 2`. Establish `h0 : ξ 1 * ξ 0 - (ξ 2 ^ 2 - D.δ * ξ 3 ^ 2) = D.δ`. Simplify using `[qr, X0] at hq`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `congrArg (algebraMap ℚ E) h0`. Simplify using `only [map_sub, map_mul, map_pow] at h1`. Rewrite using `[hsz, hzdef]`. Take the linear combination `h1 + (algebraMap ℚ E (ξ 3) ^ 2 - 1) * hsq`. Take `⟨a, b, c, d, h1, h2, h3, h4, h5⟩` from `orbField (D.σ : E →+* E) D.θ D.θ_ne_zero D.conj hss (algebraMap ℚ E (ξ 1)) (algebraMap ℚ E (ξ 0)) z (D.σ.commutes _) (D.σ.commutes _) hdet`.

Simplify using `only [RingHom.coe_coe] at h2 h3 h4 h5`. Use `⟨⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h1⟩, D.herm_injective ?_⟩` and prove the remaining obligations. Rewrite using `[D.herm_act, hermitian_standardVector]`. Establish `hval : ((gl (ratS E ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h1⟩) : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![rt a, rt b; rt c, rt d]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> rfl`. Rewrite using `[hval, D.herm_eq]`. Establish `g2` using `congrArg (algebraMap E (A E)) h2`. Establish `g3` using `congrArg (algebraMap E (A E)) h3`. Establish `g4` using `congrArg (algebraMap E (A E)) h4`.

Establish `g5` using `congrArg (algebraMap E (A E)) h5`. Simplify using `only [map_mul, map_sub] at g2 g3 g4 g5`. Establish `m : D.mkE (rp ξ 2) (rp ξ 3) = rt z` using `by rw [hzdef]; exact D.mkE_rt _ _`. Rewrite using `[m, D.bar_rt, am_rt, am_rt]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, D.bar_rt, Fin.zero_eta, Fin.mk_one, Fin.isValue]`. Take the linear combination `-g2`. Take the linear combination `-g3`. Take the linear combination `-g4`.

Take the linear combination `-g5`.
-/
private theorem part1 (ξ : Fin 4 → ℚ) (hq : qr D.δ ξ = qr D.δ X0) :
    ∃ γ : SpecialLinearGroup (Fin 2) E, rp ξ = D.act (gl (ratS E γ)) (rp X0) := by
  have inj : Function.Injective (algebraMap E (A E)) := AdeleRing.algebraMap_injective (𝓞 E) E
  have hsq : D.θ ^ 2 = algebraMap ℚ E D.δ := D.sq
  have hss : ∀ w, D.σ (D.σ w) = w := by
    intro w
    apply inj
    have := D.bar_bar (rt w)
    rwa [D.bar_rt, D.bar_rt] at this
  obtain ⟨z, hzdef⟩ : ∃ z, z = algebraMap ℚ E (ξ 2) + algebraMap ℚ E (ξ 3) * D.θ := ⟨_, rfl⟩
  have hsz : D.σ z = algebraMap ℚ E (ξ 2) - algebraMap ℚ E (ξ 3) * D.θ := by
    rw [hzdef, map_add, map_mul, D.conj, AlgEquiv.commutes, AlgEquiv.commutes]
    ring
  have hdet : algebraMap ℚ E (ξ 1) * algebraMap ℚ E (ξ 0) - z * D.σ z = D.θ ^ 2 := by
    have h0 : ξ 1 * ξ 0 - (ξ 2 ^ 2 - D.δ * ξ 3 ^ 2) = D.δ := by
      simp [qr, X0] at hq
      linarith
    have h1 := congrArg (algebraMap ℚ E) h0
    simp only [map_sub, map_mul, map_pow] at h1
    rw [hsz, hzdef]
    linear_combination h1 + (algebraMap ℚ E (ξ 3) ^ 2 - 1) * hsq
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5⟩ := orbField (D.σ : E →+* E) D.θ D.θ_ne_zero D.conj hss
    (algebraMap ℚ E (ξ 1)) (algebraMap ℚ E (ξ 0)) z (D.σ.commutes _) (D.σ.commutes _) hdet
  simp only [RingHom.coe_coe] at h2 h3 h4 h5
  refine ⟨⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h1⟩, D.herm_injective ?_⟩
  rw [D.herm_act, hermitian_standardVector]
  have hval : ((gl (ratS E ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h1⟩) : GL (Fin 2) (A E)) :
      Matrix (Fin 2) (Fin 2) (A E)) = !![rt a, rt b; rt c, rt d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hval, D.herm_eq]
  have g2 := congrArg (algebraMap E (A E)) h2
  have g3 := congrArg (algebraMap E (A E)) h3
  have g4 := congrArg (algebraMap E (A E)) h4
  have g5 := congrArg (algebraMap E (A E)) h5
  simp only [map_mul, map_sub] at g2 g3 g4 g5
  have m : D.mkE (rp ξ 2) (rp ξ 3) = rt z := by rw [hzdef]; exact D.mkE_rt _ _
  rw [m, D.bar_rt, am_rt, am_rt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, D.bar_rt, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination -g2
  · linear_combination -g3
  · linear_combination -g4
  · linear_combination -g5

/- English proof (translation)
Introduce `E _ _ _ D`. Conclude with `⟨part1 D, part2 D, part3 D⟩`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orbS :
    OrbS := by
  intro E _ _ _ D
  exact ⟨part1 D, part2 D, part3 D⟩
