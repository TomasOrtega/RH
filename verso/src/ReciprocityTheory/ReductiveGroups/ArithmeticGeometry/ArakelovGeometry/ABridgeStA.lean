import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_map, aeval_def]`. Apply the tactic sequence `congr 1 <;> exact RingHom.ext_int _ _`.
-/
theorem aeval_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    aeval x (map (Int.castRingHom ℚ) f) = aeval x f := by
  rw [aeval_def, eval₂_map, aeval_def]
  congr 1 <;> exact RingHom.ext_int _ _

/- English proof (translation)
Use `conv_lhs => rw [φ.as_sum]`. Use `conv_rhs => rw [φ.as_sum]`. Simplify using `only [map_sum, Finset.mul_sum, eval_monomial]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hd : ∑ i ∈ s.support, s i = d`.

Use `hφ (mem_support_iff.mp hs)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum]`. Simplify using `only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_of_homog {R : Type*} [CommRing R] {φ : MvPolynomial J R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : J → R) : eval (c • z) φ = c ^ d * eval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd : ∑ i ∈ s.support, s i = d := by
    have := hφ (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hb`. Establish `hmap : map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℂ) f`. Rewrite using `[map_map]`. Apply the tactic sequence `congr 1 <;> exact RingHom.ext_int _ _`. Simplify using `only [secFun, hmap]`.

Conclude with `eval_smul_of_homog (hf.map _) c z`.
-/
theorem secFun_smul {b : MvPolynomial J ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : J → ℂ) : secFun b (c • z) = c ^ n * secFun b z := by
  obtain ⟨f, hf, rfl⟩ := hb
  have hmap : map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℂ) f := by
    rw [map_map]
    congr 1 <;> exact RingHom.ext_int _ _
  simp only [secFun, hmap]
  exact eval_smul_of_homog (hf.map _) c z

/- English proof (translation)
Unfold `secFun`. Conclude with `MvPolynomial.continuous_eval _`.
-/
theorem continuous_secFun (b : MvPolynomial J ℚ) : Continuous (secFun b) := by
  unfold secFun
  exact MvPolynomial.continuous_eval _

/- English proof (translation)
Unfold `secFun`. Rewrite using `[map_map]`. Apply the tactic sequence `congr 2 <;> exact RingHom.ext_int _ _`.
-/
theorem secFun_map_int (f : MvPolynomial J ℤ) (z : J → ℂ) :
    secFun (map (Int.castRingHom ℚ) f) z = eval z (map (Int.castRingHom ℂ) f) := by
  unfold secFun
  rw [map_map]
  congr 2 <;> exact RingHom.ext_int _ _

/- English proof (translation)
Establish `hmem : d ∈ coordIdeal ℤ x`. Unfold `coordIdeal coneMap`. Rewrite using `[RingHom.mem_ker, aeval_def, ← eval_map]`. Establish `hpt : (fun i => Polynomial.C (x i) * Polynomial.X) = (Polynomial.X : Polynomial Ω) • fun i => Polynomial.C (x i)`. Use function extensionality and compare the values at `i`.

Conclude with `mul_comm _ _`. Establish `hC : eval (fun i => Polynomial.C (x i)) (map (algebraMap ℤ (Polynomial Ω)) d) = Polynomial.C (aeval x d)`. Rewrite using `[eval_map, aeval_def, hom_eval₂]`. Apply the tactic sequence `congr 1 <;> exact RingHom.ext_int _ _`. Rewrite using `[hpt, eval_smul_of_homog (hd.map _), hC, h0, map_zero, mul_zero]`.

Rewrite using `[secFun_map_int]`. Conclude with `hz.2 d hmem`.
-/
theorem secFun_eq_zero_of_pts {x : J → Ω} {n : ℕ} {d : MvPolynomial J ℤ} (hd : d.IsHomogeneous n)
    (h0 : aeval x d = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    secFun (map (Int.castRingHom ℚ) d) z = 0 := by
  have hmem : d ∈ coordIdeal ℤ x := by
    unfold coordIdeal coneMap
    rw [RingHom.mem_ker, aeval_def, ← eval_map]
    have hpt : (fun i => Polynomial.C (x i) * Polynomial.X) =
        (Polynomial.X : Polynomial Ω) • fun i => Polynomial.C (x i) := by
      funext i
      exact mul_comm _ _
    have hC : eval (fun i => Polynomial.C (x i)) (map (algebraMap ℤ (Polynomial Ω)) d) =
        Polynomial.C (aeval x d) := by
      rw [eval_map, aeval_def, hom_eval₂]
      congr 1 <;> exact RingHom.ext_int _ _
    rw [hpt, eval_smul_of_homog (hd.map _), hC, h0, map_zero, mul_zero]
  rw [secFun_map_int]
  exact hz.2 d hmem

/- English proof (translation)
Simplify using `only [secFun, eval_map, hom_eval₂]`. Rewrite using `[RingHom.ext_rat ((starRingEnd ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ)]`. Both sides reduce to the same expression.
-/
theorem secFun_conjPt (b : MvPolynomial J ℚ) (z : J → ℂ) :
    secFun b (conjPt z) = starRingEnd ℂ (secFun b z) := by
  simp only [secFun, eval_map, hom_eval₂]
  rw [RingHom.ext_rat ((starRingEnd ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ)]
  rfl

/- English proof (translation)
Conclude with `continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)`.
-/
theorem continuous_conjPt : Continuous (conjPt : (J → ℂ) → J → ℂ) := by
  exact continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

def conjEquiv (J : Type) [Fintype J] : (J → ℂ) ≃ᵐ (J → ℂ) where
  toFun := conjPt
  invFun := conjPt
  left_inv z := by funext i; simp [conjPt]
  right_inv z := by funext i; simp [conjPt]
  measurable_toFun := continuous_conjPt.measurable
  measurable_invFun := continuous_conjPt.measurable

/- English proof (translation)
Unfold `wgt conjPt`. Rewrite using `[hm z]`.
-/
theorem wgt_conjPt {m : ConeMetric ℂ J} (hm : IsConjInvariant m) (n : ℕ) (z : J → ℂ) :
    wgt m n (conjPt z) = wgt m n z := by
  unfold wgt conjPt
  rw [hm z]

/- English proof (translation)
Establish `hμ' : μ.map (conjEquiv J) = μ` using `hμ`. Establish `he : ∀ x, conjEquiv J x = conjPt x` using `fun x => rfl`. Simplify using `only [bGram, Matrix.of_apply]`. Rewrite using `[← integral_conj]`. Use `conv_rhs => rw [← hμ']`.

Rewrite using `[integral_map_equiv (conjEquiv J)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[he, secFun_conjPt, wgt_conjPt hm]`. Apply the tactic sequence `try ring`.
-/
theorem conj_bGram {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) (i j : Fin r) :
    starRingEnd ℂ (bGram μ (fun k => secFun (b k)) (wgt m n) i j) =
      bGram μ (fun k => secFun (b k)) (wgt m n) i j := by
  have hμ' : μ.map (conjEquiv J) = μ := hμ
  have he : ∀ x, conjEquiv J x = conjPt x := fun x => rfl
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  conv_rhs => rw [← hμ']
  rw [integral_map_equiv (conjEquiv J)]
  congr 1
  funext x
  simp [he, secFun_conjPt, wgt_conjPt hm]
  try ring

/- English proof (translation)
Establish `hsub : ∀ w₁ w₂ : NumberField.InfinitePlace ℚ, w₁ = w₂`. Introduce and unpack `⟨_, φ₁, rfl⟩ ⟨_, φ₂, rfl⟩`. Conclude with `Subtype.ext (by rw [RingHom.ext_rat φ₁ φ₂])`. Set `w₀ : NumberField.InfinitePlace ℚ` to `NumberField.InfinitePlace.mk (algebraMap ℚ ℂ)`. Establish `hemb : w₀.embedding = algebraMap ℚ ℂ` using `RingHom.ext_rat _ _`.

Establish `hmult : (w₀.mult : ℝ) = 1`. Establish `hr : w₀.IsReal` using `NumberField.InfinitePlace.isReal_iff.mpr (NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext_rat _ _))`. Simplify using `[NumberField.InfinitePlace.mult, hr]`. Simplify using `only [realGram]`. Rewrite using `[Fintype.sum_eq_single w₀ (fun w hw => absurd (hsub w w₀) hw), hmult, one_mul, hemb, ← Complex.conj_re (bGram μ (fun k => secFun (b k)) (wgt m n) k l)]`.

Use `congr 1`. Simplify using `only [bGram, Matrix.of_apply]`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Simplify using `[secFun, wgt, div_eq_mul_inv]`. Apply the tactic sequence `try ring`.
-/
theorem realGram_eq (m : ConeMetric ℂ J) (μ : Measure (J → ℂ)) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial J ℚ) (k l : Fin r) :
    realGram (K := ℚ) (fun _ => m) (fun _ => μ) n b k l =
      (bGram μ (fun k => secFun (b k)) (wgt m n) k l).re := by
  have hsub : ∀ w₁ w₂ : NumberField.InfinitePlace ℚ, w₁ = w₂ := by
    rintro ⟨_, φ₁, rfl⟩ ⟨_, φ₂, rfl⟩
    exact Subtype.ext (by rw [RingHom.ext_rat φ₁ φ₂])
  let w₀ : NumberField.InfinitePlace ℚ := NumberField.InfinitePlace.mk (algebraMap ℚ ℂ)
  have hemb : w₀.embedding = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hmult : (w₀.mult : ℝ) = 1 := by
    have hr : w₀.IsReal := NumberField.InfinitePlace.isReal_iff.mpr
      (NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext_rat _ _))
    simp [NumberField.InfinitePlace.mult, hr]
  simp only [realGram]
  rw [Fintype.sum_eq_single w₀ (fun w hw => absurd (hsub w w₀) hw), hmult, one_mul, hemb,
    ← Complex.conj_re (bGram μ (fun k => secFun (b k)) (wgt m n) k l)]
  congr 1
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  congr 1
  funext z
  simp [secFun, wgt, div_eq_mul_inv]
  try ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
