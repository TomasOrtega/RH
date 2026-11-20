import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord

variable {I : Type} [Fintype I] [DecidableEq I]

/- English proof (translation)
Establish `hs : ∀ (c : I) (γ : ℂ), star (Pi.single c γ : I → ℂ) = Pi.single c (star γ)`. Introduce `c γ`. Use extensionality with `i`. Distinguish the cases in `hi : i = c`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hi]`. Establish `he : ∀ (T : Matrix I I ℂ) (a b : I) (α β : ℂ), (Pi.single a α : I → ℂ) ⬝ᵥ T *ᵥ (Pi.single b β : I → ℂ) = α * β * T a b`. Introduce `T a b α β`. Simplify using `[single_dotProduct, mulVec, dotProduct_single]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ (a b : I) (α β : ℂ), (α * star β * P a b + α * β * Q a b + star α * star β * R a b + star α * β * S a b).im = 0`. Introduce `a b α β`. Use `h (Pi.single a α) (Pi.single b β)` as an intermediate fact. Rewrite `this` using `[hs, hs, he, he, he, he]`.

Conclude with `this`. Establish `h4 : ∀ a b, (P a b).re = (S a b).re ∧ (P a b).im = -(S a b).im ∧ (Q a b).re = (R a b).re ∧ (Q a b).im = -(R a b).im`. Introduce `a b`. Establish `h1` using `key a b 1 1`. Establish `h2` using `key a b Complex.I 1`.

Establish `h3` using `key a b 1 Complex.I`. Establish `h4` using `key a b Complex.I Complex.I`. Simplify using `[Complex.mul_im, Complex.add_im] at h1 h2 h3 h4`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith`. Prove the components needed by the constructor for the conclusion.

Use extensionality with `a b`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using (h4 a b).1`. Simplify using `using (h4 a b).2.1`. Use extensionality with `a b`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using (h4 a b).2.2.1`. Simplify using `using (h4 a b).2.2.2`.
-/
theorem im_terms_separate (P Q R S : Matrix I I ℂ)
    (h : ∀ z w : I → ℂ, (z ⬝ᵥ P *ᵥ star w + z ⬝ᵥ Q *ᵥ w + star z ⬝ᵥ R *ᵥ star w
      + star z ⬝ᵥ S *ᵥ w).im = 0) :
    P = S.map star ∧ Q = R.map star := by
  have hs : ∀ (c : I) (γ : ℂ), star (Pi.single c γ : I → ℂ) = Pi.single c (star γ) := by
    intro c γ; ext i; by_cases hi : i = c
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  have he : ∀ (T : Matrix I I ℂ) (a b : I) (α β : ℂ),
      (Pi.single a α : I → ℂ) ⬝ᵥ T *ᵥ (Pi.single b β : I → ℂ) = α * β * T a b := by
    intro T a b α β
    simp [single_dotProduct, mulVec, dotProduct_single]
    ring
  have key : ∀ (a b : I) (α β : ℂ), (α * star β * P a b + α * β * Q a b
      + star α * star β * R a b + star α * β * S a b).im = 0 := by
    intro a b α β
    have := h (Pi.single a α) (Pi.single b β)
    rw [hs, hs, he, he, he, he] at this
    exact this
  have h4 : ∀ a b, (P a b).re = (S a b).re ∧ (P a b).im = -(S a b).im ∧
      (Q a b).re = (R a b).re ∧ (Q a b).im = -(R a b).im := by
    intro a b
    have h1 := key a b 1 1
    have h2 := key a b Complex.I 1
    have h3 := key a b 1 Complex.I
    have h4 := key a b Complex.I Complex.I
    simp [Complex.mul_im, Complex.add_im] at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  constructor
  · ext a b
    apply Complex.ext
    · simpa using (h4 a b).1
    · simpa using (h4 a b).2.1
  · ext a b
    apply Complex.ext
    · simpa using (h4 a b).2.2.1
    · simpa using (h4 a b).2.2.2

/- English proof (translation)
Use `⟨Matrix.of fun i j => (L (Pi.single j 1) i - Complex.I * L (Pi.single j Complex.I) i) / 2, Matrix.of fun i j => (L (Pi.single j 1) i + Complex.I * L (Pi.single j Complex.I) i) / 2, ?_⟩` and prove the remaining obligations. Introduce `z`. Establish `hz : z = ∑ j, ((z j).re • (Pi.single j 1 : I → ℂ) + (z j).im • (Pi.single j Complex.I : I → ℂ))`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]`.

Establish `hL : L z = ∑ j, ((z j).re • L (Pi.single j 1) + (z j).im • L (Pi.single j Complex.I))` using `by conv_lhs => rw [hz]`. Simplify using `[map_sum, map_add, map_smul]`. Rewrite using `[hL]`. Use extensionality with `i`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, mulVec, dotProduct, Matrix.of_apply, Pi.star_apply, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `aux : ∀ (a b : ℂ) (x y : ℝ), (x : ℂ) * a + y * b = (a - Complex.I * b) / 2 * (x + y * Complex.I) + (a + Complex.I * b) / 2 * (x - y * Complex.I)`. Introduce `a b x y`. Establish `hI` using `Complex.I_mul_I`. Take the linear combination `((y : ℂ) * b) * hI`.

Establish `hc : star (z j) = (z j).re - (z j).im * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hz' : z j = (z j).re + (z j).im * Complex.I` using `(Complex.re_add_im _).symm`. Simplify using `only [Complex.real_smul]`. Rewrite using `[aux, hc, ← hz']`.
-/
theorem exists_linear_antilinear (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) :
    ∃ M D : Matrix I I ℂ, ∀ z, L z = M *ᵥ z + D *ᵥ star z := by
  refine ⟨Matrix.of fun i j => (L (Pi.single j 1) i - Complex.I * L (Pi.single j Complex.I) i) / 2,
    Matrix.of fun i j => (L (Pi.single j 1) i + Complex.I * L (Pi.single j Complex.I) i) / 2, ?_⟩
  intro z
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : I → ℂ) + (z j).im • (Pi.single j Complex.I : I → ℂ)) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hL : L z = ∑ j, ((z j).re • L (Pi.single j 1) + (z j).im • L (Pi.single j Complex.I)) := by
    conv_lhs => rw [hz]
    simp [map_sum, map_add, map_smul]
  rw [hL]
  ext i
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, mulVec, dotProduct, Matrix.of_apply,
    Pi.star_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have aux : ∀ (a b : ℂ) (x y : ℝ), (x : ℂ) * a + y * b =
      (a - Complex.I * b) / 2 * (x + y * Complex.I) + (a + Complex.I * b) / 2 * (x - y * Complex.I) := by
    intro a b x y
    have hI := Complex.I_mul_I
    linear_combination ((y : ℂ) * b) * hI
  have hc : star (z j) = (z j).re - (z j).im * Complex.I := by
    apply Complex.ext <;> simp
  have hz' : z j = (z j).re + (z j).im * Complex.I := (Complex.re_add_im _).symm
  simp only [Complex.real_smul]
  rw [aux, hc, ← hz']

/- English proof (translation)
Use extensionality with `i`. Simplify using `[mulVec, dotProduct]`.
-/
theorem star_mulVec_star (Z : Matrix I I ℂ) (w : I → ℂ) :
    star (Z *ᵥ star w) = Z.map star *ᵥ w := by
  ext i
  simp [mulVec, dotProduct]

/- English proof (translation)
Establish `hv : ∀ (y v : I → ℂ), (Z *ᵥ y) ⬝ᵥ v = y ⬝ᵥ Zᵀ *ᵥ v`. Introduce `y v`. Rewrite using `[dotProduct_mulVec, vecMul_transpose]`. Simplify using `only [tz, star_sub, star_mulVec_star, mulVec_sub, sub_dotProduct, dotProduct_sub, hv, mulVec_mulVec, neg_mulVec, dotProduct_neg, Matrix.mul_assoc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_tz (G Z : Matrix I I ℂ) (z w : I → ℂ) :
    tz Z z ⬝ᵥ G *ᵥ star (tz Z w) = z ⬝ᵥ G *ᵥ star w + z ⬝ᵥ (-(G * Z.map star)) *ᵥ w
      + star z ⬝ᵥ (-(Zᵀ * G)) *ᵥ star w + star z ⬝ᵥ (Zᵀ * G * Z.map star) *ᵥ w := by
  have hv : ∀ (y v : I → ℂ), (Z *ᵥ y) ⬝ᵥ v = y ⬝ᵥ Zᵀ *ᵥ v := by
    intro y v
    rw [dotProduct_mulVec, vecMul_transpose]
  simp only [tz, star_sub, star_mulVec_star, mulVec_sub, sub_dotProduct, dotProduct_sub, hv,
    mulVec_mulVec, neg_mulVec, dotProduct_neg, Matrix.mul_assoc]
  ring

/- English proof (translation)
Establish `h1 : star (M *ᵥ b) = M.map star *ᵥ star b`. Use `star_mulVec_star M (star b)` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis. Establish `hv : ∀ (y v : I → ℂ), (M *ᵥ y) ⬝ᵥ v = y ⬝ᵥ Mᵀ *ᵥ v`. Introduce `y v`.

Rewrite using `[dotProduct_mulVec, vecMul_transpose]`. Rewrite using `[h1, hv, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem form_pullback (H M : Matrix I I ℂ) (a b : I → ℂ) :
    (M *ᵥ a) ⬝ᵥ H *ᵥ star (M *ᵥ b) = a ⬝ᵥ (Mᵀ * H * M.map star) *ᵥ star b := by
  have h1 : star (M *ᵥ b) = M.map star *ᵥ star b := by
    have := star_mulVec_star M (star b)
    rwa [star_star] at this
  have hv : ∀ (y v : I → ℂ), (M *ᵥ y) ⬝ᵥ v = y ⬝ᵥ Mᵀ *ᵥ v := by
    intro y v
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [h1, hv, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos hG fun x hx => ?_` and prove the remaining obligations. Establish `h` using `hp (star x) (by simpa using hx)`. Rewrite `h` using `[star_star]`. Rewrite using `[Complex.lt_def]`. Conclude with `⟨by simpa using h, by simpa using (hG.im_star_dotProduct_mulVec_self x).symm⟩`.
-/
theorem posDef_of_form (G : Matrix I I ℂ) (hG : G.IsHermitian)
    (hp : ∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ G *ᵥ star z).re) : G.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hG fun x hx => ?_
  have h := hp (star x) (by simpa using hx)
  rw [star_star] at h
  rw [Complex.lt_def]
  exact ⟨by simpa using h, by simpa using (hG.im_star_dotProduct_mulVec_self x).symm⟩

/- English proof (translation)
Use `set Zc := Z.map star with hZc`. Use `set Gc := G.map star with hGc`. Establish `hcc : Zc.map star = Z` using `by ext; simp [hZc]`. Establish `hgc : Gc.map star = G` using `by ext; simp [hGc]`. Establish `hct : Zᴴ = Zcᵀ` using `by ext; simp [hZc, conjTranspose_apply]`.

Establish `mapmul : ∀ A B : Matrix I I ℂ, (A * B).map star = A.map star * B.map star`. Introduce `A B`. Use extensionality with `i j`. Simplify using `[mul_apply]`. Establish `mapone : (1 : Matrix I I ℂ).map star = 1`.

Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [one_apply, h]`. Establish `mapsub : ∀ A B : Matrix I I ℂ, (A - B).map star = A.map star - B.map star`. Introduce `A B`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Establish `mapneg : ∀ A : Matrix I I ℂ, (-A).map star = -A.map star`. Introduce `A`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `maptr : Zᵀ.map star = Zᴴ` using `by ext; simp [conjTranspose_apply]`.

Establish `r1 : G - 1 = Zᴴ * Gc * Z` using `by rw [e1, mapmul, mapmul, maptr, hcc]`. Establish `r2 : G * Zc = Zᴴ * Gc`. Use `e2` as an intermediate fact. Rewrite `this` using `[mapneg, mapmul, maptr]`. Conclude with `neg_injective this`.

Establish `hU : G * (1 - Zc * Z) = 1`. Establish `: G - 1 = G * Zc * Z` using `by rw [r1, r2]`. Rewrite using `[mul_sub, mul_one, ← mul_assoc, ← this]`. Normalize the expressions using the abelian group laws. Establish `hV : Gc * (1 - Z * Zc) = 1`.

Use `congrArg (Matrix.map · star) hU` as an intermediate fact. Simplify using `only [mapmul, mapsub, mapone, hcc] at this`. Conclude with `this`. Establish `hU' : (1 - Zc * Z) * G = 1` using `mul_eq_one_comm.mp hU`. Establish `hV' : (1 - Z * Zc) * Gc = 1` using `mul_eq_one_comm.mp hV`.

Establish `hcomm : (1 - Zc * Z) * Zc = Zc * (1 - Z * Zc)`. Simplify using `only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]`. Establish `h3 : G * Zc = Zc * Gc`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : Zc = Zᴴ`.

Establish `: Zc * Gc = Zᴴ * Gc` using `by rw [← h3, r2]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `congrArg (Matrix.map · star) h4` as an intermediate fact. Simplify using `only [hcc] at this`.

Use extensionality with `i j`. Establish `h` using `congrFun (congrFun this j) i`. Simplify `h` using `[conjTranspose_apply]`. Rewrite using `[← h4]`. Establish `hinv : (1 - Zc * Z) = G⁻¹` using `(Matrix.inv_eq_right_inv hU).symm`.

Rewrite using `[hinv]`. Conclude with `hG.inv`.
-/
theorem symm_posDef_of_relations (G Z : Matrix I I ℂ) (hG : G.PosDef)
    (e1 : G - 1 = (Zᵀ * G * Z.map star).map star)
    (e2 : -(G * Z.map star) = (-(Zᵀ * G)).map star) :
    Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef := by
  set Zc := Z.map star with hZc
  set Gc := G.map star with hGc
  have hcc : Zc.map star = Z := by ext; simp [hZc]
  have hgc : Gc.map star = G := by ext; simp [hGc]
  have hct : Zᴴ = Zcᵀ := by ext; simp [hZc, conjTranspose_apply]
  have mapmul : ∀ A B : Matrix I I ℂ, (A * B).map star = A.map star * B.map star := by
    intro A B; ext i j; simp [mul_apply]
  have mapone : (1 : Matrix I I ℂ).map star = 1 := by
    ext i j; by_cases h : i = j <;> simp [one_apply, h]
  have mapsub : ∀ A B : Matrix I I ℂ, (A - B).map star = A.map star - B.map star := by
    intro A B; ext i j; simp
  have mapneg : ∀ A : Matrix I I ℂ, (-A).map star = -A.map star := by
    intro A; ext i j; simp
  have maptr : Zᵀ.map star = Zᴴ := by ext; simp [conjTranspose_apply]

  have r1 : G - 1 = Zᴴ * Gc * Z := by rw [e1, mapmul, mapmul, maptr, hcc]
  have r2 : G * Zc = Zᴴ * Gc := by
    have := e2
    rw [mapneg, mapmul, maptr] at this
    exact neg_injective this
  have hU : G * (1 - Zc * Z) = 1 := by
    have : G - 1 = G * Zc * Z := by rw [r1, r2]
    rw [mul_sub, mul_one, ← mul_assoc, ← this]
    abel
  have hV : Gc * (1 - Z * Zc) = 1 := by
    have := congrArg (Matrix.map · star) hU
    simp only [mapmul, mapsub, mapone, hcc] at this
    exact this
  have hU' : (1 - Zc * Z) * G = 1 := mul_eq_one_comm.mp hU
  have hV' : (1 - Z * Zc) * Gc = 1 := mul_eq_one_comm.mp hV
  have hcomm : (1 - Zc * Z) * Zc = Zc * (1 - Z * Zc) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
  have h3 : G * Zc = Zc * Gc := by
    calc G * Zc = G * Zc * ((1 - Z * Zc) * Gc) := by rw [hV', mul_one]
      _ = G * (Zc * (1 - Z * Zc)) * Gc := by simp only [mul_assoc]
      _ = G * ((1 - Zc * Z) * Zc) * Gc := by rw [hcomm]
      _ = (G * (1 - Zc * Z)) * Zc * Gc := by simp only [mul_assoc]
      _ = Zc * Gc := by rw [hU, one_mul]
  have h4 : Zc = Zᴴ := by
    have : Zc * Gc = Zᴴ * Gc := by rw [← h3, r2]
    calc Zc = Zc * (Gc * (1 - Z * Zc)) := by rw [hV, mul_one]
      _ = (Zc * Gc) * (1 - Z * Zc) := by rw [mul_assoc]
      _ = (Zᴴ * Gc) * (1 - Z * Zc) := by rw [this]
      _ = Zᴴ * (Gc * (1 - Z * Zc)) := by rw [mul_assoc]
      _ = Zᴴ := by rw [hV, mul_one]
  refine ⟨?_, ?_⟩
  · have := congrArg (Matrix.map · star) h4
    simp only [hcc] at this
    ext i j
    have h := congrFun (congrFun this j) i
    simpa [conjTranspose_apply] using h
  · rw [← h4]
    have hinv : (1 - Zc * Z) = G⁻¹ := (Matrix.inv_eq_right_inv hU).symm
    rw [hinv]
    exact hG.inv

/- English proof (translation)
Establish `hker : ∀ x : I → ℂ, M *ᵥ x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `h1 : L x = D *ᵥ star x` using `by rw [hL, hx, zero_add]`. Establish `hsI : ∀ y : I → ℂ, star (Complex.I • y) = (-Complex.I) • star y`.

Introduce `y`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `h2 : L (Complex.I • x) = (-Complex.I) • L x`. Rewrite using `[hL, hsI, mulVec_smul, mulVec_smul, hx, smul_zero, zero_add, h1]`.

Establish `hsI' : star ((-Complex.I) • L x) = Complex.I • star (L x)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `h3` using `hform x (Complex.I • x)`. Rewrite `h3` using `[h2, hsI', hsI, mulVec_smul, dotProduct_smul, dotProduct_smul]`.

Establish `h4 : 0 ≤ (L x ⬝ᵥ H *ᵥ star (L x)).re`. Distinguish the cases in `h0 : L x = 0`. Simplify using `[h0]`. Conclude with `(hpos _ h0).le`. Establish `h5 : 0 < x ⬝ᵥ star x`.

Rewrite using `[dotProduct_comm]`. Conclude with `dotProduct_star_self_pos_iff.mpr hne`. Rewrite `h5` using `[Complex.lt_def]`. Simplify using `at h3 h5`. Combine the linear relations using `[h5.1]`.

Introduce `x y hxy`. Establish `: M *ᵥ (x - y) = 0` using `by rw [mulVec_sub, hxy, sub_self]`. Conclude with `sub_eq_zero.mp (hker _ this)`.
-/
theorem linear_part_injective (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H M D : Matrix I I ℂ)
    (hpos : ∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re)
    (hform : ∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im)
    (hL : ∀ z, L z = M *ᵥ z + D *ᵥ star z) : Function.Injective M.mulVec := by
  have hker : ∀ x : I → ℂ, M *ᵥ x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have h1 : L x = D *ᵥ star x := by rw [hL, hx, zero_add]
    have hsI : ∀ y : I → ℂ, star (Complex.I • y) = (-Complex.I) • star y := by
      intro y; ext i; simp
    have h2 : L (Complex.I • x) = (-Complex.I) • L x := by
      rw [hL, hsI, mulVec_smul, mulVec_smul, hx, smul_zero, zero_add, h1]
    have hsI' : star ((-Complex.I) • L x) = Complex.I • star (L x) := by
      ext i; simp
    have h3 := hform x (Complex.I • x)
    rw [h2, hsI', hsI, mulVec_smul, dotProduct_smul, dotProduct_smul] at h3
    have h4 : 0 ≤ (L x ⬝ᵥ H *ᵥ star (L x)).re := by
      by_cases h0 : L x = 0
      · simp [h0]
      · exact (hpos _ h0).le
    have h5 : 0 < x ⬝ᵥ star x := by
      rw [dotProduct_comm]; exact dotProduct_star_self_pos_iff.mpr hne
    rw [Complex.lt_def] at h5
    simp at h3 h5
    linarith [h5.1]
  intro x y hxy
  have : M *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker _ this)

/- English proof (translation)
Take `⟨M, D, hL⟩` from `exists_linear_antilinear L`. Establish `hinj` using `linear_part_injective L H M D hpos hform hL`. Establish `hU : IsUnit M` using `mulVec_injective_iff_isUnit.mp hinj`. Establish `hdet : IsUnit M.det` using `(Matrix.isUnit_iff_isUnit_det M).mp hU`. Use `set Z : Matrix I I ℂ := -(M⁻¹ * D) with hZ`.

Establish `hLZ : ∀ z, L z = M *ᵥ tz Z z`. Introduce `z`. Rewrite using `[hL, tz, mulVec_sub, mulVec_mulVec, hZ, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv M hdet, Matrix.one_mul, neg_mulVec, sub_neg_eq_add]`. Use `set G : Matrix I I ℂ := Mᵀ * H * M.map star with hGdef`. Establish `hGh : G.IsHermitian`.

Establish `hM : (M.map star)ᴴ = Mᵀ` using `by ext; simp [conjTranspose_apply]`. Establish `hM' : (Mᵀ)ᴴ = M.map star` using `by ext; simp [conjTranspose_apply]`. Rewrite using `[IsHermitian, hGdef, conjTranspose_mul, conjTranspose_mul, hM, hM', hH.eq, Matrix.mul_assoc]`. Establish `hGpd : G.PosDef`. Use `posDef_of_form G hGh fun z hz => ?_` and prove the remaining obligations.

Rewrite using `[hGdef, ← form_pullback]`. Use `hpos _ fun h0 => hz (hinj ?_)` and prove the remaining obligations. Rewrite using `[h0, mulVec_zero]`. Establish `hrel : ∀ z w : I → ℂ, (z ⬝ᵥ (G - 1) *ᵥ star w + z ⬝ᵥ (-(G * Z.map star)) *ᵥ w + star z ⬝ᵥ (-(Zᵀ * G)) *ᵥ star w + star z ⬝ᵥ (Zᵀ * G * Z.map star) *ᵥ w).im = 0`. Introduce `z w`.

Establish `h` using `hform z w`. Rewrite `h` using `[hLZ, hLZ, form_pullback, form_tz]`. Rewrite using `[sub_mulVec, one_mulVec, dotProduct_sub]`. Simplify using `only [Complex.add_im, Complex.sub_im] at h ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨e1, e2⟩` from `im_terms_separate _ _ _ _ hrel`. Take `⟨hs, hp⟩` from `symm_posDef_of_relations G Z hGpd e1 e2`. Use `⟨LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) ?_, Z, hs, hp, fun z => ?_⟩` and prove the remaining obligations. Introduce `a b h`. Rewrite `h` using `[Matrix.toLin'_apply, Matrix.toLin'_apply]`.

Conclude with `hinj h`. Rewrite using `[hLZ]`. Conclude with `(Matrix.toLin'_apply M (tz Z z)).symm`.
-/
theorem exists_linearEquiv_tz {I : Type} [Fintype I] [DecidableEq I]
    (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (hpos : ∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re)
    (hform : ∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im) :
    ∃ (A : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (Z : Matrix I I ℂ), Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef ∧
      ∀ z, L z = A (tz Z z) := by
  obtain ⟨M, D, hL⟩ := exists_linear_antilinear L
  have hinj := linear_part_injective L H M D hpos hform hL
  have hU : IsUnit M := mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hU
  set Z : Matrix I I ℂ := -(M⁻¹ * D) with hZ
  have hLZ : ∀ z, L z = M *ᵥ tz Z z := by
    intro z
    rw [hL, tz, mulVec_sub, mulVec_mulVec, hZ, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv M hdet, Matrix.one_mul, neg_mulVec, sub_neg_eq_add]
  set G : Matrix I I ℂ := Mᵀ * H * M.map star with hGdef
  have hGh : G.IsHermitian := by
    have hM : (M.map star)ᴴ = Mᵀ := by ext; simp [conjTranspose_apply]
    have hM' : (Mᵀ)ᴴ = M.map star := by ext; simp [conjTranspose_apply]
    rw [IsHermitian, hGdef, conjTranspose_mul, conjTranspose_mul, hM, hM', hH.eq, Matrix.mul_assoc]
  have hGpd : G.PosDef := by
    refine posDef_of_form G hGh fun z hz => ?_
    rw [hGdef, ← form_pullback]
    refine hpos _ fun h0 => hz (hinj ?_)
    rw [h0, mulVec_zero]
  have hrel : ∀ z w : I → ℂ, (z ⬝ᵥ (G - 1) *ᵥ star w + z ⬝ᵥ (-(G * Z.map star)) *ᵥ w
      + star z ⬝ᵥ (-(Zᵀ * G)) *ᵥ star w + star z ⬝ᵥ (Zᵀ * G * Z.map star) *ᵥ w).im = 0 := by
    intro z w
    have h := hform z w
    rw [hLZ, hLZ, form_pullback, form_tz] at h
    rw [sub_mulVec, one_mulVec, dotProduct_sub]
    simp only [Complex.add_im, Complex.sub_im] at h ⊢
    linarith
  obtain ⟨e1, e2⟩ := im_terms_separate _ _ _ _ hrel
  obtain ⟨hs, hp⟩ := symm_posDef_of_relations G Z hGpd e1 e2
  refine ⟨LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) ?_, Z, hs, hp, fun z => ?_⟩
  · intro a b h
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
    exact hinj h
  · rw [hLZ]
    exact (Matrix.toLin'_apply M (tz Z z)).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord
