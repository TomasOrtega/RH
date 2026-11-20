import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Unfold `hv`. Rewrite using `[Matrix.mulVec_sub, dotProduct_sub]`.
-/
private lemma hv_sub_l {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) :
    hv M (x - y) z = hv M x z - hv M y z := by
  unfold hv
  rw [Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Unfold `hv`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
private lemma hv_smul_l {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x z : Fin n → ℂ) :
    hv M (c • x) z = c * hv M x z := by
  unfold hv
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Unfold `hv`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
private lemma hv_smul_r {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x z : Fin n → ℂ) :
    hv M x (c • z) = star c * hv M x z := by
  unfold hv
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `hv`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
private lemma hv_J {n : ℕ} {M J : Matrix (Fin n) (Fin n) ℂ} (h : Jᴴ * M * J = M) (x y : Fin n → ℂ) :
    hv M (J *ᵥ x) (J *ᵥ y) = hv M x y := by
  unfold hv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]`. Use extensionality with `i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]`. Take the linear combination `(J *ᵥ x) i * ht`.
-/
private lemma J_plus {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {t : ℂ} (ht : t * t = -1)
    (hJ : J * J = -1) (x : Fin n → ℂ) :
    J *ᵥ (x - t • J *ᵥ x) = t • (x - t • J *ᵥ x) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (J *ᵥ x) i * ht

/- English proof (translation)
Establish `hx : x = t • y` using `sub_eq_zero.mp h`. Rewrite using `[hx, smul_smul, neg_mul, ht, neg_neg, one_smul]`.
-/
private lemma of_plus_zero {n : ℕ} {t : ℂ} (ht : t * t = -1) {x y : Fin n → ℂ}
    (h : x - t • y = 0) : y = (-t) • x := by
  have hx : x = t • y := sub_eq_zero.mp h
  rw [hx, smul_smul, neg_mul, ht, neg_neg, one_smul]

/- English proof (translation)
Establish `h1` using `hp z hz`. Rewrite `h1` using `[hJz, hv_smul_l, ← _root_.mul_assoc, neg_mul, ht, neg_neg, _root_.one_mul]`. Conclude with `h1`.
-/
private lemma eig_pos {n : ℕ} {M J : Matrix (Fin n) (Fin n) ℂ} {t : ℂ} (ht : t * t = -1)
    (hp : ∀ x, x ≠ 0 → 0 < (-t * hv M (J *ᵥ x) x).re) {z : Fin n → ℂ} (hz : z ≠ 0)
    (hJz : J *ᵥ z = t • z) : 0 < (hv M z z).re := by
  have h1 := hp z hz
  rw [hJz, hv_smul_l, ← _root_.mul_assoc, neg_mul, ht, neg_neg, _root_.one_mul] at h1
  exact h1

/- English proof (translation)
Establish `hpos : ∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re` using `fun z hz hJz => eig_pos ht hp hz hJz`. Establish `hall : (∀ x, x - t • J *ᵥ x = 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ)`. Introduce `h0`. Establish `hx : ∀ x, J *ᵥ x = (-t) • x` using `fun x => of_plus_zero ht (h0 x)`. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises.

Introduce `i`. Simplify using `only [hx]`. Use extensionality with `k`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality.

Simplify using `[Pi.single_apply, Matrix.one_apply]`. Simplify using `[Pi.single_apply, Matrix.one_apply, h]`. Use `⟨hpos, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hneg`. Apply `hall` to reduce the goal to its premises.

Introduce `x`. Assume the negation of the conclusion as `hv0`. Establish `h1` using `hpos _ hv0 (J_plus ht hJ x)`. Establish `h2` using `hneg _ hv0`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨z, hz⟩`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `h0 : ∀ x, x - t • J *ᵥ x = 0`. Introduce `x`.

Assume the negation of the conclusion as `hv0`. Conclude with `hno _ hv0 (J_plus ht hJ x)`. Establish `hx : ∀ x, J *ᵥ x = (-t) • x` using `fun x => of_plus_zero ht (h0 x)`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Simplify using `[hv] at hz`. Establish `h1` using `hp z hz0`. Rewrite `h1` using `[hx, hv_smul_l, ← _root_.mul_assoc, neg_mul_neg, ht, neg_one_mul, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `z hz hperp hJz x`.

Establish `hzz : hv M z z ≠ 0`. Introduce `h`. Rewrite `hz` using `[h]`. Simplify using `at hz`. Use `set c := hv M x z / hv M z z with hc`.

Use `set w := x - c • z with hw`. Establish `hwz : hv M w z = 0`. Rewrite using `[hw, hv_sub_l, hv_smul_l, hc, div_mul_cancel₀ _ hzz, sub_self]`. Establish `hJwz : hv M (J *ᵥ w) z = 0`. Establish `e1` using `hv_J hP w z`.

Rewrite `e1` using `[hJz, hv_smul_r, hwz]`. Establish `ht0 : star t ≠ 0`. Introduce `h0`. Rewrite `h0` using `[star_eq_zero]`. Rewrite `ht` using `[h0, zero_mul]`.

Evaluate the numerical expressions using `at ht`. Conclude with `(mul_eq_zero.mp e1).resolve_left ht0`. Establish `hJw : J *ᵥ w = (-t) • w`. Apply `of_plus_zero ht` to reduce the goal to its premises. Assume the negation of the conclusion as `hu`.

Establish `h1` using `hpos _ hu (J_plus ht hJ w)`. Establish `h2` using `hperp _ hu (by rw [hv_sub_l, hv_smul_l, hwz, hJwz, mul_zero, sub_zero])`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxw : x = w + c • z` using `by rw [hw, sub_add_cancel]`. Rewrite using `[hxw, Matrix.mulVec_add, hJw, Matrix.mulVec_smul, hJz]`.

Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma core {n : ℕ} (M J : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) (ht : t * t = -1)
    (hJ : J * J = -1) (hP : Jᴴ * M * J = M)
    (hp : ∀ x, x ≠ 0 → 0 < (-t * hv M (J *ᵥ x) x).re) :
    (∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = t • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = t • z →
      ∀ x, J *ᵥ x = t • ((2 * (hv M x z / hv M z z)) • z - x) := by
  have hpos : ∀ z, z ≠ 0 → J *ᵥ z = t • z → 0 < (hv M z z).re := fun z hz hJz => eig_pos ht hp hz hJz
  have hall : (∀ x, x - t • J *ᵥ x = 0) → J = (-t) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro h0
    have hx : ∀ x, J *ᵥ x = (-t) • x := fun x => of_plus_zero ht (h0 x)
    apply Matrix.ext_of_mulVec_single
    intro i
    simp only [hx]
    ext k
    by_cases h : k = i
    · subst h
      simp [Pi.single_apply, Matrix.one_apply]
    · simp [Pi.single_apply, Matrix.one_apply, h]
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro hneg
    apply hall
    intro x
    by_contra hv0
    have h1 := hpos _ hv0 (J_plus ht hJ x)
    have h2 := hneg _ hv0
    linarith
  · rintro ⟨z, hz⟩
    by_contra hno
    push_neg at hno
    have h0 : ∀ x, x - t • J *ᵥ x = 0 := by
      intro x
      by_contra hv0
      exact hno _ hv0 (J_plus ht hJ x)
    have hx : ∀ x, J *ᵥ x = (-t) • x := fun x => of_plus_zero ht (h0 x)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [hv] at hz
    have h1 := hp z hz0
    rw [hx, hv_smul_l, ← _root_.mul_assoc, neg_mul_neg, ht, neg_one_mul, Complex.neg_re] at h1
    linarith
  · intro z hz hperp hJz x
    have hzz : hv M z z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
    set c := hv M x z / hv M z z with hc
    set w := x - c • z with hw
    have hwz : hv M w z = 0 := by
      rw [hw, hv_sub_l, hv_smul_l, hc, div_mul_cancel₀ _ hzz, sub_self]
    have hJwz : hv M (J *ᵥ w) z = 0 := by
      have e1 := hv_J hP w z
      rw [hJz, hv_smul_r, hwz] at e1
      have ht0 : star t ≠ 0 := by
        intro h0
        rw [star_eq_zero] at h0
        rw [h0, zero_mul] at ht
        norm_num at ht
      exact (mul_eq_zero.mp e1).resolve_left ht0
    have hJw : J *ᵥ w = (-t) • w := by
      apply of_plus_zero ht
      by_contra hu
      have h1 := hpos _ hu (J_plus ht hJ w)
      have h2 := hperp _ hu (by rw [hv_sub_l, hv_smul_l, hwz, hJwz, mul_zero, sub_zero])
      linarith
    have hxw : x = w + c • z := by rw [hw, sub_add_cancel]
    rw [hxw, Matrix.mulVec_add, hJw, Matrix.mulVec_smul, hJz]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/- English proof (translation)
Introduce `n M J s hM hs hPJ`. Take `⟨hJ, hP, hp⟩` from `hPJ`. Establish `ht : (s * Complex.I) * (s * Complex.I) = -1`. Apply the tactic sequence `rcases hs with rfl | rfl <;> simp`. Establish `hp' : ∀ x, x ≠ 0 → 0 < (-(s * Complex.I) * hv M (J *ᵥ x) x).re`.

Introduce `x hx`. Establish `h1` using `hp x hx`. Rewrite `h1` using `[neg_mul]`. Then use the resulting hypothesis. Conclude with `core M J (s * Complex.I) ht hJ hP hp'`.
-/
theorem UpperTheory.Gal.W2.jLine_of :
    UpperTheory.Gal.W2.JLine := by
  intro n M J s hM hs hPJ
  obtain ⟨hJ, hP, hp⟩ := hPJ
  have ht : (s * Complex.I) * (s * Complex.I) = -1 := by
    rcases hs with rfl | rfl <;> simp
  have hp' : ∀ x, x ≠ 0 → 0 < (-(s * Complex.I) * hv M (J *ᵥ x) x).re := by
    intro x hx
    have h1 := hp x hx
    rwa [neg_mul] at h1
  exact core M J (s * Complex.I) ht hJ hP hp'
