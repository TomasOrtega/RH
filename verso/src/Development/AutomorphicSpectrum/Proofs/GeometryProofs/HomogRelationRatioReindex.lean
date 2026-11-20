import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hc : (∏ i : (Σ k, J₀ k), t i.1 ^ d i) = ∏ k, t k ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ y, t k ^ d ⟨k, y⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg d hd k]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_homog {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {A : Type} [CommRing A] [Algebra ℤ A]
    (g : MRing J₀) (a : K₀ → ℕ) (hg : IsMultiHomog g a) (u : (Σ k, J₀ k) → A) (t : K₀ → A) :
    aeval (fun p => u p * t p.1) g = aeval u g * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, J₀ k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, t k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C m => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp => simp only [map_mul, hp, aeval_X]`.
-/
theorem aeval_comp_ringHom {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (u : σ → A)
    (g : MvPolynomial σ ℤ) : aeval (fun p => φ (u p)) g = φ (aeval u g) := by
  induction g using MvPolynomial.induction_on with
  | C m => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X]

/- English proof (translation)
Establish `h : b ^ n = b ^ j * b ^ (n - j)` using `by rw [← pow_add]; congr 1; omega`. Rewrite using `[h, div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem pow_mul_pow_sub_eq {F : Type} [Field F] (x b : F) (hb : b ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    x ^ j * b ^ (n - j) = (x / b) ^ j * b ^ n := by
  have h : b ^ n = b ^ j * b ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [h, div_pow]
  field_simp

/- English proof (translation)
Introduce `K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ y₀ y bk bx i q r n c a hy hqr hr hc hrel z hz hzr w hw`. Establish `hcone : ∀ g : MRing J₀, IsMultiHomog g a → mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) = MvPolynomial.C (i (aeval y₀ g)) * ∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k`. Introduce `g hg`. Establish `h1 : mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) = aeval (fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)) g`. Simplify using `only [mConeMap]`.

Rewrite using `[aeval_rename]`. Establish `e : ((fun p : (Σ k, J k) => (MvPolynomial.C (y p) : MvPolynomial K Ω) * MvPolynomial.X p.1) ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) = fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)`. Use function extensionality and compare the values at `p`. Take `⟨k, b⟩` from `p`. Simplify using `[GlobalTheory.CompanionTheory.Ar.Chg.blkV, hy]`.

Rewrite using `[e]`. Rewrite using `[h1, aeval_mul_homog g a hg (fun p => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω)) (fun k => MvPolynomial.X (bk k))]`. Use `congr 1`. Conclude with `aeval_comp_ringHom ((MvPolynomial.C : Ω →+* MvPolynomial K Ω).comp i) y₀ g`. Establish `hXq : mConeMap y (MvPolynomial.X q) = MvPolynomial.C (y q) * MvPolynomial.X r.1`.

Simplify using `[mConeMap, hqr]`. Establish `hXr : mConeMap y (MvPolynomial.X r) = MvPolynomial.C (y r) * MvPolynomial.X r.1`. Simplify using `[mConeMap]`. Set `F : MRing J` to `∑ j ∈ Finset.range (n + 1), rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j) * MvPolynomial.X q ^ j * MvPolynomial.X r ^ (n - j)`. Establish `hF : F ∈ mCoordIdeal y` using `by show mConeMap y F = 0`.

Simplify using `only [F, map_sum, map_mul, map_pow, hcone _ (hc _), hXq, hXr]`. Establish `hterm : ∀ j ∈ Finset.range (n + 1), MvPolynomial.C (i (aeval y₀ (c j))) * (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) * (MvPolynomial.C (y q) * MvPolynomial.X r.1) ^ j * (MvPolynomial.C (y r) * MvPolynomial.X r.1) ^ (n - j) = (∏ k, (MvPolynomial.X (bk k) : MvPolynomia …`. Introduce `j hj`. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Establish `e1 : y q ^ j * y r ^ (n - j) = (y q / y r) ^ j * y r ^ n` using `pow_mul_pow_sub_eq _ _ hr hjn`.

Establish `e2 : (MvPolynomial.X r.1 : MvPolynomial K Ω) ^ n = MvPolynomial.X r.1 ^ j * MvPolynomial.X r.1 ^ (n - j)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `e3 : (MvPolynomial.C (y q) : MvPolynomial K Ω) ^ j * MvPolynomial.C (y r) ^ (n - j) = MvPolynomial.C ((y q / y r) ^ j * y r ^ n)`.

Rewrite using `[← e1]`. Simplify using `only [map_mul, map_pow]`. Rewrite using `[mul_pow, mul_pow, e2]`. Establish `e4 : (MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) : MvPolynomial K Ω) = MvPolynomial.C (i (aeval y₀ (c j))) * MvPolynomial.C ((y q / y r) ^ j * y r ^ n)`. Rewrite using `[← map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4, ← e3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, hrel]`.

Simplify using the standard rewrite rules. Take `⟨s, hs, he⟩` from `hw`. Establish `hev` using `hz.2 F hF`. Establish `hren : ∀ j, eval z (map (Int.castRingHom ℂ) (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j))) = (∏ k, s k ^ a k) * eval w (map (Int.castRingHom ℂ) (c j))`. Introduce `j`.

Rewrite using `[map_rename, eval_rename]`. Establish `: z ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx = fun p => s p.1 * w p` using `he`. Rewrite using `[this, eval_smul_homog (c j) a (hc j) s w]`. Simplify using `only [F, map_sum, map_mul, map_pow, map_X, eval_X, hren] at hev`. Establish `hP : (∏ k, s k ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)`.

Establish `hfin : (∏ k, s k ^ a k) * z r ^ n * ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0`. Rewrite using `[← hev, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Rewrite using `[mul_assoc ((∏ k, s k ^ a k) * _), pow_mul_pow_sub_eq _ _ hzr hjn]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 hfin).resolve_left (mul_ne_zero hP (pow_ne_zero _ hzr))`.
-/
theorem ratio_relation_at_complex_points :
    ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)]
      [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
      (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀)
      (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 →
      (∀ j, IsMultiHomog (c j) a) →
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) →
      ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ,
        SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w →
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ y₀ y bk bx i q r n c a hy hqr hr hc hrel z hz hzr w hw
  have hcone : ∀ g : MRing J₀, IsMultiHomog g a →
      mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        MvPolynomial.C (i (aeval y₀ g)) * ∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k := by
    intro g hg
    have h1 : mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        aeval (fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)) g := by
      simp only [mConeMap]
      rw [aeval_rename]
      have e : ((fun p : (Σ k, J k) => (MvPolynomial.C (y p) : MvPolynomial K Ω) * MvPolynomial.X p.1) ∘
          GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) =
          fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1) := by
        funext p
        obtain ⟨k, b⟩ := p
        simp [GlobalTheory.CompanionTheory.Ar.Chg.blkV, hy]
      rw [e]
    rw [h1, aeval_mul_homog g a hg (fun p => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω)) (fun k => MvPolynomial.X (bk k))]
    congr 1
    exact aeval_comp_ringHom ((MvPolynomial.C : Ω →+* MvPolynomial K Ω).comp i) y₀ g
  have hXq : mConeMap y (MvPolynomial.X q) = MvPolynomial.C (y q) * MvPolynomial.X r.1 := by
    simp [mConeMap, hqr]
  have hXr : mConeMap y (MvPolynomial.X r) = MvPolynomial.C (y r) * MvPolynomial.X r.1 := by
    simp [mConeMap]
  let F : MRing J := ∑ j ∈ Finset.range (n + 1),
    rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j) * MvPolynomial.X q ^ j * MvPolynomial.X r ^ (n - j)
  have hF : F ∈ mCoordIdeal y := by
    show mConeMap y F = 0
    simp only [F, map_sum, map_mul, map_pow, hcone _ (hc _), hXq, hXr]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        MvPolynomial.C (i (aeval y₀ (c j))) * (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) *
            (MvPolynomial.C (y q) * MvPolynomial.X r.1) ^ j * (MvPolynomial.C (y r) * MvPolynomial.X r.1) ^ (n - j) =
          (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) * MvPolynomial.X r.1 ^ n *
            MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have e1 : y q ^ j * y r ^ (n - j) = (y q / y r) ^ j * y r ^ n := pow_mul_pow_sub_eq _ _ hr hjn
      have e2 : (MvPolynomial.X r.1 : MvPolynomial K Ω) ^ n = MvPolynomial.X r.1 ^ j * MvPolynomial.X r.1 ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (MvPolynomial.C (y q) : MvPolynomial K Ω) ^ j * MvPolynomial.C (y r) ^ (n - j) =
          MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← e1]; simp only [map_mul, map_pow]
      rw [mul_pow, mul_pow, e2]
      have e4 : (MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) : MvPolynomial K Ω) =
          MvPolynomial.C (i (aeval y₀ (c j))) * MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← map_mul]; congr 1; ring
      rw [e4, ← e3]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, hrel]
    simp
  obtain ⟨s, hs, he⟩ := hw
  have hev := hz.2 F hF
  have hren : ∀ j, eval z (map (Int.castRingHom ℂ) (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j))) =
      (∏ k, s k ^ a k) * eval w (map (Int.castRingHom ℂ) (c j)) := by
    intro j
    rw [map_rename, eval_rename]
    have : z ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx = fun p => s p.1 * w p := he
    rw [this, eval_smul_homog (c j) a (hc j) s w]
  simp only [F, map_sum, map_mul, map_pow, map_X, eval_X, hren] at hev
  have hP : (∏ k, s k ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)
  have hfin : (∏ k, s k ^ a k) * z r ^ n *
      ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
    rw [← hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [mul_assoc ((∏ k, s k ^ a k) * _), pow_mul_pow_sub_eq _ _ hzr hjn]
    ring
  exact (mul_eq_zero.1 hfin).resolve_left (mul_ne_zero hP (pow_ne_zero _ hzr))

end GlobalTheory.CompanionTheory.Ar.Rel
