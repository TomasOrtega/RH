import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open PureTypeVector in

/- English proof (translation)
Introduce `g Λ w L Hm Ef hg hw hΛ hH hpos hEf hbij z z'`. Substitute `hg` using the available equality. Use `set H := hermForm Hm w w with hHdef`. Establish `hHim : H.im = 0` using `hermForm_self_im hH w`. Establish `hHreal : H = (H.re : ℂ)` using `Complex.ext (by simp) (by simp [hHim])`.

Establish `hsm : ∀ u v : ℂ, hermForm Hm (u • w) (v • w) = u * starRingEnd ℂ v * H` using `fun u v => hermForm_smul_smul Hm u v w w`. Use `set D := (L.ω₁ * starRingEnd ℂ L.ω₂).im with hD`. Establish `hw0 : w 0 ≠ 0`. Introduce `h`. Apply `hw` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `using h`. Establish `hcoord : ∀ x : Λ, ∃ m n : ℤ, (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w`. Introduce `x`.

Establish `hx : (x : Fin 1 → ℂ) = (x.1 0 / w 0) • w`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `[div_mul_cancel₀ _ hw0]`. Establish `hmem : (x.1 0 / w 0) ∈ L.lattice` using `(hΛ _).2 (by rw [← hx]; exact x.2)`.

Take `⟨m, n, hmn⟩` from `PeriodPair.mem_lattice.1 hmem`. Conclude with `⟨m, n, by rw [hmn]; exact hx⟩`. Establish `him : ∀ m n m' n' : ℤ, (((m : ℂ) * L.ω₁ + n * L.ω₂) * starRingEnd ℂ ((m' : ℂ) * L.ω₁ + n' * L.ω₂)).im = ((m * n' - n * m' : ℤ) : ℝ) * D`. Introduce `m n m' n'`. Simplify using `only [hD, map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hEfc : ∀ (x y : Λ) (m n m' n' : ℤ), (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w → (y : Fin 1 → ℂ) = ((m' : ℂ) * L.ω₁ + n' * L.ω₂) • w → (Ef x y : ℝ) = ((m * n' - n * m' : ℤ) : ℝ) * (H.re * D)`. Introduce `x y m n m' n' hx hy`. Rewrite using `[hEf, hx, hy, hsm, Complex.mul_im, hHim, him]`.

Expand and normalize the polynomial expressions, which then agree. Establish `ha : L.ω₁ • w ∈ Λ` using `(hΛ _).1 L.ω₁_mem_lattice`. Establish `hb : L.ω₂ • w ∈ Λ` using `(hΛ _).1 L.ω₂_mem_lattice`. Set `a : Λ` to `⟨L.ω₁ • w, ha⟩`. Set `b : Λ` to `⟨L.ω₂ • w, hb⟩`.

Establish `ea : (a : Fin 1 → ℂ) = (((1 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂) • w` using `by show L.ω₁ • w = _`. Simplify using the standard rewrite rules. Establish `eb : (b : Fin 1 → ℂ) = (((0 : ℤ) : ℂ) * L.ω₁ + ((1 : ℤ) : ℂ) * L.ω₂) • w` using `by show L.ω₂ • w = _`. Simplify using the standard rewrite rules. Use `set k := Ef a b with hkdef`.

Establish `hk : (k : ℝ) = H.re * D`. Rewrite using `[hEfc a b 1 0 0 1 ea eb]`. Evaluate the numerical expressions. Establish `hdvd : ∀ x y : Λ, k ∣ Ef x y`. Introduce `x y`.

Take `⟨m, n, hx⟩` from `hcoord x`. Take `⟨m', n', hy⟩` from `hcoord y`. Use `⟨m * n' - n * m', ?_⟩` and prove the remaining obligations. Establish `h` using `hEfc x y m n m' n' hx hy`. Rewrite `h` using `[← hk, mul_comm]`.

Conclude with `h` after adjusting the coercions. Establish `hba : Ef b a = -k`. Establish `h` using `hEfc b a 0 1 1 0 eb ea`. Rewrite `h` using `[← hk]`. Establish `h' : ((Ef b a : ℤ) : ℝ) = ((-k : ℤ) : ℝ)`.

Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h'` after adjusting the coercions. Establish `hk0 : k ≠ 0`.

Introduce `hk0`. Establish `hEa : Ef a = Ef 0`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Rewrite using `[map_zero, LinearMap.zero_apply]`.

Take `⟨c, hc⟩` from `hdvd a y`. Rewrite using `[hc, hk0, zero_mul]`. Establish `ha0 : a = 0` using `hbij.1 hEa`. Establish `h0 : L.ω₁ • w = 0` using `congrArg Subtype.val ha0`. Break down `smul_eq_zero.1 h0 with h | h` into its components or cases.

Conclude with `L.indep.ne_zero 0 (by simpa using h)`. Conclude with `hw h`. Set `f : Λ →ₗ[ℤ] ℤ` to `{ toFun := fun y => Ef y a / k map_add' := fun y y' => by`. Simplify using `only [map_add, LinearMap.add_apply]`. Conclude with `Int.add_ediv_of_dvd_left (hdvd y a)`.

Use the proof step `map_smul' := fun c y => by`. Simplify using `only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]`. Conclude with `Int.mul_ediv_assoc c (hdvd y a) }`. Take `⟨x, hx⟩` from `hbij.2 f`. Establish `hxb : Ef x b = -1`.

Rewrite using `[hx]`. Use `show Ef b a / k = -1`. Rewrite using `[hba, Int.neg_ediv_of_dvd (dvd_refl k), Int.ediv_self hk0]`. Establish `hunit : k = 1 ∨ k = -1`. Establish `h` using `hdvd x b`.

Rewrite `h` using `[hxb]`. Conclude with `Int.isUnit_iff.1 (isUnit_of_dvd_one (dvd_neg.1 h))`. Establish `hHre : H.re * |D| = 1`. Establish `hpos' : 0 < H.re` using `hpos`. Break down `hunit with h | h` into its components or cases.

Establish `h1 : H.re * D = 1` using `by rw [← hk, h]; norm_num`. Establish `hD0 : 0 < D` using `by nlinarith`. Rewrite using `[abs_of_pos hD0]`. Conclude with `h1`. Establish `h1 : H.re * D = -1` using `by rw [← hk, h]; norm_num`.

Establish `hD0 : D < 0` using `by nlinarith`. Rewrite using `[abs_of_neg hD0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDabs : |D| ≠ 0`. Introduce `h0`.

Rewrite `hHre` using `[h0, mul_zero]`. Conclude with `zero_ne_one hHre`. Establish `hr : H.re = 1 / |D|`. Rewrite using `[eq_div_iff hDabs]`. Conclude with `hHre`.

Rewrite using `[hsm, hHreal, hr, Complex.ofReal_div, Complex.ofReal_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_principal_dim_one :
  ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ) (L : PeriodPair) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), g = 1 → w ≠ 0 → (∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ) → Hm.IsHermitian → 0 < (hermForm Hm w w).re → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∀ z z' : ℂ, hermForm Hm (z • w) (z' • w) = z * starRingEnd ℂ z' / (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) := by
  intro g Λ w L Hm Ef hg hw hΛ hH hpos hEf hbij z z'
  subst hg
  set H := hermForm Hm w w with hHdef
  have hHim : H.im = 0 := hermForm_self_im hH w
  have hHreal : H = (H.re : ℂ) := Complex.ext (by simp) (by simp [hHim])
  have hsm : ∀ u v : ℂ, hermForm Hm (u • w) (v • w) = u * starRingEnd ℂ v * H :=
    fun u v => hermForm_smul_smul Hm u v w w
  set D := (L.ω₁ * starRingEnd ℂ L.ω₂).im with hD
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext i
    rw [Subsingleton.elim i 0]
    simpa using h
  have hcoord : ∀ x : Λ, ∃ m n : ℤ, (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w := by
    intro x
    have hx : (x : Fin 1 → ℂ) = (x.1 0 / w 0) • w := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [div_mul_cancel₀ _ hw0]
    have hmem : (x.1 0 / w 0) ∈ L.lattice := (hΛ _).2 (by rw [← hx]; exact x.2)
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hmem
    exact ⟨m, n, by rw [hmn]; exact hx⟩
  have him : ∀ m n m' n' : ℤ,
      (((m : ℂ) * L.ω₁ + n * L.ω₂) * starRingEnd ℂ ((m' : ℂ) * L.ω₁ + n' * L.ω₂)).im
        = ((m * n' - n * m' : ℤ) : ℝ) * D := by
    intro m n m' n'
    simp only [hD, map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    push_cast
    ring
  have hEfc : ∀ (x y : Λ) (m n m' n' : ℤ),
      (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w →
      (y : Fin 1 → ℂ) = ((m' : ℂ) * L.ω₁ + n' * L.ω₂) • w →
      (Ef x y : ℝ) = ((m * n' - n * m' : ℤ) : ℝ) * (H.re * D) := by
    intro x y m n m' n' hx hy
    rw [hEf, hx, hy, hsm, Complex.mul_im, hHim, him]
    ring
  have ha : L.ω₁ • w ∈ Λ := (hΛ _).1 L.ω₁_mem_lattice
  have hb : L.ω₂ • w ∈ Λ := (hΛ _).1 L.ω₂_mem_lattice
  let a : Λ := ⟨L.ω₁ • w, ha⟩
  let b : Λ := ⟨L.ω₂ • w, hb⟩
  have ea : (a : Fin 1 → ℂ) = (((1 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₁ • w = _
    simp
  have eb : (b : Fin 1 → ℂ) = (((0 : ℤ) : ℂ) * L.ω₁ + ((1 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₂ • w = _
    simp
  set k := Ef a b with hkdef
  have hk : (k : ℝ) = H.re * D := by
    rw [hEfc a b 1 0 0 1 ea eb]
    norm_num
  have hdvd : ∀ x y : Λ, k ∣ Ef x y := by
    intro x y
    obtain ⟨m, n, hx⟩ := hcoord x
    obtain ⟨m', n', hy⟩ := hcoord y
    refine ⟨m * n' - n * m', ?_⟩
    have h := hEfc x y m n m' n' hx hy
    rw [← hk, mul_comm] at h
    exact_mod_cast h
  have hba : Ef b a = -k := by
    have h := hEfc b a 0 1 1 0 eb ea
    rw [← hk] at h
    have h' : ((Ef b a : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast h'
  have hk0 : k ≠ 0 := by
    intro hk0
    have hEa : Ef a = Ef 0 := by
      apply LinearMap.ext
      intro y
      rw [map_zero, LinearMap.zero_apply]
      obtain ⟨c, hc⟩ := hdvd a y
      rw [hc, hk0, zero_mul]
    have ha0 : a = 0 := hbij.1 hEa
    have h0 : L.ω₁ • w = 0 := congrArg Subtype.val ha0
    rcases smul_eq_zero.1 h0 with h | h
    · exact L.indep.ne_zero 0 (by simpa using h)
    · exact hw h
  let f : Λ →ₗ[ℤ] ℤ :=
    { toFun := fun y => Ef y a / k
      map_add' := fun y y' => by
        simp only [map_add, LinearMap.add_apply]
        exact Int.add_ediv_of_dvd_left (hdvd y a)
      map_smul' := fun c y => by
        simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdvd y a) }
  obtain ⟨x, hx⟩ := hbij.2 f
  have hxb : Ef x b = -1 := by
    rw [hx]
    show Ef b a / k = -1
    rw [hba, Int.neg_ediv_of_dvd (dvd_refl k), Int.ediv_self hk0]
  have hunit : k = 1 ∨ k = -1 := by
    have h := hdvd x b
    rw [hxb] at h
    exact Int.isUnit_iff.1 (isUnit_of_dvd_one (dvd_neg.1 h))
  have hHre : H.re * |D| = 1 := by
    have hpos' : 0 < H.re := hpos
    rcases hunit with h | h
    · have h1 : H.re * D = 1 := by rw [← hk, h]; norm_num
      have hD0 : 0 < D := by nlinarith
      rw [abs_of_pos hD0]
      exact h1
    · have h1 : H.re * D = -1 := by rw [← hk, h]; norm_num
      have hD0 : D < 0 := by nlinarith
      rw [abs_of_neg hD0]
      linarith
  have hDabs : |D| ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hHre
    exact zero_ne_one hHre
  have hr : H.re = 1 / |D| := by
    rw [eq_div_iff hDabs]
    exact hHre
  rw [hsm, hHreal, hr, Complex.ofReal_div, Complex.ofReal_one]
  ring

end GlobalTheory
