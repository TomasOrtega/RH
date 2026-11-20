import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hm' : (0 : ℤ) < m` using `by exact_mod_cast hm`. Use `set g : ℕ := Int.gcd p r with hg`. Establish `hg0 : 0 < g`. Break down `Nat.eq_zero_or_pos g with h0 | h0` into its components or cases. Rewrite `h0` using `[hg, Int.gcd_eq_zero_iff]`.

Rewrite `h` using `[h0.1, h0.2]`. Simplify using `at h`. Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `hgZ : (0 : ℤ) < g` using `by exact_mod_cast hg0`.

Take `⟨x, hx⟩ : (g : ℤ) ∣ p` from `Int.gcd_dvd_left p r`. Take `⟨z, hz⟩ : (g : ℤ) ∣ r` from `Int.gcd_dvd_right p r`. Use `set u := Int.gcdA p r`. Use `set v := Int.gcdB p r`. Establish `hbez : (g : ℤ) = p * u + r * v` using `Int.gcd_eq_gcd_ab p r`.

Establish `h1 : x * u + z * v = 1`. Establish `: (g : ℤ) * (x * u + z * v) = g * 1`. Rewrite using `[mul_one]`. Use `conv_rhs => rw [hbez, hx, hz]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `mul_left_cancel₀ hgZ.ne' this`. Use `set E : ℤ := x * s - z * q with hE`. Establish `hgE : (g : ℤ) * E = m` using `by rw [← h, hx, hz, hE]; ring`. Establish `hE0 : 0 < E`. Assume the negation of the conclusion as `hc`.

Establish `: (g : ℤ) * E ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hgZ.le (not_lt.mp hc)`. Use linear arithmetic over natural numbers and integers. Use `set b0 : ℤ := u * q + v * s with hb0`. Establish `hmod0 : 0 ≤ b0 % E` using `Int.emod_nonneg _ hE0.ne'`. Establish `hmod1 : b0 % E < E` using `Int.emod_lt_of_pos _ hE0`.

Establish `hdiv : b0 % E + E * (b0 / E) = b0` using `Int.emod_add_mul_ediv b0 E`. Use `set k := b0 / E`. Use `set B := b0 % E`. Establish `hEn : ((E.toNat : ℕ) : ℤ) = E` using `Int.toNat_of_nonneg hE0.le`. Establish `hBn : ((B.toNat : ℕ) : ℤ) = B` using `Int.toNat_of_nonneg hmod0`.

Use `⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `h1`. Establish `: ((g * E.toNat : ℕ) : ℤ) = m` using `by push_cast; rw [hEn]; exact hgE`. Conclude with `this` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEn, hBn]`. Establish `: x * B + (x * k - v) * E = x * b0 - v * E` using `by rw [← hdiv]; ring`. Rewrite using `[this, hb0, hE]`.

Take the linear combination `(-q) * h1`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEn, hBn]`. Establish `: z * B + (z * k + u) * E = z * b0 + u * E` using `by rw [← hdiv]; ring`.

Rewrite using `[this, hb0, hE]`. Take the linear combination `(-s) * h1`.
-/
theorem exists_hermite_normal_form_coords {m : ℕ} (hm : 0 < m) (p q r s : ℤ) (h : p * s - q * r = m) :
    ∃ (x y z w : ℤ) (a b e : ℕ), x * w - y * z = 1 ∧ a * e = m ∧ b < e ∧
      p = x * a ∧ q = x * b + y * e ∧ r = z * a ∧ s = z * b + w * e := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set g : ℕ := Int.gcd p r with hg
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [hg, Int.gcd_eq_zero_iff] at h0
      rw [h0.1, h0.2] at h
      simp at h
      omega
    · exact h0
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  obtain ⟨x, hx⟩ : (g : ℤ) ∣ p := Int.gcd_dvd_left p r
  obtain ⟨z, hz⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right p r
  set u := Int.gcdA p r
  set v := Int.gcdB p r
  have hbez : (g : ℤ) = p * u + r * v := Int.gcd_eq_gcd_ab p r
  have h1 : x * u + z * v = 1 := by
    have : (g : ℤ) * (x * u + z * v) = g * 1 := by
      rw [mul_one]; conv_rhs => rw [hbez, hx, hz]
      ring
    exact mul_left_cancel₀ hgZ.ne' this
  set E : ℤ := x * s - z * q with hE
  have hgE : (g : ℤ) * E = m := by rw [← h, hx, hz, hE]; ring
  have hE0 : 0 < E := by
    by_contra hc
    have : (g : ℤ) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgZ.le (not_lt.mp hc)
    omega
  set b0 : ℤ := u * q + v * s with hb0
  have hmod0 : 0 ≤ b0 % E := Int.emod_nonneg _ hE0.ne'
  have hmod1 : b0 % E < E := Int.emod_lt_of_pos _ hE0
  have hdiv : b0 % E + E * (b0 / E) = b0 := Int.emod_add_mul_ediv b0 E
  set k := b0 / E
  set B := b0 % E
  have hEn : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg hE0.le
  have hBn : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hmod0
  refine ⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · have : ((g * E.toNat : ℕ) : ℤ) = m := by push_cast; rw [hEn]; exact hgE
    exact_mod_cast this
  · omega
  · rw [hx]; ring
  · rw [hEn, hBn]
    have : x * B + (x * k - v) * E = x * b0 - v * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-q) * h1
  · rw [hz]; ring
  · rw [hEn, hBn]
    have : z * B + (z * k + u) * E = z * b0 + u * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-s) * h1

/- English proof (translation)
Rewrite `hM` using `[Matrix.det_fin_two]`. Take `⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩` from `exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM`. Use `⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e), (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`.

Simplify using `[Tmat, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]`.
-/
theorem hnf_exists {m : ℕ} (hm : 0 < m) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = m) :
    ∃ (γ : SL(2, ℤ)) (t : ℕ × ℕ × ℕ), t ∈ Tm m ∧ M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t := by
  rw [Matrix.det_fin_two] at hM
  obtain ⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩ :=
    exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM
  refine ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e),
    (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]

/- English proof (translation)
Take `⟨a, b, e⟩` from `t`. Take `⟨a', b', e'⟩` from `t'`. Take `⟨hae, hbe⟩` from `(mem_Tm hm _).1 ht`. Take `⟨hae', hbe'⟩` from `(mem_Tm hm _).1 ht'`. Take `⟨ha, he⟩` from `Tm_pos hm ht`.

Take `⟨ha', he'⟩` from `Tm_pos hm ht'`. Simplify using `only at hae hbe hae' hbe' ha he ha' he'`. Establish `hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1`. Rewrite using `[← Matrix.det_fin_two]`. Conclude with `γ.2`.

Establish `h00 : (a : ℤ) = γ.1 0 0 * a'`. Use `congrFun (congrFun h 0) 0` as an intermediate fact. Simplify `this` using `[Tmat, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e'`. Use `congrFun (congrFun h 0) 1` as an intermediate fact.

Simplify `this` using `[Tmat, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `h10 : (0 : ℤ) = γ.1 1 0 * a'`. Use `congrFun (congrFun h 1) 0` as an intermediate fact. Simplify `this` using `[Tmat, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e'`.

Use `congrFun (congrFun h 1) 1` as an intermediate fact. Simplify `this` using `[Tmat, Matrix.mul_apply, Fin.sum_univ_two]`. Generalize the expression as in `γ.1 0 0 = x at *`. Generalize the expression as in `γ.1 0 1 = y at *`. Generalize the expression as in `γ.1 1 0 = z at *`.

Generalize the expression as in `γ.1 1 1 = w at *`. Establish `haZ : (0 : ℤ) < a` using `by exact_mod_cast ha`. Establish `haZ' : (0 : ℤ) < a'` using `by exact_mod_cast ha'`. Establish `heZ' : (0 : ℤ) < e'` using `by exact_mod_cast he'`. Establish `hz : z = 0`.

Break down `mul_eq_zero.1 h10.symm with h0 | h0` into its components or cases. Conclude with `h0`. Use linear arithmetic over natural numbers and integers. Substitute `hz` using the available equality. Establish `hxw : x * w = 1` using `by linear_combination hdet`.

Establish `hx0 : 0 < x`. Assume the negation of the conclusion as `hc`. Establish `: x * a' ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le`. Use linear arithmetic over natural numbers and integers. Establish `hx : x = 1`.

Break down `Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0` into its components or cases. Conclude with `h0`. Use linear arithmetic over natural numbers and integers. Substitute `hx` using the available equality. Establish `hw : w = 1` using `by linear_combination hxw`.

Substitute `hw` using the available equality. Establish `e1 : a = a'` using `by omega`. Establish `e2 : e = e'` using `by omega`. Substitute `e1 e2` using the available equality. Establish `hy : y = 0`.

Establish `hbZ : (b : ℤ) < e` using `by exact_mod_cast hbe`. Establish `hbZ' : (b' : ℤ) < e` using `by exact_mod_cast hbe'`. Assume the negation of the conclusion as `hc`. Break down `lt_or_gt_of_ne hc with h0 | h0` into its components or cases. Establish `: y * e ≤ -1 * e` using `mul_le_mul_of_nonneg_right (by omega) heZ'.le`.

Use linear arithmetic over natural numbers and integers. Establish `: 1 * (e : ℤ) ≤ y * e` using `mul_le_mul_of_nonneg_right (by omega) heZ'.le`. Use linear arithmetic over natural numbers and integers. Substitute `hy` using the available equality. Establish `e3 : b = b'` using `by omega`.

Substitute `e3` using the available equality. Both sides reduce to the same expression.
-/
theorem hnf_unique {m : ℕ} (hm : 0 < m) {t t' : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (ht' : t' ∈ Tm m)
    (γ : SL(2, ℤ)) (h : Tmat t = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') : t = t' := by
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', e'⟩ := t'
  obtain ⟨hae, hbe⟩ := (mem_Tm hm _).1 ht
  obtain ⟨hae', hbe'⟩ := (mem_Tm hm _).1 ht'
  obtain ⟨ha, he⟩ := Tm_pos hm ht
  obtain ⟨ha', he'⟩ := Tm_pos hm ht'
  simp only at hae hbe hae' hbe' ha he ha' he'
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h00 : (a : ℤ) = γ.1 0 0 * a' := by
    have := congrFun (congrFun h 0) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e' := by
    have := congrFun (congrFun h 0) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : (0 : ℤ) = γ.1 1 0 * a' := by
    have := congrFun (congrFun h 1) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e' := by
    have := congrFun (congrFun h 1) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  generalize γ.1 0 0 = x at *
  generalize γ.1 0 1 = y at *
  generalize γ.1 1 0 = z at *
  generalize γ.1 1 1 = w at *
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have haZ' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have heZ' : (0 : ℤ) < e' := by exact_mod_cast he'
  have hz : z = 0 := by
    rcases mul_eq_zero.1 h10.symm with h0 | h0
    · exact h0
    · omega
  subst hz
  have hxw : x * w = 1 := by linear_combination hdet
  have hx0 : 0 < x := by
    by_contra hc
    have : x * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le
    omega
  have hx : x = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0
    · exact h0
    · omega
  subst hx
  have hw : w = 1 := by linear_combination hxw
  subst hw
  have e1 : a = a' := by omega
  have e2 : e = e' := by omega
  subst e1 e2
  have hy : y = 0 := by
    have hbZ : (b : ℤ) < e := by exact_mod_cast hbe
    have hbZ' : (b' : ℤ) < e := by exact_mod_cast hbe'
    by_contra hc
    rcases lt_or_gt_of_ne hc with h0 | h0
    · have : y * e ≤ -1 * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
    · have : 1 * (e : ℤ) ≤ y * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
  subst hy
  have e3 : b = b' := by omega
  subst e3
  rfl

end ReciprocityTheory.ChartRestriction.L1
