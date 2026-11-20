import Mathlib
import GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfDiscr
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.EqOneOrNegOneOfMemTorsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Rows

namespace SqfDiscr

open NumberField Module Polynomial GroundTheory.Heights₂.Theta.QuadraticFieldArithmetic

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] {d : ℕ} {x : K}

/- English proof (translation)
Establish `hd : 0 < d` using `Nat.pos_of_ne_zero hsq.ne_zero`. Use `set y := algebraMap ℚ K a + algebraMap ℚ K b * x with hy_def`. Establish `hc` using `isIntegral_conj hy`. Rewrite `hc` using `[conj_apply hd hx]`. Establish `h2 : (2 : K) = algebraMap ℚ K 2` using `(map_ofNat _ 2).symm`.

Establish `hdK : (d : K) = algebraMap ℚ K d` using `(map_natCast _ d).symm`. Establish `htr : IsIntegral ℤ (algebraMap ℚ K (2 * a))`. Establish `e : algebraMap ℚ K (2 * a) = y + (algebraMap ℚ K a - algebraMap ℚ K b * x)`. Rewrite using `[map_mul, ← h2, hy_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `hy.add hc`. Take `⟨A, hA⟩` from `exists_int_of_isIntegral _ htr`. Establish `hnm : IsIntegral ℤ (algebraMap ℚ K (a ^ 2 + d * b ^ 2))`. Establish `e : algebraMap ℚ K (a ^ 2 + d * b ^ 2) = y * (algebraMap ℚ K a - algebraMap ℚ K b * x)`.

Rewrite using `[map_add, map_mul, map_pow, map_pow, ← hdK, hy_def]`. Take the linear combination `(algebraMap ℚ K b) ^ 2 * hx`. Rewrite using `[e]`. Conclude with `hy.mul hc`. Take `⟨N, hN⟩` from `exists_int_of_isIntegral _ hnm`.

Establish `hAK : algebraMap ℤ K A = algebraMap ℚ K (2 * a)`. Rewrite using `[hA, eq_intCast, map_intCast]`. Establish `h2y : IsIntegral ℤ (y + y - algebraMap ℤ K A)` using `(hy.add hy).sub isIntegral_algebraMap`. Establish `hk : IsIntegral ℤ (algebraMap ℚ K (-(d * (2 * b))))`. Establish `e : algebraMap ℚ K (-(d * (2 * b))) = (y + y - algebraMap ℤ K A) * x`.

Rewrite using `[hAK, hy_def, map_neg, map_mul, map_mul, map_mul, ← hdK, ← h2]`. Take the linear combination `(-(2 : K) * algebraMap ℚ K b) * hx`. Rewrite using `[e]`. Conclude with `h2y.mul (isIntegral_alt hx)`. Take `⟨k, hk'⟩` from `exists_int_of_isIntegral _ hk`.

Establish `he : IsIntegral ℤ (algebraMap ℚ K (-(d * (2 * b) ^ 2)))`. Establish `e : algebraMap ℚ K (-(d * (2 * b) ^ 2)) = (y + y - algebraMap ℤ K A) ^ 2`. Rewrite using `[hAK, hy_def, map_neg, map_mul, map_pow, map_mul, map_mul, ← hdK, ← h2]`. Take the linear combination `(-(2 : K) ^ 2 * algebraMap ℚ K b ^ 2) * hx`. Rewrite using `[e]`.

Conclude with `h2y.pow 2`. Take `⟨e, he'⟩` from `exists_int_of_isIntegral _ he`. Establish `hke : (k : ℚ) ^ 2 = d * (-e)`. Establish `h1 : (k : ℚ) = -(d * (2 * b))` using `hk'.symm`. Establish `h2 : (e : ℚ) = -(d * (2 * b) ^ 2)` using `he'.symm`.

Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hke' : k ^ 2 = d * (-e)` using `by exact_mod_cast hke`. Establish `hdk : (d : ℤ) ∣ k` using `((Int.squarefree_natCast.mpr hsq).dvd_pow_iff_dvd two_ne_zero).mp ⟨-e, hke'⟩`. Take `⟨B, hB⟩` from `hdk`.

Establish `hd0 : (d : ℚ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `h1 : (k : ℚ) = -(d * (2 * b))` using `hk'.symm`. Rewrite `h1` using `[hB]`. Move the coercions through the operations in `at h1`. Establish `hb : 2 * b = -(B : ℚ)`.

Establish `: (d : ℚ) * (2 * b) = d * (-B)` using `by linarith`. Conclude with `mul_left_cancel₀ hd0 this`. Use `⟨A, -B, N, hA, by push_cast; exact hb, ?_⟩` and prove the remaining obligations. Establish `: ((A ^ 2 + d * (-B) ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ)`. Use `push_cast`.

Rewrite using `[← hA, ← hN]`. Establish `: (B : ℚ) = -(2 * b)` using `by linarith`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.
-/
theorem coords_of_isIntegral (hsq : Squarefree d) (hx : x ^ 2 = -(d : K)) {a b : ℚ}
    (hy : IsIntegral ℤ (algebraMap ℚ K a + algebraMap ℚ K b * x)) :
    ∃ A B N : ℤ, 2 * a = A ∧ 2 * b = B ∧ A ^ 2 + d * B ^ 2 = 4 * N := by
  have hd : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  set y := algebraMap ℚ K a + algebraMap ℚ K b * x with hy_def
  have hc := isIntegral_conj hy
  rw [conj_apply hd hx] at hc
  have h2 : (2 : K) = algebraMap ℚ K 2 := (map_ofNat _ 2).symm
  have hdK : (d : K) = algebraMap ℚ K d := (map_natCast _ d).symm

  have htr : IsIntegral ℤ (algebraMap ℚ K (2 * a)) := by
    have e : algebraMap ℚ K (2 * a) =
        y + (algebraMap ℚ K a - algebraMap ℚ K b * x) := by
      rw [map_mul, ← h2, hy_def]; ring
    rw [e]; exact hy.add hc
  obtain ⟨A, hA⟩ := exists_int_of_isIntegral _ htr

  have hnm : IsIntegral ℤ (algebraMap ℚ K (a ^ 2 + d * b ^ 2)) := by
    have e : algebraMap ℚ K (a ^ 2 + d * b ^ 2) =
        y * (algebraMap ℚ K a - algebraMap ℚ K b * x) := by
      rw [map_add, map_mul, map_pow, map_pow, ← hdK, hy_def]
      linear_combination (algebraMap ℚ K b) ^ 2 * hx
    rw [e]; exact hy.mul hc
  obtain ⟨N, hN⟩ := exists_int_of_isIntegral _ hnm
  have hAK : algebraMap ℤ K A = algebraMap ℚ K (2 * a) := by
    rw [hA, eq_intCast, map_intCast]
  have h2y : IsIntegral ℤ (y + y - algebraMap ℤ K A) :=
    (hy.add hy).sub isIntegral_algebraMap

  have hk : IsIntegral ℤ (algebraMap ℚ K (-(d * (2 * b)))) := by
    have e : algebraMap ℚ K (-(d * (2 * b))) = (y + y - algebraMap ℤ K A) * x := by
      rw [hAK, hy_def, map_neg, map_mul, map_mul, map_mul, ← hdK, ← h2]
      linear_combination (-(2 : K) * algebraMap ℚ K b) * hx
    rw [e]; exact h2y.mul (isIntegral_alt hx)
  obtain ⟨k, hk'⟩ := exists_int_of_isIntegral _ hk

  have he : IsIntegral ℤ (algebraMap ℚ K (-(d * (2 * b) ^ 2))) := by
    have e : algebraMap ℚ K (-(d * (2 * b) ^ 2)) = (y + y - algebraMap ℤ K A) ^ 2 := by
      rw [hAK, hy_def, map_neg, map_mul, map_pow, map_mul, map_mul, ← hdK, ← h2]
      linear_combination (-(2 : K) ^ 2 * algebraMap ℚ K b ^ 2) * hx
    rw [e]; exact h2y.pow 2
  obtain ⟨e, he'⟩ := exists_int_of_isIntegral _ he

  have hke : (k : ℚ) ^ 2 = d * (-e) := by
    have h1 : (k : ℚ) = -(d * (2 * b)) := hk'.symm
    have h2 : (e : ℚ) = -(d * (2 * b) ^ 2) := he'.symm
    rw [h1, h2]; ring
  have hke' : k ^ 2 = d * (-e) := by exact_mod_cast hke
  have hdk : (d : ℤ) ∣ k :=
    ((Int.squarefree_natCast.mpr hsq).dvd_pow_iff_dvd two_ne_zero).mp ⟨-e, hke'⟩
  obtain ⟨B, hB⟩ := hdk
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : (k : ℚ) = -(d * (2 * b)) := hk'.symm
  rw [hB] at h1
  push_cast at h1
  have hb : 2 * b = -(B : ℚ) := by
    have : (d : ℚ) * (2 * b) = d * (-B) := by linarith
    exact mul_left_cancel₀ hd0 this
  refine ⟨A, -B, N, hA, by push_cast; exact hb, ?_⟩
  have : ((A ^ 2 + d * (-B) ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
    push_cast
    rw [← hA, ← hN]
    have : (B : ℚ) = -(2 * b) := by linarith
    rw [this]; ring
  exact_mod_cast this

/- English proof (translation)
Take `⟨a, b, hab⟩` from `exists_rat (Nat.pos_of_ne_zero hsq.ne_zero) hx (y : K)`. Establish `hy : IsIntegral ℤ (algebraMap ℚ K a + algebraMap ℚ K b * x)` using `hab ▸ y.2`. Take `⟨A, B, N, hA, hB, hN⟩` from `coords_of_isIntegral hsq hx hy`. Take `⟨m, hm⟩` from `parity_of_norm hd4 hN`. Use `⟨m, B, ?_⟩` and prove the remaining obligations.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hab]`. Express the relevant statement in the definitionally equal form `_ = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + B • omega hd4 hx)`. Rewrite using `[map_add, map_zsmul, map_zsmul, map_one, ← RingOfIntegers.coe_eq_algebraMap, coe_omega, zsmul_eq_mul, zsmul_eq_mul]`. Establish `ha : algebraMap ℚ K a = (A : K) / 2`.

Rewrite using `[eq_div_iff two_ne_zero, ← map_intCast (algebraMap ℚ K), ← hA]`. Simplify using `[mul_comm]`. Establish `hb : algebraMap ℚ K b = (B : K) / 2`. Rewrite using `[eq_div_iff two_ne_zero, ← map_intCast (algebraMap ℚ K), ← hB]`. Simplify using `[mul_comm]`.

Rewrite using `[ha, hb, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_coords (hsq : Squarefree d) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K))
    (y : 𝓞 K) : ∃ m n : ℤ, y = m • (1 : 𝓞 K) + n • omega hd4 hx := by
  obtain ⟨a, b, hab⟩ := exists_rat (Nat.pos_of_ne_zero hsq.ne_zero) hx (y : K)
  have hy : IsIntegral ℤ (algebraMap ℚ K a + algebraMap ℚ K b * x) := hab ▸ y.2
  obtain ⟨A, B, N, hA, hB, hN⟩ := coords_of_isIntegral hsq hx hy
  obtain ⟨m, hm⟩ := parity_of_norm hd4 hN
  refine ⟨m, B, ?_⟩
  apply RingOfIntegers.ext
  rw [hab]
  change _ = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + B • omega hd4 hx)
  rw [map_add, map_zsmul, map_zsmul, map_one, ← RingOfIntegers.coe_eq_algebraMap, coe_omega,
    zsmul_eq_mul, zsmul_eq_mul]
  have ha : algebraMap ℚ K a = (A : K) / 2 := by
    rw [eq_div_iff two_ne_zero, ← map_intCast (algebraMap ℚ K), ← hA]; simp [mul_comm]
  have hb : algebraMap ℚ K b = (B : K) / 2 := by
    rw [eq_div_iff two_ne_zero, ← map_intCast (algebraMap ℚ K), ← hB]; simp [mul_comm]
  rw [ha, hb, hm]
  push_cast
  ring

def basisInt (hsq : Squarefree d) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk (linearIndependent_one_omega (Nat.pos_of_ne_zero hsq.ne_zero) hd4 hx) (by
    rintro y -
    obtain ⟨m, n, rfl⟩ := exists_int_coords hsq hd4 hx y
    exact Submodule.add_mem _ (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩)))

/- English proof (translation)
Simplify using `[basisInt]`.
-/
theorem basisInt_apply (hsq : Squarefree d) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    ⇑(basisInt hsq hd4 hx) = ![1, omega hd4 hx] := by
  simp [basisInt]

/- English proof (translation)
Establish `hd : 0 < d` using `Nat.pos_of_ne_zero hsq.ne_zero`. Use `set b := basisInt hsq hd4 hx`. Establish `h1 : (discr K : ℚ) = Algebra.discr ℚ (b.localizationLocalization ℚ (nonZeroDivisors ℤ) K)`. Rewrite using `[Algebra.discr_localizationLocalization, discr_eq_discr]`. Both sides reduce to the same expression.

Establish `hb : ⇑(b.localizationLocalization ℚ (nonZeroDivisors ℤ) K) = ![(1 : K), (1 + x) / 2]`. Use extensionality with `i`. Rewrite using `[Basis.localizationLocalization_apply, basisInt_apply]`. Apply the tactic sequence `fin_cases i <;> simp [coe_omega]`. Rewrite `h1` using `[hb, Algebra.discr_def, Matrix.det_fin_two]`.

Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one] at h1`. Establish `c` using `conj_alt_bis (K := K) hd hx`. Establish `t1 : Algebra.trace ℚ K 1 = 2` using `trace_eq_of _ _ (by rw [map_one, map_ofNat]; norm_num)`. Establish `tω : Algebra.trace ℚ K ((1 + x) / 2) = 1` using `trace_eq_of _ _ (by rw [map_div₀, map_add, map_one, c, map_one, map_ofNat]; ring)`. Establish `tω2 : Algebra.trace ℚ K ((1 + x) / 2 * ((1 + x) / 2)) = (1 - d) / 2` using `trace_eq_of _ _ (by`.

Rewrite using `[map_mul, map_div₀, map_add, map_one, c, map_ofNat, map_div₀, map_sub, map_one, map_natCast, map_ofNat]`. Take the linear combination `(1 / 2 : K) * hx)`. Rewrite `h1` using `[t1, tω, tω2]`. Establish `: (discr K : ℚ) = ((-(d : ℤ) : ℤ) : ℚ)` using `by rw [h1]; push_cast; ring`. Conclude with `this` after adjusting the coercions.
-/
theorem discr_eq (hsq : Squarefree d) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    discr K = -(d : ℤ) := by
  have hd : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  set b := basisInt hsq hd4 hx
  have h1 : (discr K : ℚ) = Algebra.discr ℚ (b.localizationLocalization ℚ (nonZeroDivisors ℤ) K) := by
    rw [Algebra.discr_localizationLocalization, discr_eq_discr]; rfl
  have hb : ⇑(b.localizationLocalization ℚ (nonZeroDivisors ℤ) K) = ![(1 : K), (1 + x) / 2] := by
    ext i
    rw [Basis.localizationLocalization_apply, basisInt_apply]
    fin_cases i <;> simp [coe_omega]
  rw [hb, Algebra.discr_def, Matrix.det_fin_two] at h1
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, mul_one] at h1
  have c := conj_alt_bis (K := K) hd hx
  have t1 : Algebra.trace ℚ K 1 = 2 := trace_eq_of _ _ (by rw [map_one, map_ofNat]; norm_num)
  have tω : Algebra.trace ℚ K ((1 + x) / 2) = 1 :=
    trace_eq_of _ _ (by rw [map_div₀, map_add, map_one, c, map_one, map_ofNat]; ring)
  have tω2 : Algebra.trace ℚ K ((1 + x) / 2 * ((1 + x) / 2)) = (1 - d) / 2 :=
    trace_eq_of _ _ (by
      rw [map_mul, map_div₀, map_add, map_one, c, map_ofNat, map_div₀, map_sub, map_one,
        map_natCast, map_ofNat]
      linear_combination (1 / 2 : K) * hx)
  rw [t1, tω, tω2] at h1
  have : (discr K : ℚ) = ((-(d : ℤ) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
  exact_mod_cast this

end SqfDiscr

/- English proof (translation)
Introduce `d hsq hd4 K _ _ hK x hx`. Establish `: Algebra.IsQuadraticExtension ℚ K` using `⟨hK⟩`. Conclude with `SqfDiscr.discr_eq hsq hd4 hx`.
-/
theorem SqfDiscr.proof : SqfDiscr.Statement := by
  intro d hsq hd4 K _ _ hK x hx
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  exact SqfDiscr.discr_eq hsq hd4 hx

end GroundTheory.Heights₂.Heights.Rows
