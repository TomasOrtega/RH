import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum]`. Use `conv_rhs => rw [p.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial]`.

Establish `hdeg : ∑ i ∈ m.support, m i = d`. Use `hp (mem_support_iff.mp hm)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum]`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/- English proof (translation)
Take `⟨hfd, hc0, hhom, hcp⟩` from `h`. Use `set P := pullField y L with hP`. Use `set n := Module.finrank P Ω with hn`. Establish `hfix : ∀ x ∈ P, σ x = x`. Introduce `x hx`.

Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, j, hj, rfl⟩` from `hx`. Rewrite using `[map_div₀, hL, hL, mul_div_mul_left _ _ hμ0]`. Consider the case `algebraMap r => exact σ.toRatAlgHom.commutes r`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `inv x _ hx => rw [map_inv₀, hx]`. Consider the case `mul x y _ _ hx hy => rw [map_mul, hx, hy]`. Use `set v : ℕ → Ω := fun i => aeval (fun j => aeval y (L j)) (c i) with hv`. Establish `hσv : ∀ i ≤ n, σ (v i) = μ ^ (i * m) * v i`.

Introduce `i hi`. Establish `h1` using `DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℚ) (fun j => aeval y (L j)) σ.toRatAlgHom) (c i)`. Simplify using `only [AlgHom.comp_apply] at h1`. Express the relevant statement in the definitionally equal form `σ (v i) = _ at h1`. Rewrite using `[h1]`.

Express the relevant statement in the definitionally equal form `aeval (fun j => σ (aeval y (L j))) (c i) = _`. Simplify using `only [hL]`. Conclude with `aeval_mul_of_isHomogeneous (hhom i hi) μ _`. Establish `hcoeff : ∀ i ≤ n, ((LinearMap.charpoly (Algebra.lmul P Ω s)).map (algebraMap P Ω)).coeff (n - i) = v i`. Introduce `i hi`.

Rewrite using `[hcp, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]`. Rewrite using `[Polynomial.coeff_C_mul_X_pow, if_pos rfl]`. Introduce `b hb hbi`. Rewrite using `[Polynomial.coeff_C_mul_X_pow, if_neg]`. Use `Finset.mem_range.mp hb` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `hi'`. Conclude with `absurd (Finset.mem_range.mpr (by omega)) hi'`. Establish `hzero : ∀ i, 1 ≤ i → i ≤ n → v i = 0`. Introduce `i h1 hi`.

Establish `hfixv : σ (v i) = v i`. Rewrite using `[← hcoeff i hi, Polynomial.coeff_map]`. Conclude with `hfix _ (SetLike.coe_mem _)`. Rewrite `hfixv` using `[hσv i hi]`. Establish `hne : μ ^ (i * m) - 1 ≠ 0` using `sub_ne_zero.mpr (hμ _ (Nat.mul_pos (by omega) hm))`.

Establish `: (μ ^ (i * m) - 1) * v i = 0` using `by rw [sub_mul, hfixv, one_mul, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_left hne`. Establish `hX : (LinearMap.charpoly (Algebra.lmul P Ω s)).map (algebraMap P Ω) = (Polynomial.X ^ n : Polynomial P).map (algebraMap P Ω)`. Rewrite using `[hcp, Finset.sum_eq_single 0]`. Establish `: v 0 = 1` using `by simp [hv, hc0]`.

Express the relevant statement in the definitionally equal form `Polynomial.C (v 0) * _ = _`. Rewrite using `[this, Polynomial.map_pow, Polynomial.map_X]`. Simplify using the standard rewrite rules. Introduce `b hb hb0`. Express the relevant statement in the definitionally equal form `Polynomial.C (v b) * _ = 0`.

Rewrite using `[hzero b (by omega) (by have := Finset.mem_range.mp hb; omega), map_zero, zero_mul]`. Introduce `h0`. Conclude with `absurd (Finset.mem_range.mpr (by omega)) h0`. Establish `hchar : LinearMap.charpoly (Algebra.lmul P Ω s) = Polynomial.X ^ n` using `Polynomial.map_injective _ (algebraMap P Ω).injective hX`. Establish `hCH` using `LinearMap.aeval_self_charpoly (Algebra.lmul P Ω s)`.

Rewrite `hCH` using `[hchar, Polynomial.aeval_X_pow, ← map_pow]`. Establish `h1` using `LinearMap.congr_fun hCH 1`. Express the relevant statement in the definitionally equal form `s ^ n * 1 = 0 at h1`. Rewrite `h1` using `[mul_one]`. Conclude with `(pow_eq_zero_iff'.mp h1).1`.
-/
theorem eq_zero_of_isNormForms {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {L : Fin (D + 1) → MRing ι} {m : ℕ} {s : Ω}
    {c : ℕ → MvPolynomial (Fin (D + 1)) ℚ} (σ : Ω →+* Ω) (μ : Ω) (hμ0 : μ ≠ 0)
    (hL : ∀ j, σ (aeval y (L j)) = μ * aeval y (L j)) (hμ : ∀ d, 0 < d → μ ^ d ≠ 1) (hm : 0 < m)
    (h : IsNormForms y L m s c) : s = 0 := by
  classical
  obtain ⟨hfd, hc0, hhom, hcp⟩ := h
  set P := pullField y L with hP
  set n := Module.finrank P Ω with hn

  have hfix : ∀ x ∈ P, σ x = x := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, j, hj, rfl⟩ := hx
      rw [map_div₀, hL, hL, mul_div_mul_left _ _ hμ0]
    | algebraMap r => exact σ.toRatAlgHom.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  set v : ℕ → Ω := fun i => aeval (fun j => aeval y (L j)) (c i) with hv

  have hσv : ∀ i ≤ n, σ (v i) = μ ^ (i * m) * v i := by
    intro i hi
    have h1 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℚ) (fun j => aeval y (L j)) σ.toRatAlgHom) (c i)
    simp only [AlgHom.comp_apply] at h1
    change σ (v i) = _ at h1
    rw [h1]
    change aeval (fun j => σ (aeval y (L j))) (c i) = _
    simp only [hL]
    exact aeval_mul_of_isHomogeneous (hhom i hi) μ _

  have hcoeff : ∀ i ≤ n,
      ((LinearMap.charpoly (Algebra.lmul P Ω s)).map (algebraMap P Ω)).coeff (n - i) = v i := by
    intro i hi
    rw [hcp, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b hb hbi
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      have := Finset.mem_range.mp hb
      omega
    · intro hi'
      exact absurd (Finset.mem_range.mpr (by omega)) hi'
  have hzero : ∀ i, 1 ≤ i → i ≤ n → v i = 0 := by
    intro i h1 hi
    have hfixv : σ (v i) = v i := by
      rw [← hcoeff i hi, Polynomial.coeff_map]
      exact hfix _ (SetLike.coe_mem _)
    rw [hσv i hi] at hfixv
    have hne : μ ^ (i * m) - 1 ≠ 0 := sub_ne_zero.mpr (hμ _ (Nat.mul_pos (by omega) hm))
    have : (μ ^ (i * m) - 1) * v i = 0 := by rw [sub_mul, hfixv, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne

  have hX : (LinearMap.charpoly (Algebra.lmul P Ω s)).map (algebraMap P Ω) =
      (Polynomial.X ^ n : Polynomial P).map (algebraMap P Ω) := by
    rw [hcp, Finset.sum_eq_single 0]
    · have : v 0 = 1 := by simp [hv, hc0]
      change Polynomial.C (v 0) * _ = _
      rw [this, Polynomial.map_pow, Polynomial.map_X]
      simp
    · intro b hb hb0
      change Polynomial.C (v b) * _ = 0
      rw [hzero b (by omega) (by have := Finset.mem_range.mp hb; omega), map_zero, zero_mul]
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0
  have hchar : LinearMap.charpoly (Algebra.lmul P Ω s) = Polynomial.X ^ n :=
    Polynomial.map_injective _ (algebraMap P Ω).injective hX

  have hCH := LinearMap.aeval_self_charpoly (Algebra.lmul P Ω s)
  rw [hchar, Polynomial.aeval_X_pow, ← map_pow] at hCH
  have h1 := LinearMap.congr_fun hCH 1
  change s ^ n * 1 = 0 at h1
  rw [mul_one] at h1
  exact (pow_eq_zero_iff'.mp h1).1

end FibreNormCharpoly

namespace ProjLine

open ProjLine

def swapIx : (Σ k, GlobalTheory (Fin 2) k) → (Σ k, GlobalTheory (Fin 2) k) := fun p => ⟨(), Fin.rev p.2⟩

/- English proof (translation)
Introduce and unpack `⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h`. Establish `: Fin.rev i = Fin.rev j` using `by simpa [swapIx] using h`. Rewrite `this` using `[Fin.rev_inj]`. Rewrite using `[this]`.
-/
theorem swapIx_injective : Function.Injective swapIx := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  have : Fin.rev i = Fin.rev j := by simpa [swapIx] using h
  rw [Fin.rev_inj] at this
  rw [this]

/- English proof (translation)
The claim follows from `(IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename_injective _ swapIx_injective)`.
-/
theorem swap_injective :
    Function.Injective ((algebraMap (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename swapIx).toRingHom) :=
  (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename_injective _ swapIx_injective)

def swapK : Kfr →+* Kfr := IsFractionRing.lift swap_injective

/- English proof (translation)
Simplify using `[swapK, Xk, IsFractionRing.lift_algebraMap, swapIx]`.
-/
theorem swapK_Xk (i : Fin 2) : swapK (Xk i) = Xk (Fin.rev i) := by
  simp [swapK, Xk, IsFractionRing.lift_algebraMap, swapIx]

/- English proof (translation)
Rewrite using `[u, map_div₀, swapK_Xk, swapK_Xk, inv_div]`. Both sides reduce to the same expression.
-/
theorem swapK_u : swapK u = u⁻¹ := by
  rw [u, map_div₀, swapK_Xk, swapK_Xk, inv_div]
  rfl

/- English proof (translation)
Rewrite using `[Subfield.closure_le]`. Introduce and unpack `_ rfl`. Use `show swapK u ∈ Subfield.closure ({u} : Set Kfr)`. Rewrite using `[swapK_u]`. Conclude with `inv_mem (Subfield.subset_closure rfl)`.
-/
theorem closure_le_comap_swapK :
    Subfield.closure ({u} : Set Kfr) ≤ (Subfield.closure ({u} : Set Kfr)).comap swapK := by
  rw [Subfield.closure_le]
  rintro _ rfl
  show swapK u ∈ Subfield.closure ({u} : Set Kfr)
  rw [swapK_u]
  exact inv_mem (Subfield.subset_closure rfl)

def swapF : FnField →+* FnField :=
  (swapK.comp incl).codRestrict (Subfield.closure ({u} : Set Kfr)) fun x => closure_le_comap_swapK x.2

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg incl h`. Rewrite `h'` using `[map_zero]`. Conclude with `div_ne_zero (Xk_ne_zero 1) (Xk_ne_zero 0) h'`.
-/
theorem uF_ne_zero : uF ≠ 0 := by
  intro h
  have h' := congrArg incl h
  rw [map_zero] at h'
  exact div_ne_zero (Xk_ne_zero 1) (Xk_ne_zero 0) h'

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `swapK u = incl uF⁻¹`. Rewrite using `[swapK_u, map_inv₀]`. Both sides reduce to the same expression.
-/
theorem swapF_uF : swapF uF = uF⁻¹ := by
  apply Subtype.ext
  change swapK u = incl uF⁻¹
  rw [swapK_u, map_inv₀]
  rfl

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg incl h`. Rewrite `h'` using `[map_pow, map_one]`. Express the relevant statement in the definitionally equal form `(Xk 1 / Xk 0) ^ k = 1 at h'`. Rewrite `h'` using `[div_pow, div_eq_one_iff_eq (pow_ne_zero _ (Xk_ne_zero 0)), ← map_pow, ← map_pow]`.

Establish `h2` using `IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr h'`. Establish `h3` using `congrArg (eval (fun p : (Σ k, GlobalTheory (Fin 2) k) => if p.2 = 1 then (1 : ℤ) else 0)) h2`. Simplify using `[zero_pow hk.ne'] at h3`.
-/
theorem uF_pow_ne_one {k : ℕ} (hk : 0 < k) : uF ^ k ≠ 1 := by
  intro h
  have h' := congrArg incl h
  rw [map_pow, map_one] at h'
  change (Xk 1 / Xk 0) ^ k = 1 at h'
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ (Xk_ne_zero 0)), ← map_pow, ← map_pow] at h'
  have h2 := IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr h'
  have h3 := congrArg (eval (fun p : (Σ k, GlobalTheory (Fin 2) k) => if p.2 = 1 then (1 : ℤ) else 0)) h2
  simp [zero_pow hk.ne'] at h3

def Lc : Fin 2 → MRing (GlobalTheory (Fin 2)) :=
  ![X ⟨(), 0⟩ * X ⟨(), 1⟩, X ⟨(), 0⟩ ^ 2 + X ⟨(), 1⟩ ^ 2]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Lc_zero : Lc 0 = X ⟨(), 0⟩ * X ⟨(), 1⟩ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Lc_one : Lc 1 = X ⟨(), 0⟩ ^ 2 + X ⟨(), 1⟩ ^ 2 := rfl

/- English proof (translation)
Simplify using `[Lc]`.
-/
theorem aeval_Lc_zero : aeval y (Lc 0) = uF := by simp [Lc]

/- English proof (translation)
Simplify using `[Lc]`.
-/
theorem aeval_Lc_one : aeval y (Lc 1) = 1 + uF ^ 2 := by simp [Lc]

/- English proof (translation)
Establish `hu` using `uF_ne_zero`. Use `fin_cases j`. Use `show swapF (aeval y (Lc 0)) = _ * aeval y (Lc 0)`. Rewrite using `[aeval_Lc_zero, swapF_uF]`. Clear the denominators using the available nonvanishing facts.

Use `show swapF (aeval y (Lc 1)) = _ * aeval y (Lc 1)`. Rewrite using `[aeval_Lc_one, map_add, map_one, map_pow, swapF_uF]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem swapF_Lc (j : Fin 2) : swapF (aeval y (Lc j)) = (uF ^ 2)⁻¹ * aeval y (Lc j) := by
  have hu := uF_ne_zero
  fin_cases j
  · show swapF (aeval y (Lc 0)) = _ * aeval y (Lc 0)
    rw [aeval_Lc_zero, swapF_uF]
    field_simp
  · show swapF (aeval y (Lc 1)) = _ * aeval y (Lc 1)
    rw [aeval_Lc_one, map_add, map_one, map_pow, swapF_uF]
    field_simp
    ring

/- English proof (translation)
Establish `h1 : ∀ i : Fin 2, IsMultiHomog (X ⟨(), i⟩ : MRing (GlobalTheory (Fin 2))) (fun _ : Unit => 1)`. Introduce `i`. Use `isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), i⟩ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Establish `h2 : ∀ i i' : Fin 2, IsMultiHomog (X ⟨(), i⟩ * X ⟨(), i'⟩ : MRing (GlobalTheory (Fin 2))) (fun _ : Unit => 2)`. Introduce `i i'`. Use `mhMul (h1 i) (h1 i') using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Use `match j with`. Consider the case `0 => rw [Lc_zero]`. Conclude with `h2 0 1`. Consider the case `1 => rw [Lc_one, pow_two, pow_two]`. Conclude with `mhAdd (h2 0 0) (h2 1 1)`.
-/
theorem isMultiHomog_Lc (j : Fin 2) : IsMultiHomog (Lc j) (fun _ : Unit => 2) := by
  have h1 : ∀ i : Fin 2, IsMultiHomog (X ⟨(), i⟩ : MRing (GlobalTheory (Fin 2))) (fun _ : Unit => 1) := by
    intro i
    convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), i⟩ using 1
    funext k
    simp
  have h2 : ∀ i i' : Fin 2, IsMultiHomog (X ⟨(), i⟩ * X ⟨(), i'⟩ : MRing (GlobalTheory (Fin 2))) (fun _ : Unit => 2) := by
    intro i i'
    convert mhMul (h1 i) (h1 i') using 1
    funext k
    simp
  match j with
  | 0 => rw [Lc_zero]; exact h2 0 1
  | 1 => rw [Lc_one, pow_two, pow_two]; exact mhAdd (h2 0 0) (h2 1 1)

/- English proof (translation)
Introduce `z hz`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0` using `hcon 0`. Establish `h1` using `hcon 1`.

Simplify using `[Lc] at h0 h1`. Take `⟨i, hi⟩` from `hz.1 ()`. Break down `h0 with h0 | h0` into its components or cases. Rewrite `h1` using `[h0]`. Establish `: z ⟨(), 1⟩ = 0` using `by simpa using h1`.

Apply the tactic sequence `fin_cases i <;> simp_all`. Rewrite `h1` using `[h0]`. Establish `: z ⟨(), 0⟩ = 0` using `by simpa using h1`. Apply the tactic sequence `fin_cases i <;> simp_all`.
-/
theorem Lc_no_common_zero : ∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃ j : Fin 2,
    eval z (map (Int.castRingHom ℂ) (Lc j)) ≠ 0 := by
  intro z hz
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  simp [Lc] at h0 h1
  obtain ⟨i, hi⟩ := hz.1 ()
  rcases h0 with h0 | h0
  · rw [h0] at h1
    have : z ⟨(), 1⟩ = 0 := by simpa using h1
    fin_cases i <;> simp_all
  · rw [h0] at h1
    have : z ⟨(), 0⟩ = 0 := by simpa using h1
    fin_cases i <;> simp_all

/- English proof (translation)
Introduce `c hc`. Establish `hmem : ∀ x ∈ chartRingZ y c, x ∈ integralClosure (chartRingZ y c) FnField` using `fun x hx => isIntegral_algebraMap (R := chartRingZ y c) (A := FnField) (x := ⟨x, hx⟩)`. Apply `hmem` to reduce the goal to its premises. Rewrite using `[one_mul, Fintype.prod_unique]`. Establish `hq : ∀ p : (Σ k, GlobalTheory (Fin 2) k), y p / y ⟨p.1, c p.1⟩ ∈ chartRingZ y c` using `fun p => Algebra.subset_adjoin ⟨p, rfl⟩`.

Establish `hc0` using `hq ⟨(), 0⟩`. Simplify using `only [y_zero] at hc0`. Choose the witnesses or unpack the hypotheses as in `h | h : c default = 0 ∨ c default = 1 := by`. Apply the tactic sequence `rcases Fin.exists_fin_two.mp ⟨c default, rfl⟩ with h | h <;> simp_all`. Rewrite using `[h, y_zero, one_zpow]`.

Conclude with `one_mem _`. Establish `e : y ⟨default, c default⟩ ^ (-((1 : ℕ) * ((1 * 2 : ℕ) : ℤ))) = (1 / y ⟨(), c ()⟩) ^ 2`. Simplify using `[zpow_neg, h]`. Rewrite using `[e]`. Conclude with `pow_mem hc0 2`.
-/
theorem one_mem_chartLatNm : (1 : FnField) ∈ chartLatNm (ι := GlobalTheory (Fin 2)) y (fun _ => ((1 * 2 : ℕ) : ℤ)) 1 := by
  intro c hc
  have hmem : ∀ x ∈ chartRingZ y c, x ∈ integralClosure (chartRingZ y c) FnField :=
    fun x hx => isIntegral_algebraMap (R := chartRingZ y c) (A := FnField) (x := ⟨x, hx⟩)
  apply hmem
  rw [one_mul, Fintype.prod_unique]
  have hq : ∀ p : (Σ k, GlobalTheory (Fin 2) k), y p / y ⟨p.1, c p.1⟩ ∈ chartRingZ y c :=
    fun p => Algebra.subset_adjoin ⟨p, rfl⟩
  have hc0 := hq ⟨(), 0⟩
  simp only [y_zero] at hc0
  obtain h | h : c default = 0 ∨ c default = 1 := by
    rcases Fin.exists_fin_two.mp ⟨c default, rfl⟩ with h | h <;> simp_all
  · rw [h, y_zero, one_zpow]
    exact one_mem _
  · have e : y ⟨default, c default⟩ ^ (-((1 : ℕ) * ((1 * 2 : ℕ) : ℤ))) = (1 / y ⟨(), c ()⟩) ^ 2 := by
      simp [zpow_neg, h]
    rw [e]
    exact pow_mem hc0 2

end ProjLine

namespace FibreNormCharpoly

open ProjLine

/- English proof (translation)
Introduce `H`. Establish `hyp` using `FibreNormCharpoly.hyps_inhabited`. Take `⟨-, hH⟩` from `H Unit (GlobalTheory (Fin 2)) FnField y 1 (fun _ => 2) Lc 1 hyp.2.1.1 hyp.2.1.2 (fun _ => by norm_num) isMultiHomog_Lc Lc_no_common_zero`. Take `⟨c, hc, -⟩` from `hH 1 1 one_mem_chartLatNm`. Establish `hμ : ∀ d, 0 < d → ((uF ^ 2)⁻¹) ^ d ≠ 1`.

Introduce `d hd h`. Rewrite `h` using `[inv_pow, inv_eq_one, ← pow_mul]`. Conclude with `uF_pow_ne_one (by omega) h`. Conclude with `one_ne_zero (eq_zero_of_isNormForms swapF ((uF ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero _ uF_ne_zero)) swapF_Lc hμ (by norm_num) hc)`.
-/
theorem statement_false : ¬ FibreNormCharpoly.Statement := by
  intro H
  have hyp := FibreNormCharpoly.hyps_inhabited
  obtain ⟨-, hH⟩ := H Unit (GlobalTheory (Fin 2)) FnField y 1 (fun _ => 2) Lc 1 hyp.2.1.1 hyp.2.1.2
    (fun _ => by norm_num) isMultiHomog_Lc Lc_no_common_zero
  obtain ⟨c, hc, -⟩ := hH 1 1 one_mem_chartLatNm
  have hμ : ∀ d, 0 < d → ((uF ^ 2)⁻¹) ^ d ≠ 1 := by
    intro d hd h
    rw [inv_pow, inv_eq_one, ← pow_mul] at h
    exact uF_pow_ne_one (by omega) h
  exact one_ne_zero (eq_zero_of_isNormForms swapF ((uF ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero _ uF_ne_zero))
    swapF_Lc hμ (by norm_num) hc)

end FibreNormCharpoly

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
