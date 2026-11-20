import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {σ : Type}

abbrev qmap : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

def qIdeal (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) := P.map qmap

/- English proof (translation)
The claim follows from `MvPolynomial.map_injective _ Int.cast_injective`.
-/
theorem qmap_injective : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective _ Int.cast_injective

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Use `⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩` and prove the remaining obligations. Rewrite using `[show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm, C_mul_monomial, MvPolynomial.map_monomial]`. Use `congr 1`.

Use `push_cast`. Conclude with `Rat.den_mul_eq_num a`. Consider the case `add p q hp hq`. Take `⟨D₁, hD₁, p', hp'⟩` from `hp`. Take `⟨D₂, hD₂, q', hq'⟩` from `hq`.

Use `⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_mul_eq_qmap (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩
    rw [show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm,
      C_mul_monomial, MvPolynomial.map_monomial]
    congr 1
    push_cast
    exact Rat.den_mul_eq_num a
  | add p q hp hq =>
    obtain ⟨D₁, hD₁, p', hp'⟩ := hp
    obtain ⟨D₂, hD₂, q', hq'⟩ := hq
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']
    push_cast
    ring

/- English proof (translation)
Establish `hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ)))` using `hg`. Use `clear hg`. Proceed by induction on `hg' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, hh, rfl⟩` from `hx`.

Conclude with `⟨1, one_ne_zero, h, hh, by simp⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨N₁, hN₁, h₁, hh₁, e₁⟩` from `hx`. Take `⟨N₂, hN₂, h₂, hh₂, e₂⟩` from `hy`.

Use `⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂, P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a x _ hx`.

Take `⟨N, hN, h, hh, e⟩` from `hx`. Take `⟨D, hD, a', ha'⟩` from `exists_int_mul_eq_qmap a`. Use `⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← ha', ← e, smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_mul_mem_of_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by
  have hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨1, one_ne_zero, h, hh, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁, hh₁, e₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂, hh₂, e₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂,
      P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]
    push_cast
    ring
  | smul a x _ hx =>
    obtain ⟨N, hN, h, hh, e⟩ := hx
    obtain ⟨D, hD, a', ha'⟩ := exists_int_mul_eq_qmap a
    refine ⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩
    rw [map_mul, ← ha', ← e, smul_eq_mul]
    push_cast
    ring

/- English proof (translation)
Take `⟨N, hN, h, hh, e⟩` from `exists_int_mul_mem_of_mem_qIdeal P hf`. Establish `hNf : (N : MvPolynomial σ ℤ) * f = h`. Apply `qmap_injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_intCast, e]`. Rewrite `hh` using `[← hNf, show (N : MvPolynomial σ ℤ) = C N from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) N).symm]`.

Break down `hP.mem_or_mem hh with hC | hf'` into its components or cases. Establish `: N ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ)` using `hC`. Rewrite `this` using `[hH]`. Conclude with `absurd ((Submodule.mem_bot ℤ).mp this) hN`. Conclude with `hf'`.
-/
theorem mem_of_qmap_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {f : MvPolynomial σ ℤ}
    (hf : qmap f ∈ qIdeal P) : f ∈ P := by
  obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hf
  have hNf : (N : MvPolynomial σ ℤ) * f = h := by
    apply qmap_injective
    rw [map_mul, map_intCast, e]
  rw [← hNf, show (N : MvPolynomial σ ℤ) = C N from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) N).symm] at hh
  rcases hP.mem_or_mem hh with hC | hf'
  · have : N ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hC
    rw [hH] at this
    exact absurd ((Submodule.mem_bot ℤ).mp this) hN
  · exact hf'

def ratHom (P : Ideal (MvPolynomial σ ℤ)) :
    MvPolynomial σ ℤ ⧸ P →+* MvPolynomial σ ℚ ⧸ qIdeal P :=
  Ideal.quotientMap (qIdeal P) qmap Ideal.le_comap_map

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratHom_mk (P : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ) :
    ratHom P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (qIdeal P) (qmap f) := rfl

/- English proof (translation)
Set `_` to `(ratHom P).toAlgebra`. Establish `hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P) (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n`. Introduce `n`. Rewrite using `[eq_intCast, map_intCast, map_intCast]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, hy⟩`. Take `⟨n, hn, rfl⟩` from `Submonoid.mem_map.mp hy`. Rewrite using `[hcast]`. Conclude with `(IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _`. Introduce `z`.

Take `⟨q, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨D, hD, q', hq'⟩` from `exists_int_mul_eq_qmap q`. Use `⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D, Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')`. Rewrite using `[hcast, ratHom_mk, ← hq', mul_comm, map_mul]`.

Use `congr 1`. Introduce `x y hxy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Express the relevant statement in the definitionally equal form `ratHom P _ = ratHom P _ at hxy`.

Rewrite `hxy` using `[ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub]`. Take `⟨N, hN, h, hh, e⟩` from `exists_int_mul_mem_of_mem_qIdeal P hxy`. Establish `hNab : (N : MvPolynomial σ ℤ) * (a - b) = h`. Apply `qmap_injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_intCast, e]`.

Use `⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b`. Rewrite using `[← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul, hNab, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hh`.
-/
theorem ratHom_isLocalization (P : Ideal (MvPolynomial σ ℤ)) :
    letI := (ratHom P).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
      (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P)
      (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n := by
    intro n
    rw [eq_intCast, map_intCast, map_intCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hy
    rw [hcast]
    exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _
  · intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨D, hD, q', hq'⟩ := exists_int_mul_eq_qmap q
    refine ⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D,
      Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩
    change _ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')
    rw [hcast, ratHom_mk, ← hq', mul_comm, map_mul]
    congr 1
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change ratHom P _ = ratHom P _ at hxy
    rw [ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hxy
    have hNab : (N : MvPolynomial σ ℤ) * (a - b) = h := by
      apply qmap_injective
      rw [map_mul, map_intCast, e]
    refine ⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩
    change algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul,
      hNab, Ideal.Quotient.eq_zero_iff_mem]
    exact hh

/- English proof (translation)
Set `_` to `(ratHom P).toAlgebra`. Use `ratHom_isLocalization P` as an intermediate fact. Use `IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P) (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ)) (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Apply `mem_nonZeroDivisors_of_ne_zero` to reduce the goal to its premises.

Introduce `h0`. Rewrite `h0` using `[eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem, show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm]`. Establish `: n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ)` using `h0`. Rewrite `this` using `[hH]`. Conclude with `nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)`.
-/
theorem isDomain_qQuot (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) :
    IsDomain (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have := ratHom_isLocalization P
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P)
    (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
    (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm] at h0
  have : n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h0
  rw [hH] at this
  exact nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)

end

end ReciprocityTheory.ChartRestriction.G.Geo
