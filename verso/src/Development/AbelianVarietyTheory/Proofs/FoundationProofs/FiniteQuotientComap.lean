import Mathlib

open NumberField

namespace GlobalTheory.FiniteQuotientComap

/- English proof (translation)
Take `⟨m, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ) (M := nonZeroDivisors ℤ) a (Algebra.IsIntegral.isIntegral a)`. Use `⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, (⟨m • a, hm⟩ : 𝓞 E), ?_⟩` and prove the remaining obligations. Use `show m • a = _`. Rewrite using `[Submonoid.smul_def, zsmul_eq_mul]`.
-/
theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ b : 𝓞 E, (b : E) = (m : E) * a := by

  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) a (Algebra.IsIntegral.isIntegral a)
  refine ⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, (⟨m • a, hm⟩ : 𝓞 E), ?_⟩
  show m • a = _
  rw [Submonoid.smul_def, zsmul_eq_mul]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨m, hm0, hm⟩` from `hy`.

Take `⟨k, hk0, hk⟩` from `hz`. Use `⟨m * k, mul_ne_zero hm0 hk0, ?_⟩` and prove the remaining obligations. Establish `e1 : (m * k) • y = k • (m • y)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (m * k) • z = m • (k • z)` using `mul_smul m k z`. Rewrite using `[smul_add, e1, e2]`.

Conclude with `add_mem (zsmul_mem hm k) (zsmul_mem hk m)`. Consider the case `smul c y _ hy`. Take `⟨m, hm0, hm⟩` from `hy`. Take `⟨k, hk0, b, hb⟩` from `exists_int_mul_mem c`. Use `⟨k * m, mul_ne_zero hk0 hm0, ?_⟩` and prove the remaining obligations.

Establish `e : (k * m) • (c • y) = b • (m • y)`. Use extensionality with `i`. Simplify using `[Algebra.smul_def, hb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `L.smul_mem b hm`.
-/
theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, hk⟩ := hz
    refine ⟨m * k, mul_ne_zero hm0 hk0, ?_⟩
    have e1 : (m * k) • y = k • (m • y) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • z = m • (k • z) := mul_smul m k z
    rw [smul_add, e1, e2]
    exact add_mem (zsmul_mem hm k) (zsmul_mem hk m)
  | smul c y _ hy =>

    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, b, hb⟩ := exists_int_mul_mem c
    refine ⟨k * m, mul_ne_zero hk0 hm0, ?_⟩
    have e : (k * m) • (c • y) = b • (m • y) := by
      ext i
      simp [Algebra.smul_def, hb]
      ring
    rw [e]
    exact L.smul_mem b hm

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) L₀` using `Module.Finite.iff_fg.mpr h₀`. Establish `: Module.Finite ℤ L₀` using `Module.Finite.trans (𝓞 E) L₀`. Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective (Submodule.comap L₀.subtype L) q`.

Take `⟨m, hm0, hm⟩` from `exists_int_smul_mem L (y : Fin n → E) (by rw [hL]; exact Submodule.mem_top)`. Use `⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m : ℤ) • (Submodule.Quotient.mk y : L₀ ⧸ Submodule.comap L₀.subtype L) = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Simplify using `using hm`.
-/
theorem finite_quotient_comap {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L₀ L : Submodule (𝓞 E) (Fin n → E)) (h₀ : L₀.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by

  have : Module.Finite (𝓞 E) L₀ := Module.Finite.iff_fg.mpr h₀
  have : Module.Finite ℤ L₀ := Module.Finite.trans (𝓞 E) L₀
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap L₀.subtype L) q
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem L (y : Fin n → E) (by rw [hL]; exact Submodule.mem_top)
  refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, ?_⟩
  change (m : ℤ) • (Submodule.Quotient.mk y : L₀ ⧸ Submodule.comap L₀.subtype L) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  simpa using hm

end GlobalTheory.FiniteQuotientComap
