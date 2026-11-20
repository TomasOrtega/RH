import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRoots

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `hi : IsIntegral ℚ z` using `hz.isIntegral`. Use `set p := minpoly ℚ z with hp`. Establish `hm : p.Monic` using `minpoly.monic hi`. Establish `hqm : (p.map (algebraMap ℚ Ω)).Monic` using `hm.map _`.

Establish `hroots` using `hqm.roots_map_of_card_eq_natDegree ε IsAlgClosed.card_roots_eq_natDegree`. Establish `hcomp : ε.comp (algebraMap ℚ Ω) = algebraMap ℚ ℂ` using `Subsingleton.elim _ _`. Rewrite `hroots` using `[Polynomial.map_map, hcomp]`. Establish `hne : p.map (algebraMap ℚ ℂ) ≠ 0` using `(hm.map _).ne_zero`. Establish `hzr : z ∈ (p.map (algebraMap ℚ ℂ)).roots`.

Rewrite using `[Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]`. Conclude with `minpoly.aeval ℚ z`. Rewrite `hzr` using `[← hroots]`. Take `⟨w, -, hw⟩` from `Multiset.mem_map.1 hzr`. Conclude with `⟨w, hw⟩`.
-/
theorem alg_mem_range (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (z : ℂ) (hz : IsAlgebraic ℚ z) : z ∈ ε.range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hi : IsIntegral ℚ z := hz.isIntegral
  set p := minpoly ℚ z with hp
  have hm : p.Monic := minpoly.monic hi
  have hqm : (p.map (algebraMap ℚ Ω)).Monic := hm.map _
  have hroots := hqm.roots_map_of_card_eq_natDegree ε IsAlgClosed.card_roots_eq_natDegree
  have hcomp : ε.comp (algebraMap ℚ Ω) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  rw [Polynomial.map_map, hcomp] at hroots
  have hne : p.map (algebraMap ℚ ℂ) ≠ 0 := (hm.map _).ne_zero
  have hzr : z ∈ (p.map (algebraMap ℚ ℂ)).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval ℚ z
  rw [← hroots] at hzr
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hzr
  exact ⟨w, hw⟩

/- English proof (translation)
Establish `hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1`. Rewrite using `[← Complex.exp_nat_mul]`. Establish `: (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I)`. Establish `hx : (x : ℂ) = (x.num : ℂ) / (x.den : ℂ)`. Conclude with `(Rat.num_div_den x).symm` after adjusting the coercions.

Establish `hd : (x.den : ℂ) ≠ 0` using `by exact_mod_cast x.den_nz`. Rewrite using `[hx]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Use `⟨Polynomial.X ^ x.den - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero x.pos 1, ?_⟩` and prove the remaining obligations.

Simplify using `[hpow]`.
-/
theorem exp_isAlgebraic (x : ℚ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) := by
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hx : (x : ℂ) = (x.num : ℂ) / (x.den : ℂ) := by
        exact_mod_cast (Rat.num_div_den x).symm
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_nz
      rw [hx]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  refine ⟨Polynomial.X ^ x.den - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero x.pos 1, ?_⟩
  simp [hpow]

/- English proof (translation)
Introduce `Ω _ _ _ ε`. Establish `hr : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range` using `fun x => alg_mem_range Ω ε _ (exp_isAlgebraic x)`. Establish `he : ∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))`. Introduce `x`. Take `⟨w, hw⟩` from `hr x`.

Conclude with `Function.invFun_eq ⟨w, hw⟩`. Establish `hinj : Function.Injective ε` using `ε.injective`. Use `⟨hr, he, ?_, ?_, ?_, fun z hz => alg_mem_range Ω ε z hz⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[he, map_one]`.

Simplify using the standard rewrite rules. Introduce `x y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, he, he, he, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `N hN`. Apply `IsPrimitiveRoot.of_map_of_injective (f := ε) _ hinj` to reduce the goal to its premises. Rewrite using `[he]`.

Establish `h` using `Complex.isPrimitiveRoot_exp N hN.ne'`. Use `h using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  intro Ω _ _ _ ε
  have hr : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range :=
    fun x => alg_mem_range Ω ε _ (exp_isAlgebraic x)
  have he : ∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    intro x
    obtain ⟨w, hw⟩ := hr x
    exact Function.invFun_eq ⟨w, hw⟩
  have hinj : Function.Injective ε := ε.injective
  refine ⟨hr, he, ?_, ?_, ?_, fun z hz => alg_mem_range Ω ε z hz⟩
  · apply hinj; rw [he, map_one]; simp
  · intro x y; apply hinj
    rw [map_mul, he, he, he, ← Complex.exp_add]; congr 1; push_cast; ring
  · intro N hN
    apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ hinj
    rw [he]
    have h := Complex.isPrimitiveRoot_exp N hN.ne'
    convert h using 2
    push_cast; ring

end GlobalTheory.FNRoots
