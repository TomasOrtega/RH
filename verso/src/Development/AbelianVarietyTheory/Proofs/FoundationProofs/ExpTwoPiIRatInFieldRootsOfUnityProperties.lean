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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
