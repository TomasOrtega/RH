import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
open GlobalTheory.LogU

namespace GlobalTheory.LogU

open MvPolynomial

/- English proof (translation)
Introduce `n i j hij`. Set `J : Ideal (MvPolynomial (Fin 2) ℚ)` to `MvPolynomial.idealOfVars (Fin 2) ℚ`. Set `q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n` to `Ideal.Quotient.mk _`. Establish `hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n)` using `fun m hm => by`. Establish `hu : IsUnit ((m : ℚ))` using `(Nat.cast_ne_zero.2 hm).isUnit`.

Simplify using `using hu.map (q.comp MvPolynomial.C)`. Establish `hI : (J.map q) ^ n = ⊥`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.map_quotient_self _`. Establish `hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J` using `fun k => Ideal.subset_span (Set.mem_range_self k)`.

Establish `key` using `GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1)) (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))`. Establish `h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0`. Use `(aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_` and prove the remaining obligations. Simplify using `only [truncLogF]`. Rewrite using `[key]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) = (MvPolynomial.aeval (R` using `ℤ) ![q (X 0), q (X 1)]).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules.

Apply the tactic sequence `intro k; fin_cases k <;> simp`. Establish `hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0`. Use `RingHom.congr_fun hcomp (logDefect n)` as an intermediate fact. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this`. Rewrite using `[this, h0]`.

Rewrite `hφ` using `[Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff']`. Establish `hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n` using `by first`. Consider the case `simpa [Finsupp.degree_single] using hij`. Consider the case `simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij`. Use `hφ _ hd` as an intermediate fact.

Rewrite `this` using `[MvPolynomial.coeff_map]`. Simplify using `using this`.
-/
theorem logDefect_coeff_eq_zero : ∀ (n i j : ℕ), i + j < n →
    MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (GlobalTheory.LogU.logDefect n) = 0 := by
  intro n i j hij
  let J : Ideal (MvPolynomial (Fin 2) ℚ) := MvPolynomial.idealOfVars (Fin 2) ℚ
  let q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n) := fun m hm => by
    have hu : IsUnit ((m : ℚ)) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hu.map (q.comp MvPolynomial.C)
  have hI : (J.map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _
  have hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J := fun k =>
    Ideal.subset_span (Set.mem_range_self k)
  have key := GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1))
    (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))
  have h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0 := by
    refine (aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_
    simp only [truncLogF]; rw [key]; ring
  have hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.aeval (R := ℤ) ![q (X 0), q (X 1)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro k; fin_cases k <;> simp
  have hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0 := by
    have := RingHom.congr_fun hcomp (logDefect n)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, h0]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at hφ
  have hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n := by
    first
      | simpa [Finsupp.degree_single] using hij
      | simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij
  have := hφ _ hd
  rw [MvPolynomial.coeff_map] at this
  simpa using this

end GlobalTheory.LogU
