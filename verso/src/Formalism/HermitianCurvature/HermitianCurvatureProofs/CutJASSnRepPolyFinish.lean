import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConst

open Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

/- English proof (translation)
Rewrite using `[Polynomial.eval_map]`. Establish `hx : (x : ℂ) = starRingEnd ℂ (x : ℂ)` using `(Complex.conj_ofReal x).symm`. Use `conv_lhs => rw [hx]`. Conclude with `Polynomial.eval₂_at_apply _ _`.
-/
theorem pf_conj_eval' (q : ℂ[X]) (x : ℝ) :
    (q.map (starRingEnd ℂ)).eval (x : ℂ) = starRingEnd ℂ (q.eval (x : ℂ)) := by
  rw [Polynomial.eval_map]
  have hx : (x : ℂ) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  conv_lhs => rw [hx]
  exact Polynomial.eval₂_at_apply _ _

/- English proof (translation)
Establish `hroots : Set.Infinite {z : ℂ | IsRoot (q * q.map (starRingEnd ℂ) - Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n)) z}`. Use `Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((a + 1 + m : ℝ) : ℂ)) ?_ ?_` and prove the remaining obligations. Introduce `s t hst`. Use `Complex.ofReal_injective hst` as an intermediate fact. Conclude with `(by linarith : (s : ℝ) = t)` after adjusting the coercions.

Introduce `m`. Simplify using `only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]`. Establish `hx : a < a + 1 + (m : ℝ)` using `by have := m.cast_nonneg (α := ℝ); linarith`. Rewrite using `[pf_conj_eval', Complex.mul_conj, h _ hx]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hroots)`.
-/
theorem pf_id (q : ℂ[X]) (n : ℕ) (a C : ℝ)
    (h : ∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) :
    q * q.map (starRingEnd ℂ) = Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n) := by
  have hroots : Set.Infinite {z : ℂ | IsRoot (q * q.map (starRingEnd ℂ) -
      Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n)) z} := by
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((a + 1 + m : ℝ) : ℂ)) ?_ ?_
    · intro s t hst
      have := Complex.ofReal_injective hst
      exact_mod_cast (by linarith : (s : ℝ) = t)
    · intro m
      simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      have hx : a < a + 1 + (m : ℝ) := by have := m.cast_nonneg (α := ℝ); linarith
      rw [pf_conj_eval', Complex.mul_conj, h _ hx]
      push_cast
      ring
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hroots)

/- English proof (translation)
Introduce `q n a C h`. Establish `hid` using `pf_id q n a C h`. Distinguish the cases in `hq : q = 0`. Conclude with `⟨0, by simp [hq]⟩`. Establish `hqb : q.map (starRingEnd ℂ) ≠ 0`.

Rewrite using `[Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]` and apply the resulting hypothesis. Establish `hC : (C : ℂ) ≠ 0`. Introduce `h0`. Rewrite `hid` using `[h0, Polynomial.C_0, zero_mul]`. Conclude with `mul_ne_zero hq hqb hid`.

Establish `hroot : ∀ b ∈ q.roots, b = (a : ℂ)`. Introduce `b hb`. Establish `hb0 : q.eval b = 0` using `(Polynomial.mem_roots hq).1 hb`. Use `congrArg (Polynomial.eval b) hid` as an intermediate fact. Simplify using `only [eval_mul, hb0, zero_mul, eval_C, eval_pow, eval_sub, eval_X] at this`.

Establish `h2` using `(mul_eq_zero.1 this.symm).resolve_left hC`. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff'.1 h2).1`. Establish `hcard : Multiset.card q.roots = q.natDegree` using `by first`. Consider the case `exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits q)).symm`. Consider the case `exact IsAlgClosed.card_roots_eq_natDegree`.

Establish `hrep : q.roots = Multiset.replicate q.natDegree (a : ℂ)`. Rewrite using `[← hcard]`. Conclude with `Multiset.eq_replicate.2 ⟨rfl, hroot⟩`. Establish `hform : q = Polynomial.C q.leadingCoeff * (X - Polynomial.C (a : ℂ)) ^ q.natDegree` using `by conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]`. Rewrite using `[hrep, Multiset.map_replicate, Multiset.prod_replicate]`.

Establish `hdeg : q.natDegree = n`. Establish `h1` using `congrArg Polynomial.natDegree hid`. Rewrite `h1` using `[Polynomial.natDegree_mul hq hqb, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _), Polynomial.natDegree_C_mul hC, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨q.leadingCoeff, by rw [← hdeg]; exact hform⟩`.
-/
theorem polynomial_finish_holds : PolyFinish := by
  intro q n a C h
  have hid := pf_id q n a C h
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hqb : q.map (starRingEnd ℂ) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
  have hC : (C : ℂ) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0, zero_mul] at hid
    exact mul_ne_zero hq hqb hid
  have hroot : ∀ b ∈ q.roots, b = (a : ℂ) := by
    intro b hb
    have hb0 : q.eval b = 0 := (Polynomial.mem_roots hq).1 hb
    have := congrArg (Polynomial.eval b) hid
    simp only [eval_mul, hb0, zero_mul, eval_C, eval_pow, eval_sub, eval_X] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left hC
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h2).1
  have hcard : Multiset.card q.roots = q.natDegree := by
    first
      | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits q)).symm
      | exact IsAlgClosed.card_roots_eq_natDegree
  have hrep : q.roots = Multiset.replicate q.natDegree (a : ℂ) := by
    rw [← hcard]; exact Multiset.eq_replicate.2 ⟨rfl, hroot⟩
  have hform : q = Polynomial.C q.leadingCoeff * (X - Polynomial.C (a : ℂ)) ^ q.natDegree := by
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [hrep, Multiset.map_replicate, Multiset.prod_replicate]
  have hdeg : q.natDegree = n := by
    have h1 := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hq hqb, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _),
      Polynomial.natDegree_C_mul hC, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at h1
    omega
  exact ⟨q.leadingCoeff, by rw [← hdeg]; exact hform⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
