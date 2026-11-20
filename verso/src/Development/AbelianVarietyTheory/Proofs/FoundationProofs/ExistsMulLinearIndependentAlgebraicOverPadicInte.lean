import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5

namespace GlobalTheory.K5.ReprInd

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `a f _`. Use `⟨0, a, f, 1, by simp, linearIndependent_empty_type, one_ne_zero, by simp⟩` and prove the remaining obligations.

Consider the case `succ m ih`. Introduce `a f hP`. Distinguish the cases in `hli : LinearIndependent R a`. Conclude with `⟨m + 1, a, f, 1, hP, hli, one_ne_zero, one_smul _ _⟩`. Take `⟨c, hc, k, hk⟩` from `Fintype.not_linearIndependent_iff.mp hli`.

Take `⟨n, a', f', g, hP', hli', hg, heq⟩` from `ih (fun j => a (k.succAbove j)) (fun j => c k * f (k.succAbove j) - f k * c (k.succAbove j)) (fun j => hP _)`. Use `⟨n, a', f', g * c k, hP', hli', mul_ne_zero hg hk, ?_⟩` and prove the remaining obligations. Establish `key : c k • (∑ i, f i • a i) = ∑ j : Fin m, (c k * f (k.succAbove j) - f k * c (k.succAbove j)) • a (k.succAbove j)`. Establish `h1 : c k • (∑ i, f i • a i) = c k • (∑ i, f i • a i) - f k • (∑ i, c i • a i)`. Rewrite using `[hc, smul_zero, sub_zero]`.

Rewrite using `[h1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Fin.sum_univ_succAbove _ k]`. Simplify using `only [smul_smul, ← sub_smul]`. Rewrite using `[mul_comm (f k) (c k), sub_self, zero_smul, zero_add]`. Rewrite using `[mul_smul, key, heq]`.
-/
theorem aux {R Ω : Type*} [CommRing R] [IsDomain R] [AddCommGroup Ω] [Module R Ω] (P : Ω → Prop) :
    ∀ (m : ℕ) (a : Fin m → Ω) (f : Fin m → R), (∀ i, P (a i)) →
      ∃ (n : ℕ) (a' : Fin n → Ω) (f' : Fin n → R) (g : R), (∀ i, P (a' i)) ∧
        LinearIndependent R a' ∧ g ≠ 0 ∧ g • (∑ i, f i • a i) = ∑ i, f' i • a' i := by
  intro m
  induction m with
  | zero =>
    intro a f _
    refine ⟨0, a, f, 1, by simp, linearIndependent_empty_type, one_ne_zero, by simp⟩
  | succ m ih =>
    intro a f hP
    by_cases hli : LinearIndependent R a
    · exact ⟨m + 1, a, f, 1, hP, hli, one_ne_zero, one_smul _ _⟩
    · obtain ⟨c, hc, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hli
      obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := ih (fun j => a (k.succAbove j))
        (fun j => c k * f (k.succAbove j) - f k * c (k.succAbove j)) (fun j => hP _)
      refine ⟨n, a', f', g * c k, hP', hli', mul_ne_zero hg hk, ?_⟩
      have key : c k • (∑ i, f i • a i) =
          ∑ j : Fin m, (c k * f (k.succAbove j) - f k * c (k.succAbove j)) • a (k.succAbove j) := by
        have h1 : c k • (∑ i, f i • a i) = c k • (∑ i, f i • a i) - f k • (∑ i, c i • a i) := by
          rw [hc, smul_zero, sub_zero]
        rw [h1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
          Fin.sum_univ_succAbove _ k]
        simp only [smul_smul, ← sub_smul]
        rw [mul_comm (f k) (c k), sub_self, zero_smul, zero_add]
      rw [mul_smul, key, heq]

/- English proof (translation)
Introduce `y hy`. Take `⟨m, f, a, rfl⟩` from `Submodule.mem_span_set'.mp hy`. Take `⟨n, a', f', g, hP', hli', hg, heq⟩` from `aux P m (fun i => (a i : Ω)) f (fun i => (a i).2)`. Use `⟨n, a', f', g, hP', hli', hg, ?_⟩` and prove the remaining obligations. Simplify `heq` using `only [Algebra.smul_def]`.
-/
theorem main {R Ω : Type*} [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω] (P : Ω → Prop) :
    ∀ y ∈ Submodule.span R {x : Ω | P x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → R) (g : R), (∀ i, P (a i)) ∧
      LinearIndependent R a ∧ g ≠ 0 ∧
      algebraMap R Ω g * y = ∑ i, algebraMap R Ω (f i) * a i := by
  intro y hy
  obtain ⟨m, f, a, rfl⟩ := Submodule.mem_span_set'.mp hy
  obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := aux P m (fun i => (a i : Ω)) f (fun i => (a i).2)
  refine ⟨n, a', f', g, hP', hli', hg, ?_⟩
  simpa only [Algebra.smul_def] using heq

end GlobalTheory.K5.ReprInd

/- English proof (translation)
Introduce `p _ Ω _ _ _`. Conclude with `GlobalTheory.K5.ReprInd.main (fun x => IsAlgZp p x)`.
-/
theorem GlobalTheory.K5.algSpan_reprInd : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp p (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro p _ Ω _ _ _
  exact GlobalTheory.K5.ReprInd.main (fun x => IsAlgZp p x)
