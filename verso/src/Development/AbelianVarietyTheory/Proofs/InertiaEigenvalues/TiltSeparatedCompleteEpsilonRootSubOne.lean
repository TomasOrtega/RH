import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf

namespace GlobalTheory.TiltComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

section General

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

/- English proof (translation)
Proceed by induction on `N, h using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ N h ih`. Rewrite using `[Finset.sum_range_succ, map_add, ih, map_mul, map_pow, pow_eq_zero_of_le h hM, zero_mul, add_zero]`.
-/
theorem coeff_sum_stable (t : Perfection R p) (a : ℕ → Perfection R p) (n M N : ℕ)
    (hM : Perfection.coeff R p n t ^ M = 0) (h : M ≤ N) :
    Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) =
      Perfection.coeff R p n (∑ i ∈ Finset.range M, t ^ i * a i) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    rw [Finset.sum_range_succ, map_add, ih, map_mul, map_pow, pow_eq_zero_of_le h hM, zero_mul,
      add_zero]

/- English proof (translation)
Use `⟨⟨fun n => Perfection.coeff R p n (∑ i ∈ Finset.range (M n), t ^ i * a i), fun n => ?_⟩, fun n N h => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← coeff_sum_stable t a (n + 1) _ _ (hM _) (le_max_left (M (n + 1)) (M n)), ← coeff_sum_stable t a n _ _ (hM _) (le_max_right (M (n + 1)) (M n)), Perfection.coeff_pow_p']`. Rewrite using `[Perfection.coeff_mk, coeff_sum_stable t a n _ _ (hM _) h]`.
-/
theorem exists_limit (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) (a : ℕ → Perfection R p) :
    ∃ x : Perfection R p, ∀ n N, M n ≤ N →
      Perfection.coeff R p n x = Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) := by
  refine ⟨⟨fun n => Perfection.coeff R p n (∑ i ∈ Finset.range (M n), t ^ i * a i), fun n => ?_⟩,
    fun n N h => ?_⟩
  · beta_reduce
    rw [← coeff_sum_stable t a (n + 1) _ _ (hM _) (le_max_left (M (n + 1)) (M n)),
      ← coeff_sum_stable t a n _ _ (hM _) (le_max_right (M (n + 1)) (M n)),
      Perfection.coeff_pow_p']
  · rw [Perfection.coeff_mk, coeff_sum_stable t a n _ _ (hM _) h]

/- English proof (translation)
Use `⟨fun x hx => Perfection.ext fun n => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hx (M n)`. Rewrite using `[map_mul, map_pow, hM, zero_mul, map_zero]`. Take `⟨x, hx⟩` from `exists_limit t M hM a`. Use `⟨x, fun m => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy⟩` from `exists_limit t M hM fun i => a (m + i)`. Use `⟨y, Perfection.ext fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, hx n (m + M n) (Nat.le_add_left _ _), hy n (M n) le_rfl, ← map_mul, ← map_sub, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_assoc]`.
-/
theorem separated_complete (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) :
    (∀ x : Perfection R p, (∀ m : ℕ, t ^ m ∣ x) → x = 0) ∧
      ∀ a : ℕ → Perfection R p, ∃ x : Perfection R p, ∀ m : ℕ,
        t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i := by
  refine ⟨fun x hx => Perfection.ext fun n => ?_, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hx (M n)
    rw [map_mul, map_pow, hM, zero_mul, map_zero]
  · obtain ⟨x, hx⟩ := exists_limit t M hM a
    refine ⟨x, fun m => ?_⟩
    obtain ⟨y, hy⟩ := exists_limit t M hM fun i => a (m + i)
    refine ⟨y, Perfection.ext fun n => ?_⟩
    rw [map_sub, map_mul, hx n (m + M n) (Nat.le_add_left _ _), hy n (M n) le_rfl, ← map_mul,
      ← map_sub, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_assoc]

end General

/- English proof (translation)
Introduce `l _ P AI s`. Use `separated_complete (R := ModP (OC l) l) (p := l) (AI.εroot s - 1 : OCb l) (fun n => l ^ (s + n)) fun n => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n (AI.εroot s - 1) ^ l ^ (s + n) = 0`. Establish `h` using `ζ_add_pow AI 0 (s + n)`. Rewrite `h` using `[zero_add, AI.ζ_zero]`.

Rewrite using `[map_sub, map_one, sub_pow_char_pow, coeff_εroot, ← map_pow, h, map_one, one_pow, sub_self]`.
-/
theorem tilt_separated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), (∀ x : OCb l, (∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x) → x = 0) ∧ ∀ a : ℕ → OCb l, ∃ x : OCb l, ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x - ∑ i ∈ Finset.range m, (AI.εroot s - 1) ^ i * a i := by
  intro l _ P AI s
  refine separated_complete (R := ModP (OC l) l) (p := l) (AI.εroot s - 1 : OCb l)
    (fun n => l ^ (s + n)) fun n => ?_
  change PreTilt.coeff n (AI.εroot s - 1) ^ l ^ (s + n) = 0
  have h := ζ_add_pow AI 0 (s + n)
  rw [zero_add, AI.ζ_zero] at h
  rw [map_sub, map_one, sub_pow_char_pow, coeff_εroot, ← map_pow, h, map_one, one_pow, sub_self]

end GlobalTheory.TiltComplete
