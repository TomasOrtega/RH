import Mathlib
import Formalism.PeriodIntegrals.ArtSch

namespace PI.ArtSch.RootWork

open Polynomial

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Set `p : (OC l)[X]` to `X ^ l - (C c * X + C b)`. Establish `hdeg : (C c * X + C b).degree < (X ^ l : (OC l)[X]).degree`. Rewrite using `[degree_X_pow]`. Conclude with `lt_of_le_of_lt degree_linear_le (by exact_mod_cast (show 1 < l by omega))`.

Establish `hmon : p.Monic` using `(monic_X_pow l).sub_of_left hdeg`. Establish `hnat : p.natDegree = l`. Apply `natDegree_eq_of_degree_eq_some` to reduce the goal to its premises. Rewrite using `[degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]`. Set `q : ℂ_[l][X]` to `p.map (algebraMap (OC l) ℂ_[l])`.

Establish `hq : q.degree ≠ 0`. Rewrite using `[degree_eq_natDegree (hmon.map _).ne_zero, (hmon.natDegree_map _), hnat]`. Conclude with `(show l ≠ 0 by omega)` after adjusting the coercions. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root q hq`. Establish `hx' : eval₂ (algebraMap (OC l) ℂ_[l]) x p = 0`.

Rewrite using `[← eval_map]`. Conclude with `hx`. Establish `hint : IsIntegral (OC l) x` using `⟨p, hmon, hx'⟩`. Establish `hmem : x ∈ PadicComplexInt l` using `(PadicComplexInt.integers l).mem_of_integral hint`. Use `⟨⟨x, hmem⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2 : eval₂ (algebraMap (OC l) ℂ_[l]) x p = x ^ l - ((c : ℂ_[l]) * x + (b : ℂ_[l]))`. Simplify using `only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C]`. Both sides reduce to the same expression. Rewrite `hx'` using `[h2]`.

Use `show x ^ l - (c : ℂ_[l]) * x - (b : ℂ_[l]) = 0`. Rewrite using `[sub_sub]`. Conclude with `hx'`.
-/
theorem exists_root_OC (c b : OC l) : ∃ z : OC l, z ^ l - c * z - b = 0 := by
  classical
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  let p : (OC l)[X] := X ^ l - (C c * X + C b)
  have hdeg : (C c * X + C b).degree < (X ^ l : (OC l)[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast (show 1 < l by omega))
  have hmon : p.Monic := (monic_X_pow l).sub_of_left hdeg
  have hnat : p.natDegree = l := by
    apply natDegree_eq_of_degree_eq_some
    rw [degree_sub_eq_left_of_degree_lt hdeg, degree_X_pow]
  let q : ℂ_[l][X] := p.map (algebraMap (OC l) ℂ_[l])
  have hq : q.degree ≠ 0 := by
    rw [degree_eq_natDegree (hmon.map _).ne_zero, (hmon.natDegree_map _), hnat]
    exact_mod_cast (show l ≠ 0 by omega)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hq
  have hx' : eval₂ (algebraMap (OC l) ℂ_[l]) x p = 0 := by
    rw [← eval_map]
    exact hx
  have hint : IsIntegral (OC l) x := ⟨p, hmon, hx'⟩
  have hmem : x ∈ PadicComplexInt l := (PadicComplexInt.integers l).mem_of_integral hint
  refine ⟨⟨x, hmem⟩, ?_⟩
  apply Subtype.ext
  have h2 : eval₂ (algebraMap (OC l) ℂ_[l]) x p = x ^ l - ((c : ℂ_[l]) * x + (b : ℂ_[l])) := by
    simp only [p, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C]
    rfl
  rw [h2] at hx'
  show x ^ l - (c : ℂ_[l]) * x - (b : ℂ_[l]) = 0
  rw [sub_sub]
  exact hx'

end PI.ArtSch.RootWork
