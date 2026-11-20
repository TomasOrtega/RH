import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

/- English proof (translation)
Introduce `k K _ _ _ _ B Q hQ s m y T e he hs hgen ⟨a, r, ha, hr, hT⟩`. Set `g : Fin m → Ω[K⁄k]` to `fun j => D k K (y j)`. Set `f : Ω[K⁄k] →ₗ[K] ExteriorAlgebra K Ω[K⁄k]` to `(ExteriorAlgebra.ιMulti K (m+1)).toMultilinearMap.toLinearMap (Fin.cons 0 g) 0`. Establish `hf : ∀ v, f v = ExteriorAlgebra.ιMulti K (m+1) (Fin.cons v g : Fin (m+1) → Ω[K⁄k])`. Introduce `v`.

Simplify using `only [f, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]`. Both sides reduce to the same expression. Establish `hg0 : ∀ j, f (g j) = 0`. Introduce `j`. Rewrite using `[hf]`.

Conclude with `AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := j.succ) (by simp) (Fin.succ_ne_zero j).symm`. Establish `key : ∀ v : B, ∃ ρ : B, ρ ∉ Q ∧ ∃ c0 : B, (ρ : K) • f (D k K (v:K)) = (c0 : K) • f (D k K (s:K))`. Introduce `v`. Take `⟨ρ, hρ, c, hc⟩` from `hgen v`. Use `⟨ρ, hρ, c 0, ?_⟩` and prove the remaining obligations.

Establish `h2` using `congrArg f hc`. Rewrite `h2` using `[map_smul, map_sum, Fin.sum_univ_succ]`. Simplify `h2` using `[hg0, g]`. Take `⟨ρa, hρa, ca, hA⟩` from `key a`. Take `⟨ρr, hρr, cr, hR⟩` from `key r`.

Establish `hse : (s:K)^e = (s:K) * (s:K)^(e-1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hX : (r:K) • f (D k K T) + T • f (D k K (r:K)) = ((a:K) * (e:K) * (s:K)^(e-1)) • f (D k K (s:K)) + ((s:K) * (s:K)^(e-1)) • f (D k K (a:K))`.

Establish `h1` using `congrArg (fun z => f (D k K z)) hT`. Simplify using `only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_smul, map_nsmul] at h1`. Rewrite using `[← hse, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul K]`. Conclude with `h1`. Establish `heB : (e : B) ∉ Q`.

Introduce `h`. Establish `hu : IsUnit (e : B)`. Establish `h3 : (e : B) = algebraMap k B (e : k)` using `by simp`. Rewrite using `[h3]`. Conclude with `(isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))).map _`.

Conclude with `hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)`. Use `⟨ρa*ρr*(e:B)*a*r + s*(ρr*r*ca - ρa*a*cr), ρa*ρr*r^2, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h4 : ρa*ρr*(e:B)*a*r ∈ Q`. Use `Q.sub_mem h (Q.mul_mem_right (ρr*r*ca - ρa*a*cr) hs)` as an intermediate fact.

Simplify using `using this`. Break down `hQ.mem_or_mem h4 with h4 | h4` into its components or cases. Break down `hQ.mem_or_mem h4 with h4 | h4` into its components or cases. Break down `hQ.mem_or_mem h4 with h4 | h4` into its components or cases. Break down `hQ.mem_or_mem h4 with h4 | h4` into its components or cases.

Conclude with `hρa h4`. Conclude with `hρr h4`. Conclude with `heB h4`. Conclude with `ha h4`. Conclude with `hr h4`.

Introduce `h`. Break down `hQ.mem_or_mem h with h | h` into its components or cases. Break down `hQ.mem_or_mem h with h | h` into its components or cases. Conclude with `hρa h`. Conclude with `hρr h`.

Conclude with `hr (hQ.mem_of_pow_mem _ h)`. Establish `hT' : (r:K) * T = (a:K) * ((s:K) * (s:K)^(e-1))` using `by rw [hT, hse]`. Rewrite using `[← hf, ← hf]`. Use `push_cast`. Take the linear combination `(norm := module) ((ρa:K)*ρr*r) • hX + ((ρr:K)*r*s*(s:K)^(e-1)) • hA - ((ρa:K)*r*T) • hR - ((ρa:K)*cr) • hT' • f (D k K (s:K))`.
-/
theorem GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow : ∀ (k K : Type) [Field k] [CharZero k] [Field K] [Algebra k K] (B : Subalgebra k K) (Q : Ideal B), Q.IsPrime → ∀ (s : B) (m : ℕ) (y : Fin m → K) (T : K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, (r : K) • D k K (v : K) = ∑ l, (c l : K) • (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) l) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * T = a * s ^ e) → ∃ N Dn : B, N ∉ Q ∧ Dn ∉ Q ∧ (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K T) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) = ((N : K) * (s : K) ^ (e - 1)) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) := by
  intro k K _ _ _ _ B Q hQ s m y T e he hs hgen ⟨a, r, ha, hr, hT⟩
  classical
  let g : Fin m → Ω[K⁄k] := fun j => D k K (y j)
  let f : Ω[K⁄k] →ₗ[K] ExteriorAlgebra K Ω[K⁄k] :=
    (ExteriorAlgebra.ιMulti K (m+1)).toMultilinearMap.toLinearMap (Fin.cons 0 g) 0
  have hf : ∀ v, f v = ExteriorAlgebra.ιMulti K (m+1) (Fin.cons v g : Fin (m+1) → Ω[K⁄k]) := by
    intro v; simp only [f, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]; rfl
  have hg0 : ∀ j, f (g j) = 0 := by
    intro j; rw [hf]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := j.succ) (by simp) (Fin.succ_ne_zero j).symm
  have key : ∀ v : B, ∃ ρ : B, ρ ∉ Q ∧ ∃ c0 : B, (ρ : K) • f (D k K (v:K)) = (c0 : K) • f (D k K (s:K)) := by
    intro v
    obtain ⟨ρ, hρ, c, hc⟩ := hgen v
    refine ⟨ρ, hρ, c 0, ?_⟩
    have h2 := congrArg f hc
    rw [map_smul, map_sum, Fin.sum_univ_succ] at h2
    simpa [hg0, g] using h2
  obtain ⟨ρa, hρa, ca, hA⟩ := key a
  obtain ⟨ρr, hρr, cr, hR⟩ := key r
  have hse : (s:K)^e = (s:K) * (s:K)^(e-1) := by
    rw [← pow_succ']; congr 1; omega
  have hX : (r:K) • f (D k K T) + T • f (D k K (r:K)) = ((a:K) * (e:K) * (s:K)^(e-1)) • f (D k K (s:K)) + ((s:K) * (s:K)^(e-1)) • f (D k K (a:K)) := by
    have h1 := congrArg (fun z => f (D k K z)) hT
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_smul, map_nsmul] at h1
    rw [← hse, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul K]; exact h1
  have heB : (e : B) ∉ Q := by
    intro h
    have hu : IsUnit (e : B) := by
      have h3 : (e : B) = algebraMap k B (e : k) := by simp
      rw [h3]
      exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))).map _
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  refine ⟨ρa*ρr*(e:B)*a*r + s*(ρr*r*ca - ρa*a*cr), ρa*ρr*r^2, ?_, ?_, ?_⟩
  · intro h
    have h4 : ρa*ρr*(e:B)*a*r ∈ Q := by
      have := Q.sub_mem h (Q.mul_mem_right (ρr*r*ca - ρa*a*cr) hs)
      simpa using this
    rcases hQ.mem_or_mem h4 with h4 | h4
    · rcases hQ.mem_or_mem h4 with h4 | h4
      · rcases hQ.mem_or_mem h4 with h4 | h4
        · rcases hQ.mem_or_mem h4 with h4 | h4
          · exact hρa h4
          · exact hρr h4
        · exact heB h4
      · exact ha h4
    · exact hr h4
  · intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hρa h
      · exact hρr h
    · exact hr (hQ.mem_of_pow_mem _ h)
  · have hT' : (r:K) * T = (a:K) * ((s:K) * (s:K)^(e-1)) := by rw [hT, hse]
    rw [← hf, ← hf]
    push_cast
    linear_combination (norm := module) ((ρa:K)*ρr*r) • hX + ((ρr:K)*r*s*(s:K)^(e-1)) • hA - ((ρa:K)*r*T) • hR - ((ρa:K)*cr) • hT' • f (D k K (s:K))
